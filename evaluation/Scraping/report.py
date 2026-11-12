#!/usr/bin/env python3
"""Scraping ablation CSVs and figures; never reruns Lean or a solver."""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import importlib.util
import itertools
import json
import math
import os
from pathlib import Path
import re
import statistics

_spec = importlib.util.spec_from_file_location(
    'scraping_rq3_report', Path(__file__).resolve().parents[1] / 'RQ3a/report.py')
rq3 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(rq3)

CONFIGS = ['bank', 'basic', 'standard', 'deep', 'auto']
LABELS = dict(zip(CONFIGS, ['Bank', 'Basic', 'Standard', 'Deep', 'Auto']))
COLORS = dict(zip(CONFIGS, ['#64748b', '#2b7bba', '#19816a', '#bd7150', '#7752a5']))
IDENTITY = ['study', 'case', 'configuration']


def maximum(values):
    values = [v for v in values if v is not None]
    return max(values) if values else None


def corpus(case):
    if case.get('corpus'):
        return case['corpus']
    if case.get('suite') in {'rq1', 'imp'}:
        return case['suite']
    return 'chc-comp' if case.get('format') == 'smtlib_to_lean' else 'refinement'


def input_measures(case):
    result = {'screening_structure': case.get('structure'),
              'screening_level': case.get('screening_level'),
              'screening_flex_ms': case.get('screening_flex_ms'),
              'selection_size_band': case.get('selection_size_band')}
    for field, label in [('source', 'source'), ('generated', 'generated_lean')]:
        path = Path(case[field]) if case.get(field) else None
        data = path.read_bytes() if path and path.is_file() else None
        lines = data.decode(errors='replace').splitlines() if data is not None else None
        result[label+'_bytes'] = len(data) if data is not None else None
        result[label+'_loc'] = len(lines) if lines is not None else None
        result[label+'_nonblank_lines'] = sum(bool(line.strip()) for line in lines) if lines is not None else None
    queries = case.get('queries', [])
    clause_counts = [q.get('clause_count') for q in queries]
    result['source_clause_count'] = sum(clause_counts) if clause_counts and all(n is not None for n in clause_counts) else None
    arities = [len(s['argument_sorts']) for q in queries for s in q.get('symbols', [])
               if s.get('role') == 'predicate' and 'argument_sorts' in s]
    result['source_max_predicate_arity'] = maximum(arities)
    return result


def artifact_dir(output, record):
    path = output / record.get('artifacts', '')
    if (path / 'lean.log').is_file():
        return path
    return output / 'runs' / record['study'] / 'cases' / record['configuration'] / \
        record['case'].removesuffix('.lean')


def failure_observations(text):
    """These are visible diagnostics, not counts of every attempted tactic failure."""
    patterns = {
        'heartbeat': re.compile(r'maximum number of (?:internal )?heartbeats|'
                               r'\(?deterministic\)? timeout|'
                               r'heartbeats.{0,60}(?:exceeded|exhausted)|'
                               r'(?:exceeded|exhausted).{0,60}heartbeats', re.I),
        'recursion': re.compile(r'maximum recursion depth|'
                               r'(?:exceeded|exhausted).{0,60}(?:recursion|maxRecDepth)', re.I)}
    result = {}
    for kind, pattern in patterns.items():
        messages = sorted({line.strip()[:400] for line in text.splitlines() if pattern.search(line)})
        result[kind+'_failure_observed'] = bool(messages)
        result[kind+'_distinct_messages_observed'] = len(messages)
        result[kind+'_messages_observed'] = json.dumps(messages)
    for kind in ['candidate', 'instance']:
        pattern = re.compile(r'\b'+kind+r' limit \(\d+\) reached', re.I)
        messages = sorted({line.strip()[:400] for line in text.splitlines() if pattern.search(line)})
        result[kind+'_limit_observed'] = bool(messages)
        result[kind+'_limit_distinct_messages_observed'] = len(messages)
        result[kind+'_limit_messages_observed'] = json.dumps(messages)
    for kind, fragment in [
        ('safety_rejection', 'synthesized predicates do not satisfy a safety clause'),
        ('safety_inconclusive', 'could not validate a safety clause for the synthesized predicates')]:
        messages = sorted({line.strip()[:400] for line in text.splitlines() if fragment in line})
        result[kind+'_observed'] = bool(messages)
        result[kind+'_distinct_messages_observed'] = len(messages)
        result[kind+'_messages_observed'] = json.dumps(messages)
    return result


def pa_rows(record):
    """Observer timings are exact to the emitted event; interrupted stages are censored."""
    identity = {k: record[k] for k in IDENTITY}
    terminal = next((e for e in reversed(record.get('events', []))
                     if e.get('stage') == 'result'), {})
    retained = {r.get('pa_stage'): r for r in
                terminal.get('retention', {}).get('retained_candidates', [])
                if r.get('backend') == 'fix' and terminal.get('kernel_checked')}
    stages, candidates, rounds = [], [], []
    active, current_round = None, None
    for event in record.get('events', []):
        if event.get('stage') != 'fix/pa':
            continue
        status = event.get('status')
        if status == 'stage_start':
            if active is not None:
                stages.append(active)
            active = {**identity, 'stage_id': event.get('pa_stage'),
                      'mode': event.get('mode'), 'completed': False,
                      'accepted': None, 'retained': event.get('pa_stage') in retained,
                      'remaining_heads': retained.get(event.get('pa_stage'), {}).get('remaining_heads'),
                      'start_ms': event.get('mono_ms'), 'rounds_completed': 0,
                      'elapsed_ms': None, 'heartbeats': None,
                      'last_observed_elapsed_ms': 0,
                      'last_observed_heartbeats': 0, 'initial_candidates': None,
                      'surviving_candidates': None, 'query_status': record['status']}
            current_round = None
        if active is None:
            continue
        elapsed = event.get('stage_elapsed_ms')
        hb = event.get('stage_heartbeats_raw')
        if elapsed is not None:
            active['last_observed_elapsed_ms'] = elapsed
        if hb is not None:
            active['last_observed_heartbeats'] = hb / 1000
        key = {**identity, 'stage_id': active['stage_id'], 'mode': active['mode']}
        if status == 'setup':
            active.update({k: event.get(k) for k in
                           ['scraped_templates', 'bank_templates', 'tagged_templates']})
            counts = event.get('candidates', [])
            active['initial_candidates'] = sum(c['count'] for c in counts)
            active['predicates'] = len(counts)
            active['predicate_names'] = json.dumps([c['name'] for c in counts])
            active['max_candidates_per_predicate'] = maximum(c['count'] for c in counts)
            candidates.extend({**key, 'predicate': c['name'], 'initial_candidates': c['count']}
                              for c in counts)
        elif status == 'round_start':
            current_round = {**key, 'round': active['rounds_completed'] + 1,
                             'before': event.get('candidates'), 'after': None,
                             'completed': False, 'elapsed_ms': None, 'heartbeats': None,
                             'start_ms': event.get('mono_ms'),
                             'start_heartbeats_raw': event.get('heartbeats_raw')}
            rounds.append(current_round)
        elif status == 'round_end':
            active['rounds_completed'] += 1
            if current_round is not None:
                current_round.update(completed=True, before=event.get('before'), after=event.get('after'))
                if event.get('mono_ms') is not None and current_round['start_ms'] is not None:
                    current_round['elapsed_ms'] = event['mono_ms'] - current_round['start_ms']
                if event.get('heartbeats_raw') is not None and current_round['start_heartbeats_raw'] is not None:
                    delta = event['heartbeats_raw'] - current_round['start_heartbeats_raw']
                    current_round['heartbeats'] = delta / 1000 if delta >= 0 else None
                current_round = None
        elif status == 'converged':
            active['surviving_candidates'] = event.get('candidates')
        elif status == 'stage_end':
            active.update(completed=True, accepted=event.get('accepted'),
                          elapsed_ms=elapsed, heartbeats=hb / 1000 if hb is not None else None)
            stages.append(active)
            active = None
    if active is not None:
        stages.append(active)
    return stages, candidates, rounds


def log_rows(output, record, stages):
    """Phase starts follow PA stages in order. Trace call totals are observed, not exhaustive."""
    identity = {k: record[k] for k in IDENTITY}
    path = artifact_dir(output, record) / 'lean.log'
    text = path.read_text(errors='replace') if path.exists() else ''
    failures = failure_observations(text+'\n'+str(record.get('error', '')))
    if not path.exists():
        return [], [], [], [], failures, [], []
    phases, sources, scrapes, calls = [], [], [], []
    batches, oracle_events = {}, []
    next_stage, current, candidates_seen = 0, None, False
    starts = defaultdict(list)

    def allocate():
        nonlocal next_stage, current, candidates_seen
        current = stages[next_stage] if next_stage < len(stages) else None
        next_stage += 1
        candidates_seen = False

    def stage_key():
        return {**identity, 'stage_id': current['stage_id'] if current else None,
                'mode': current['mode'] if current else None}

    for line_number, line in enumerate(text.splitlines(), 1):
        match = re.search(r'FIX_ORACLE (\{.*\})', line)
        if match:
            try:
                event = json.loads(match.group(1))
            except json.JSONDecodeError:
                continue
            oracle_events.append({**stage_key(), 'line': line_number, **event})
            batch = batches.setdefault(event['batch_id'], {**stage_key(), 'batch_id': event['batch_id'],
                'backend': event['backend'], 'start_seen': False, 'end_seen': False,
                'completed': False, 'status': 'unfinished', 'queries': event.get('queries'),
                'elapsed_ns': None, 'elapsed_ms': None, 'heartbeats_raw': None,
                'valid': None, 'invalid': None, 'unknown': None,
                'measurement': event.get('measurement')})
            if event.get('event') == 'start':
                batch.update(start_seen=True, start_ms=event.get('mono_ms'))
            elif event.get('event') == 'end':
                batch.update({k:event.get(k) for k in ['completed','status','elapsed_ns','elapsed_ms',
                    'heartbeats_raw','valid','invalid','unknown']})
                batch.update(end_seen=True, end_ms=event.get('mono_ms'))
                counts = [batch[k] for k in ['valid','invalid','unknown']]
                batch['result_count_consistent'] = sum(counts) == batch['queries'] \
                    if all(x is not None for x in counts) else None
            continue
        match = re.search(r'FIX_PHASE_START (\w+)', line)
        if match:
            phase = match.group(1)
            if phase == 'partition':
                current, candidates_seen = None, False
            elif phase == 'scrape':
                allocate()
            elif phase == 'candidates':
                if current is None or candidates_seen:
                    allocate()
                candidates_seen = True
            item = {**stage_key(), 'phase': phase, 'line': line_number,
                    'ended': False, 'completed': None, 'ns': None, 'ms': None}
            starts[phase].append(item)
            phases.append(item)
            continue
        match = re.search(r'FIX_PHASE (\w+) ns=(\d+) completed=(true|false)', line)
        if match:
            phase, ns, completed = match.groups()
            if starts[phase]:
                item = starts[phase].pop()
                item.update(ended=True, completed=completed == 'true', ns=int(ns), ms=int(ns)/1e6)
            continue
        match = re.search(r'FIX_SCRAPE (\{.*\})', line)
        if match:
            try:
                stats = json.loads(match.group(1))
            except json.JSONDecodeError:
                continue
            scrapes.append({**stage_key(), 'line': line_number,
                           **{k: stats.get(k) for k in ['templates', 'anchored', 'nodes', 'definitions', 'rejected']},
                           'limits_hit': json.dumps(stats.get('limits_hit', []))})
            for kind, field in [('template', 'template_origins'), ('anchored', 'anchored_origins')]:
                sources.extend({**stage_key(), 'kind': kind, 'origin': origin, 'count': n}
                               for origin, n in Counter(stats.get(field, [])).items())
        match = re.search(r'\[flex\.synthesis\] (SMT|native fallback): (\d+) queries, '
                          r'(\d+) valid, (?:(\d+) invalid, )?(\d+)ms', line)
        if match:
            backend, queries, valid, invalid, ms = match.groups()
            queries, valid = int(queries), int(valid)
            invalid = int(invalid) if invalid is not None else None
            calls.append({**identity, 'line': line_number, 'backend': backend,
                          'queries': queries, 'valid': valid, 'invalid': invalid,
                          'unknown': queries-valid-invalid if invalid is not None else None,
                          'ms': int(ms), 'measurement': 'observed_trace_messages'})
    return phases, sources, scrapes, calls, failures, list(batches.values()), oracle_events


def timeout_reasons(record, phase_events):
    reasons = {e['phase'] for e in phase_events if e.get('status') == 'timeout'}
    if record['status'] in {'case_timeout', 'process_timeout'}:
        reasons.add('outer_watchdog')
    return ';'.join(sorted(reasons))


def stage_elapsed(phase_events, name):
    """Enclosing stage time includes preparation and discharge; open stages stay null."""
    pending, measured = [], []
    for event in phase_events:
        if event.get('phase') != name:
            continue
        if event.get('status') == 'start':
            pending.append(event)
        elif pending:
            pending.pop()
            measured.append(event.get('elapsed_ms'))
    return sum(measured) if measured and not pending and all(x is not None for x in measured) else None


def phase_heartbeats(phase_events, name):
    pending, measured = [], []
    for event in phase_events:
        if event.get('phase') != name:
            continue
        if event.get('status') == 'start':
            pending.append(event)
        elif pending:
            start = pending.pop().get('heartbeats_raw')
            end = event.get('heartbeats_raw')
            measured.append((end-start)/1000 if start is not None and end is not None and end >= start else None)
    return sum(measured) if measured and not pending and all(x is not None for x in measured) else None


def candidate_growth(rows, stages):
    """Fixed modes are not nested. Auto growth is measured only within a Bank-started scope."""
    bank = {r['case']: r for r in rows if r['configuration'] == 'bank'}
    grouped = defaultdict(list)
    for stage in stages:
        grouped[tuple(stage[k] for k in IDENTITY)].append(stage)
    transitions = []
    order = {'bank': 0, 'basic': 1, 'standard': 2, 'deep': 3}
    for row in rows:
        baseline = bank.get(row['case'], {}).get('max_stage_initial_candidates')
        size = row['max_stage_initial_candidates']
        row['bank_max_stage_initial_candidates'] = baseline
        row['max_pool_ratio_to_bank_arm'] = size/baseline if size is not None and baseline is not None and baseline > 0 else None
        row['max_pool_difference_from_bank_arm'] = size-baseline if size is not None and baseline is not None else None
        row['auto_observed_candidates_added'] = None
        if row['configuration'] != 'auto':
            continue
        observed_stages = grouped[tuple(row[k] for k in IDENTITY)]
        valid = bool(observed_stages) and all(s.get('initial_candidates') is not None for s in observed_stages)
        previous, origin, added = None, None, []
        for stage in observed_stages:
            if stage['mode'] == 'bank':
                previous = origin = stage
                continue
            comparable = previous is not None and origin is not None and \
                stage.get('predicate_names') == previous.get('predicate_names') and \
                stage.get('predicate_names') is not None and \
                order.get(stage['mode'], -1) > order.get(previous['mode'], -1)
            before = previous.get('initial_candidates') if previous else None
            after = stage.get('initial_candidates')
            delta = after-before if comparable and before is not None and after is not None else None
            monotone = delta is not None and delta >= 0
            transitions.append({**{k: row[k] for k in IDENTITY}, 'from_stage': previous['stage_id'] if previous else None,
                'to_stage': stage['stage_id'], 'from_mode': previous['mode'] if previous else None,
                'to_mode': stage['mode'], 'same_scope_observed': comparable,
                'before': before, 'after': after, 'monotone': monotone,
                'candidates_added': delta if monotone else None})
            valid = valid and monotone
            if monotone: added.append(delta)
            previous = stage
        row['auto_observed_candidates_added'] = sum(added) if origin is not None and valid else None
    return transitions


def write_statistics(output, rows):
    metrics = ['flex_ms', 'wall_ms', 'startup_ms', 'zap_ms', 'fix_ms',
               'stage_zap_ms', 'stage_fix_ms', 'discharge_ms',
               'tactic_heartbeats', 'proof_nodes', 'proof_depth', 'kernel_ns',
               'max_stage_initial_candidates', 'sum_stage_initial_candidates',
               'max_candidates_per_predicate', 'pa_elapsed_ms', 'pa_heartbeats',
               'pa_rounds', 'scrape_ms', 'candidate_build_ms', 'synthesis_ms',
               'safety_ms', 'certificate_ms', 'process_user_seconds',
               'process_system_seconds', 'process_max_rss_bytes', 'process_elapsed_seconds',
               'process_minor_faults', 'process_major_faults',
               'process_voluntary_context_switches', 'process_involuntary_context_switches',
               'stage_zap_heartbeats', 'stage_fix_heartbeats', 'discharge_heartbeats',
               'preprocess_heartbeats', 'source_bytes', 'generated_lean_bytes', 'generated_lean_loc',
               'original_predicates', 'remaining_predicates', 'instantiated_count',
               'fix_predicates_inferred_from_retained_setup', 'non_fix_predicate_reduction',
               'max_pool_ratio_to_bank_arm', 'max_pool_difference_from_bank_arm',
               'auto_observed_candidates_added', 'input_expr_depth', 'input_expr_dag_nodes',
               'input_expr_constants', 'proof_package_depth', 'proof_package_nodes',
               'proof_package_constants', 'proof_auxiliary_declarations']
    metrics += [f'{backend}_logical_{metric}' for backend in ['smt','native'] for metric in
                ['batches_started','batches_completed','queries_started','queries_completed',
                 'queries_unfinished','valid_completed','invalid_completed','unknown_completed',
                 'elapsed_ms','heartbeats']]
    statistics_rows, pairs = [], []
    configs = [c for c in CONFIGS if any(r['configuration'] == c for r in rows)]
    for cfg in configs:
        for group in ['ALL'] + sorted({r['corpus'] for r in rows}):
            selected = [r for r in rows if r['configuration'] == cfg and
                        (group == 'ALL' or r['corpus'] == group)]
            for population in ['all_measured', 'proved', 'not_proved', 'all_inferred', 'heads_eliminated']:
                subset = [r for r in selected if population == 'all_measured' or
                          (population == 'proved' and r['fully_proved']) or
                          (population == 'not_proved' and not r['fully_proved']) or
                          (population == 'all_inferred' and r['all_predicates_instantiated']) or
                          (population == 'heads_eliminated' and r['all_heads_eliminated'])]
                for metric in metrics:
                    statistics_rows.append({'configuration': cfg, 'corpus': group,
                        'population': population, 'metric': metric, 'queries': len(subset),
                        'missing': sum(r.get(metric) is None for r in subset),
                        **rq3.distribution([r.get(metric) for r in subset])})
    for first, second in itertools.combinations(configs, 2):
        a = {r['case']: r for r in rows if r['configuration'] == first}
        b = {r['case']: r for r in rows if r['configuration'] == second}
        shared = a.keys() & b.keys()
        for population, field in [('all_completed', None), ('jointly_inferred', 'all_predicates_instantiated'),
                                   ('jointly_proved', 'fully_proved')]:
            joint = [c for c in shared if field is None or (a[c][field] and b[c][field])]
            for metric in ['flex_ms', 'stage_fix_ms', 'fix_ms', 'tactic_heartbeats', 'kernel_ns']:
              measured = [(a[c][metric],b[c][metric]) for c in joint
                          if a[c].get(metric) is not None and b[c].get(metric) is not None]
              ratios = [x/y for x,y in measured if x > 0 and y > 0]
              pairs.append({'first': first, 'second': second, 'metric': metric, 'population': population,
                  'completed_pairs': len(shared),
                  'both_proved': sum(a[c]['fully_proved'] and b[c]['fully_proved'] for c in shared),
                  'population_pairs': len(joint), 'measured_pairs': len(measured),
                  **{'first_'+k:v for k,v in rq3.distribution([x for x,y in measured]).items()},
                  **{'second_'+k:v for k,v in rq3.distribution([y for x,y in measured]).items()},
                            'first_only_proved': sum(a[c]['fully_proved'] and not b[c]['fully_proved'] for c in shared),
                            'second_only_proved': sum(b[c]['fully_proved'] and not a[c]['fully_proved'] for c in shared),
                            'ratio_pairs': len(ratios),
                            'geomean_first_over_second': math.exp(statistics.mean(map(math.log, ratios))) if ratios else None,
                            'median_first_over_second': statistics.median(ratios) if ratios else None})
    rq3.write_csv(output/'ablation_statistics.csv', statistics_rows,
                  ['configuration', 'corpus', 'population', 'metric', 'queries', 'n'])
    rq3.write_csv(output/'ablation_comparisons.csv', pairs, ['first', 'second', 'metric'])


def summarize(output, figures=False):
    output = Path(output)
    rows, summary = rq3.tables(output)
    records = rq3.read(output)
    selection = json.loads((output/'selection.json').read_text())
    case_map = {c['case']: c for cases in selection['cases'].values() for c in cases}
    inputs = {name: input_measures(case) for name,case in case_map.items()}
    by_key = {(r['study'], r['case'], r['configuration']): r for r in rows}
    stages, candidates, rounds, phases, sources, scrapes, calls = [], [], [], [], [], [], []
    oracle_batches, oracle_events = [], []
    for record in records:
        stage, candidate, round_ = pa_rows(record)
        phase, source, scrape, call, failures, batches, raw_oracle = log_rows(output, record, stage)
        stages += stage; candidates += candidate; rounds += round_
        phases += phase; sources += source; scrapes += scrape; calls += call
        oracle_batches += batches; oracle_events += raw_oracle
        row = by_key[tuple(record[k] for k in IDENTITY)]
        row.update(failures)
        row.update(inputs[record['case']])
        input_path = artifact_dir(output, record)/'input_metrics.json'
        input_stats = json.loads(input_path.read_text()) if input_path.exists() else {}
        for key in ['expr_depth','expr_dag_nodes','expr_constants','scope']:
            row['input_'+key] = input_stats.get(key)
        row['corpus'] = corpus(case_map[record['case']])
        for metric in ['process_user_seconds', 'process_system_seconds', 'process_max_rss_bytes',
                       'process_elapsed_seconds', 'process_minor_faults', 'process_major_faults',
                       'process_voluntary_context_switches', 'process_involuntary_context_switches',
                       'resource_scope', 'resource_tool']:
            row[metric] = record.get(metric)
        row['pa_stages_started'] = len(stage)
        row['pa_stages_unfinished'] = sum(not s['completed'] for s in stage)
        row['pa_stages_accepted'] = sum(s['accepted'] is True for s in stage)
        row['fix_retained'] = any(s['retained'] for s in stage)
        row['retained_levels'] = ';'.join(s['mode'] for s in stage if s['retained'])
        terminal = next((e for e in reversed(record.get('events', [])) if e.get('stage') == 'result'), {})
        proof_stats = terminal.get('proof_metrics', {})
        for key in ['proof_package_depth','proof_package_nodes','proof_package_constants',
                    'proof_auxiliary_declarations','proof_metrics_version','kernel_scope']:
            row[key] = proof_stats.get(key)
        retention = terminal.get('retention', {}).get('retained_candidates', []) if row['kernel_checked'] else []
        retained_fix = {r.get('pa_stage') for r in retention if r.get('backend') == 'fix'}
        row['fix_retained'] = bool(retained_fix)
        witnessed = [s for s in stage if s['stage_id'] in retained_fix]
        counts_known = row['kernel_checked'] and len(witnessed) == len(retained_fix) and \
            all(s.get('predicates') is not None for s in witnessed)
        inferred = sum(s['predicates'] for s in witnessed) if counts_known else None
        reduction = row.get('instantiated_count')
        consistent = inferred is not None and reduction is not None and inferred <= reduction
        row['fix_retained_scopes'] = len(retained_fix) if row['kernel_checked'] else None
        row['fix_predicates_inferred_from_retained_setup'] = inferred if consistent else None
        row['non_fix_predicate_reduction'] = reduction-inferred if consistent else None
        row['inference_attribution_consistent'] = consistent
        row['retained_backends'] = ';'.join(sorted({r['backend'] for r in retention}))
        for backend in ['fix', 'zap']:
            remaining = [r.get('remaining_heads') for r in retention if r.get('backend') == backend]
            row[backend+'_remaining_head_obligations'] = sum(remaining) \
                if row['kernel_checked'] and all(n is not None for n in remaining) else None
        row['max_stage_initial_candidates'] = maximum(s['initial_candidates'] for s in stage)
        row['sum_stage_initial_candidates'] = sum(s['initial_candidates'] for s in stage) \
            if stage and all(s['initial_candidates'] is not None for s in stage) else None
        row['max_candidates_per_predicate'] = maximum(c['initial_candidates'] for c in candidate)
        row['max_stage_surviving_candidates'] = maximum(s['surviving_candidates'] for s in stage)
        row['pa_rounds'] = sum(s['rounds_completed'] for s in stage) if stage else None
        complete = bool(stage) and all(s['completed'] for s in stage)
        row['pa_elapsed_ms'] = sum(s['elapsed_ms'] for s in stage) \
            if complete and all(s['elapsed_ms'] is not None for s in stage) else None
        row['pa_heartbeats'] = sum(s['heartbeats'] for s in stage) if complete and all(s['heartbeats'] is not None for s in stage) else None
        row['pa_observed_elapsed_ms'] = sum(s['last_observed_elapsed_ms'] for s in stage) if stage else None
        raw_phases = rq3.phase_events(record, output)
        row['timeout_phases'] = timeout_reasons(record, raw_phases)
        row['stage_zap_ms'] = stage_elapsed(raw_phases, 'stage/zap')
        row['stage_fix_ms'] = stage_elapsed(raw_phases, 'stage/fix')
        for label,name in [('stage_zap','stage/zap'),('stage_fix','stage/fix'),
                           ('discharge','discharge'),('preprocess','preprocess')]:
            row[label+'_heartbeats'] = phase_heartbeats(raw_phases, name)
        row['scrape_limits_hit'] = ';'.join(sorted({x for s in scrape for x in json.loads(s['limits_hit'])}))
        row['scrape_limits_hit_count'] = sum(bool(json.loads(s['limits_hit'])) for s in scrape)
        row['scrape_nodes_observed'] = sum(s['nodes'] or 0 for s in scrape)
        row['definitions_inspected_observed'] = sum(s['definitions'] or 0 for s in scrape)
        for label, name in [('scrape', 'scrape'), ('candidate_build', 'candidates'),
                            ('synthesis', 'synthesis'), ('safety', 'safety'), ('certificate', 'certificate')]:
            selected = [p for p in phase if p['phase'] == name]
            row[label+'_ms'] = sum(p['ms'] for p in selected) if selected and all(p['ended'] for p in selected) else None
            row[label+'_calls'] = len(selected)
            row[label+'_unfinished'] = sum(not p['ended'] for p in selected)
            row[label+'_failed_or_interrupted'] = sum(not p['ended'] or not p['completed'] for p in selected)
            row[label+'_ended_unsuccessfully'] = sum(p['ended'] and p['completed'] is False for p in selected)
        for backend, label in [('SMT', 'smt'), ('native fallback', 'native')]:
            observed = [c for c in call if c['backend'] == backend]
            row[label+'_queries_observed'] = sum(c['queries'] for c in observed)
            row[label+'_ms_observed'] = sum(c['ms'] for c in observed)
        row['oracle_batch_telemetry_present'] = bool(batches)
        for backend,label in [('SMT','smt'),('native','native')]:
            selected = [b for b in batches if b['backend'] == backend]
            completed = [b for b in selected if b['completed']]
            prefix = label+'_logical_'
            row[prefix+'batches_started'] = sum(b['start_seen'] for b in selected) if batches else None
            row[prefix+'batches_completed'] = len(completed) if batches else None
            row[prefix+'queries_started'] = sum(b['queries'] for b in selected if b['start_seen']) if batches else None
            row[prefix+'queries_completed'] = sum(b['queries'] for b in completed) if batches else None
            row[prefix+'queries_unfinished'] = sum(b['queries'] for b in selected if not b['completed']) if batches else None
            for outcome in ['valid','invalid','unknown']:
                values = [b[outcome] for b in completed]
                row[prefix+outcome+'_completed'] = sum(values) \
                    if batches and all(v is not None for v in values) else None
            durations = [b['elapsed_ms'] for b in selected]
            beats = [b['heartbeats_raw'] for b in selected]
            row[prefix+'elapsed_ms'] = sum(durations) \
                if batches and all(v is not None for v in durations) else None
            row[prefix+'heartbeats'] = sum(beats)/1000 \
                if batches and all(v is not None for v in beats) else None
    growth = candidate_growth(rows, stages)
    for name, data, fields in [
        ('ablation_results', rows, IDENTITY), ('scraping_stages', stages, IDENTITY+['stage_id','mode']),
        ('candidate_counts', candidates, IDENTITY+['stage_id','predicate']),
        ('candidate_rounds', rounds, IDENTITY+['stage_id','round']),
        ('candidate_growth', growth, IDENTITY+['from_stage','to_stage']),
        ('fix_phases', phases, IDENTITY+['stage_id','phase']),
        ('scrape_sources', sources, IDENTITY+['stage_id','kind','origin']),
        ('scrape_details', scrapes, IDENTITY+['stage_id']),
        ('oracle_calls', calls, IDENTITY+['line','backend']),
        ('oracle_batches', oracle_batches, IDENTITY+['batch_id','backend']),
        ('oracle_events', oracle_events, IDENTITY+['batch_id','event'])]:
        rq3.write_csv(output/(name+'.csv'), data, fields)
    write_statistics(output, rows)
    configs = [c for c in CONFIGS if any(r['configuration'] == c for r in rows)]
    coverage = []
    for cfg in configs:
        subset = [r for r in rows if r['configuration'] == cfg]
        coverage.append({'configuration': cfg, 'selected': len(case_map), 'completed': len(subset),
                         'pending': len(case_map)-len(subset),
                         **{field: sum(bool(r[field]) for r in subset) for field in
                            ['fully_proved','all_predicates_instantiated','all_heads_eliminated',
                             'fix_retained','internal_timeout','external_timeout',
                             'heartbeat_failure_observed','recursion_failure_observed',
                             'candidate_limit_observed','instance_limit_observed',
                             'safety_rejection_observed','safety_inconclusive_observed']},
                         'outcomes': dict(Counter(r['category'] for r in subset))})
    summary['scraping'] = {'coverage': coverage,
        'interpretation': 'Conditioned on earlier escalating-run full successes; this ablation does not estimate corpus coverage.',
        'censoring': 'Interrupted PA elapsed times are null; last-observed elapsed times are lower bounds. Timeout flags overlap coverage.',
        'phase_failures': 'FIX_PHASE completed=false means the action threw, including ordinary safety rejection; it does not establish a timeout. Unfinished means no phase-end record. Only explicit phase timeout events and the outer watchdog establish timeout flags.',
        'stage_times': 'stage_zap_ms and stage_fix_ms measure the enclosing 60/120-second allocations, including their preparation and discharge. zap_ms and fix_ms measure the inner tactics only.',
        'resource_diagnostics': 'Heartbeat and recursion flags count visible diagnostic messages in lean.log and record.error, independently of wall-clock timeouts. Rolled-back or unlogged diagnostics are not observable; distinct-message counts are not attempted-failure counts.',
        'safety_diagnostics': 'Observed rejection means a candidate assignment failed a safety check; inconclusive means validation could not establish it. These are attempt diagnostics and can coexist with a later successful attempt.',
        'oracle_counts': 'Observed Lean trace messages only; rolled-back traces may be absent.',
        'oracle_batches': 'FIX_ORACLE direct-IO batches survive tactic rollback. Logical queries count supplied decision obligations per batch, not unique formulas or physical solver check-sat commands. Native batches retry original SMT-unknown obligations; do not add backend query totals as unique obligations. completed means an array of decisions returned, possibly including unknowns. Start-only durations remain null.',
        'candidate_counts': 'Counts are qualifier instances, not just templates. Auto pools are cumulative; sum_stage counts repeated candidates.',
        'candidate_growth': 'Bank-arm ratios compare observed maximum stage pools, not nested sets. Auto additions require increasing levels and matching predicate names within a Bank-started scope; only nonnegative measured additions are included.',
        'input_sizes': 'Source bytes/LOC describe the original input format; generated_lean bytes/LOC describe emitted Lean. LOC counts physical lines, including comments and blanks. Classification is measured before the tactic.',
        'input_expressions': 'input_expr_* measure the prepared goal at the recorded input_scope. Named model definitions remain opaque; file LOC is not structural CHC complexity.',
        'proof_metrics': 'proof_depth/nodes/constants measure the direct bridge. proof_package_* also cover generated helper declarations. kernel_scope and proof_metrics_version distinguish helper-inclusive v2 checking from earlier measurements.',
        'inference_counts': 'Fix predicate counts join kernel-retained stage IDs to their setup predicate arrays, keeping scopes separate. Non-Fix reduction includes Zap and preprocessing; it is not exact Zap attribution. Missing or inconsistent joins remain null.',
        'peak_recursion_depth': 'Not measured; recursion_limit and proof_depth are distinct metrics.'}
    (output/'ablation_summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    if figures:
        plot(output, rows, stages, phases, sources, selection)
    return rows, summary


def plot(output, rows, stages, phases, sources, selection):
    os.environ.setdefault('MPLCONFIGDIR', str(output/'matplotlib-cache'))
    os.environ.setdefault('XDG_CACHE_HOME', str(output/'matplotlib-cache'))
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.backends.backend_pdf import PdfPages
    from matplotlib.colors import ListedColormap, BoundaryNorm
    from matplotlib.patches import Patch
    import numpy as np
    if not rows:
        return
    settings = json.loads((output/'settings.json').read_text())
    selected = [c for cases in selection['cases'].values() for c in cases]
    total = len(selected)
    configs = [c for c in CONFIGS if any(r['configuration'] == c for r in rows)]
    destination = output/'figures'; destination.mkdir(exist_ok=True)
    plt.rcParams.update({'font.family':'DejaVu Sans', 'font.size':9,
                         'axes.spines.top':False, 'axes.spines.right':False,
                         'pdf.fonttype':42, 'ps.fonttype':42})
    complete = len(rows) == total * len(CONFIGS)
    caption = ('Complete' if complete else 'Provisional') + ' · '
    caption += f'{total} selected screening successes · Zap {settings.get("zap_timeout",60)} s + Fix {settings.get("fix_timeout",120)} s'
    caption += f' · {settings.get("workers",1)} workers · one trial per query/configuration'
    groups = {c:[r for r in rows if r['configuration']==c] for c in configs}
    cats = ['proved','heads_eliminated','instantiated','some_predicates','no_certified_progress','preparation_failed']
    cat_labels = ['Full proof','All heads eliminated','All predicates inferred','Some predicates inferred','No checked inference','Preparation failure']
    cat_colors = ['#247955','#79b998','#e1bd58','#6a9bc2','#d6dae0','#b76a81']

    def save(fig, pdf, name):
        fig.text(.5,.018,caption,ha='center',fontsize=7.5,color='#505050')
        fig.savefig(destination/(name+'.png'),dpi=180)
        fig.savefig(destination/(name+'.pdf'))
        pdf.savefig(fig)
        plt.close(fig)

    with PdfPages(output/('pilot.pdf' if total <= 50 else 'ablation.pdf')) as pdf:
        fig = plt.figure(figsize=(11.7,8.3))
        gs = fig.add_gridspec(2,2,height_ratios=[1.4,1],left=.09,right=.97,top=.88,bottom=.12,hspace=.45,wspace=.35)
        ax=fig.add_subplot(gs[0,0])
        for i,cfg in enumerate(configs):
            left=0
            for cat,label,color in zip(cats,cat_labels,cat_colors):
                n=sum(r['category']==cat for r in groups[cfg])
                ax.barh(i,n,left=left,color=color,label=label if i==0 else None)
                if n:ax.text(left+n/2,i,str(n),ha='center',va='center',fontsize=8)
                left+=n
            pending=total-len(groups[cfg])
            if pending:ax.barh(i,pending,left=left,color='white',edgecolor='#bbbbbb',hatch='///')
        ax.set_yticks(range(len(configs)),[LABELS[c] for c in configs]);ax.invert_yaxis()
        ax.set_xlim(0,total);ax.set_xlabel('CHCs (disjoint outcomes)');ax.set_title('Coverage')
        ax.legend(loc='upper left',bbox_to_anchor=(-.14,-.22),fontsize=7,ncol=2,frameon=False)
        ax=fig.add_subplot(gs[0,1])
        for cfg in configs:
            values=sorted(r['flex_ms']/1000 for r in groups[cfg] if r['fully_proved'] and r.get('flex_ms') is not None)
            if values:ax.step(values,range(1,len(values)+1),where='post',color=COLORS[cfg],label=LABELS[cfg])
        ax.set_xscale('log');ax.set_ylim(0,total+1);ax.set_xlabel('Measured tactic time (seconds)')
        ax.set_ylabel('Full proofs');ax.set_title('Proof completion');ax.grid(alpha=.2);ax.legend(frameon=False,fontsize=8)
        ax=fig.add_subplot(gs[1,:]);ax.axis('off')
        table=[]
        for cfg in configs:
            g=groups[cfg];times=[r['flex_ms']/1000 for r in g if r['fully_proved'] and r.get('flex_ms') is not None]
            pools=[r['max_stage_initial_candidates'] for r in g if r.get('max_stage_initial_candidates') is not None]
            table.append([LABELS[cfg],str(len(g)),str(sum(r['fully_proved'] for r in g)),str(sum(r['all_predicates_instantiated'] for r in g)),
                          str(sum(r['internal_timeout'] for r in g)),str(sum(r['external_timeout'] for r in g)),
                          f'{statistics.median(times):.2f}' if times else '—',f'{statistics.median(pools):,.0f}' if pools else '—'])
        t=ax.table(cellText=table,colLabels=['Configuration','Completed','Full proofs','All inferred','Internal\ntimeouts','Outer\ntimeouts','Median proof\ntime (s)','Median max\ncandidate pool'],loc='center',cellLoc='center')
        t.auto_set_font_size(False);t.set_fontsize(8);t.scale(1,1.8)
        for (i,j),cell in t.get_celld().items():
            cell.set_edgecolor('#dddddd')
            if i==0:cell.set_facecolor('#edf1f5');cell.set_text_props(weight='bold')
        fig.suptitle('Scraping ablation · coverage and time',fontsize=17,y=.97)
        fig.text(.5,.925,'All five configurations start from the original CHC. The selected suite is conditioned on screening success.',ha='center',fontsize=9)
        fig.text(.5,.075,'Timeout flags can coexist with retained progress. Proof-time medians include successful trials only; all-trial distributions are in CSV.',ha='center',fontsize=8)
        save(fig,pdf,'01-coverage-time')

        fig,axes=plt.subplots(2,2,figsize=(11.7,8.3))
        fig.subplots_adjust(left=.09,right=.97,top=.88,bottom=.12,hspace=.48,wspace=.33)
        ax=axes[0,0]
        x=list(range(len(configs)));lookup={(r['case'],r['configuration']):r for r in rows}
        for case in selected:
            vals=[lookup.get((case['case'],c),{}).get('max_stage_initial_candidates') for c in configs]
            ax.plot(x,[v+1 if v is not None else np.nan for v in vals],color='#c5ccd4',alpha=.5,linewidth=.6)
        for i,cfg in enumerate(configs):
            vals=[r['max_stage_initial_candidates']+1 for r in groups[cfg] if r.get('max_stage_initial_candidates') is not None]
            if vals:
                q=np.percentile(vals,[25,50,75]);ax.errorbar(i,q[1],yerr=[[q[1]-q[0]],[q[2]-q[1]]],fmt='o',capsize=5,color=COLORS[cfg],markersize=7)
        ax.set_yscale('log');ax.set_xticks(x,[LABELS[c] for c in configs]);ax.set_ylabel('Maximum stage candidate count + 1')
        ax.set_title('Candidate growth · median and quartiles');ax.grid(axis='y',alpha=.2)
        ax=axes[0,1]
        for cfg in configs:
            for proved,marker in [(True,'o'),(False,'x')]:
                g=[r for r in groups[cfg] if r['fully_proved']==proved and r.get('max_stage_initial_candidates') is not None and r.get('fix_ms') is not None]
                ax.scatter([r['max_stage_initial_candidates']+1 for r in g],[max(r['fix_ms']/1000,.001) for r in g],
                           color=COLORS[cfg],marker=marker,s=21,alpha=.65,label=LABELS[cfg] if proved else None)
        ax.set_xscale('log');ax.set_yscale('log');ax.set_xlabel('Maximum stage candidate count + 1');ax.set_ylabel('Fix phase time (seconds)')
        ax.set_title('Candidate size versus Fix cost');ax.legend(fontsize=7,frameon=False);ax.grid(alpha=.2)
        ax.text(.02,.02,'○ full proof    × unfinished proof\nMissing/censored Fix times omitted',transform=ax.transAxes,fontsize=7)
        ax=axes[1,0]
        names=[('scrape','Scraping'),('candidates','Candidates'),('synthesis','PA'),('safety','Validation'),('certificate','Certification')]
        phasecolors=['#98b6d2','#a8caa2','#6b91bb','#d6b272','#997cae']
        bottoms=[0.]*len(configs)
        for (phase,label),color in zip(names,phasecolors):
            vals=[]
            for cfg in configs:
                per=[]
                for r in groups[cfg]:
                    pp=[p for p in phases if p['case']==r['case'] and p['configuration']==cfg and p['phase']==phase]
                    if pp and all(p['ended'] for p in pp):per.append(sum(p['ms'] for p in pp)/1000)
                vals.append(statistics.mean(per) if per else 0.)
            ax.bar(x,vals,bottom=bottoms,color=color,label=label)
            bottoms=[a+b for a,b in zip(bottoms,vals)]
        ax.set_xticks(x,[LABELS[c] for c in configs]);ax.set_ylabel('Mean measured phase time (seconds)')
        ax.set_title('Where Fix spends time');ax.legend(fontsize=7,ncol=3,loc='upper left',
            facecolor='white',edgecolor='none',framealpha=.94)
        ax.text(.01,-.24,'Each phase uses its measured trials; phase means need not sum to mean total time.',transform=ax.transAxes,fontsize=7)
        ax=axes[1,1]
        top=[origin for origin,_ in Counter({origin:sum(s['count'] for s in sources if s['origin']==origin)
                                             for origin in {s['origin'] for s in sources}}).most_common(7)]
        sourcecolors=plt.cm.Set2(np.linspace(0,1,len(top)+1));bottoms=[0.]*len(configs)
        for origin,color in zip(top+['Other'],sourcecolors):
            vals=[sum(s['count'] for s in sources if s['configuration']==cfg and
                      (s['origin']==origin if origin!='Other' else s['origin'] not in top)) for cfg in configs]
            ax.bar(x,vals,bottom=bottoms,color=color,label=origin)
            bottoms=[a+b for a,b in zip(bottoms,vals)]
        ax.set_xticks(x,[LABELS[c] for c in configs]);ax.set_ylabel('Scraped template/source-instance occurrences')
        ax.set_title('Qualifier sources');ax.legend(fontsize=6,ncol=2,loc='upper left',
            facecolor='white',edgecolor='none',framealpha=.94)
        ax.text(.01,-.24,'Auto counts include repeated discoveries across levels; these are not unique candidates.',transform=ax.transAxes,fontsize=7)
        fig.suptitle('Scraping ablation · candidates and cost',fontsize=17,y=.97)
        save(fig,pdf,'02-candidates-cost')

        ordered=sorted(selected,key=lambda c:(corpus(c),c['case']))
        keys=['proved','heads_eliminated','instantiated','some_predicates','no_certified_progress','preparation_failed']
        for offset in range(0,len(ordered),50):
            page=ordered[offset:offset+50]
            values=np.full((len(page),len(configs)),-1.)
            for i,case in enumerate(page):
                for j,cfg in enumerate(configs):
                    r=lookup.get((case['case'],cfg))
                    if r:values[i,j]=keys.index(r['category'])
            fig,ax=plt.subplots(figsize=(11.7,max(8.3,.19*len(page)+1.8)))
            cmap=ListedColormap(['#ffffff']+cat_colors)
            ax.imshow(values,cmap=cmap,norm=BoundaryNorm(np.arange(-1.5,6,1),cmap.N),aspect='auto',interpolation='none')
            ax.set_xticks(range(len(configs)),[LABELS[c] for c in configs]);ax.xaxis.tick_top()
            labels=[f'{offset+i+1:03d}  {corpus(c)} / {Path(c["case"]).stem}' for i,c in enumerate(page)]
            ax.set_yticks(range(len(page)),labels,fontsize=6.5)
            for i,case in enumerate(page):
                for j,cfg in enumerate(configs):
                    r=lookup.get((case['case'],cfg))
                    if r and (r['internal_timeout'] or r['external_timeout']):ax.text(j,i,'T',ha='center',va='center',fontsize=7)
            ax.set_xticks(np.arange(-.5,len(configs),1),minor=True);ax.set_yticks(np.arange(-.5,len(page),1),minor=True)
            ax.grid(which='minor',color='white',linewidth=.6);ax.tick_params(which='minor',length=0)
            fig.suptitle(f'Scraping ablation · queries {offset+1}–{offset+len(page)}',fontsize=17,y=.98)
            fig.legend(handles=[Patch(color=c,label=l) for c,l in zip(cat_colors,cat_labels)],
                       loc='lower center',bbox_to_anchor=(.55,.035),ncol=3,frameon=False,fontsize=8)
            fig.text(.76,.075,'T: internal or outer timeout · white: pending',ha='center',fontsize=8)
            fig.subplots_adjust(left=.52,right=.97,top=.92,bottom=.12)
            save(fig,pdf,'03-query-outcomes'+(f'-{offset//50+1:02d}' if total>50 else ''))


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--figures',action='store_true',help='also write pilot.pdf (up to 50 queries) or ablation.pdf and figures/*.png/pdf')
    args=p.parse_args()
    _,summary=summarize(args.output.resolve(),figures=args.figures)
    print(json.dumps(summary['scraping']['coverage'],indent=2))


if __name__=='__main__':
    main()
