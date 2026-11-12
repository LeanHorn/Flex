#!/usr/bin/env python3
"""Profile one automatic scraping escalation per input using the RQ3 harness."""
from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import fcntl
import json
import os
from pathlib import Path
import random
import shutil
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'evaluation/RQ3a'))
import benchmark as rq3
import report


def prepare(manifest, output):
    source = json.loads(manifest.read_text())
    cases = source['cases']
    if len({c['case'] for c in cases}) != len(cases):
        raise ValueError('duplicate case identifiers')
    for i, case in enumerate(cases):
        for field in ['source', 'generated']:
            path = Path(case[field])
            if rq3.common.digest(path) != case[field + '_sha256']:
                raise ValueError(f'changed {field}: {case["case"]}')
            dest = output / 'corpus' / field / f'{i:03d}{path.suffix}'
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(path, dest)
            case['original_' + field + '_path'] = str(path)
            case[field] = str(dest)
    rq3.save(output / 'manifest.json', source)
    selection = {'method': source['method'], 'cases': {'scraping': cases},
                 'benchmarks_commit': rq3.common.capture([
                     'git', '-C', str(ROOT.parent/'flex-benchmarks'), 'rev-parse', 'HEAD'])}
    rq3.save(output / 'selection.json', selection)
    return selection


def summaries(output):
    """Keep raw events as well as one row per attempted scraping level."""
    _, coverage = report.tables(output)
    rows, query_rows = [], []
    for record in report.read(output):
        terminal = next((e for e in reversed(record.get('events', []))
                         if e.get('stage') == 'result'), {})
        retained = {r['pa_stage']: r for r in terminal.get('retention', {}).get('retained_candidates', [])
                    if r.get('backend') == 'fix' and terminal.get('kernel_checked') is True}
        modes = [e.get('mode') for e in record.get('events', [])
                 if e.get('stage') == 'fix/pa' and e.get('status') == 'stage_start']
        query_rows.append({'case': record['case'], 'status': record['status'],
                           'levels_reached': ';'.join(modes),
                           'retained_levels': ';'.join(sorted({r['scrape_mode'] for r in retained.values()})),
                           'fix_reached': bool(modes),
                           'kernel_checked': terminal.get('kernel_checked', False),
                           'all_predicates_instantiated': terminal.get('all_predicates_instantiated'),
                           'fully_proved': terminal.get('fully_proved'),
                           'flex_ms': terminal.get('flex_ms')})
        active = None
        for event in record.get('events', []):
            if event.get('stage') != 'fix/pa':
                continue
            if event['status'] == 'stage_start':
                if active is not None:
                    rows.append(active)
                active = {'case': record['case'], 'mode': event.get('mode'),
                          'stage_id': event.get('pa_stage'), 'completed': False,
                          'retained': event.get('pa_stage') in retained,
                          'remaining_heads': retained.get(event.get('pa_stage'), {}).get('remaining_heads'),
                          'accepted': False, 'start_ms': event.get('mono_ms'),
                          'start_heartbeats_raw': event.get('heartbeats_raw'),
                          'rounds': 0, 'query_status': record['status'],
                          'kernel_checked': terminal.get('kernel_checked', False)}
            elif active is not None:
                if event['status'] == 'setup':
                    for key in ['scraped_templates', 'bank_templates', 'tagged_templates']:
                        active[key] = event.get(key)
                    counts = event.get('candidates', [])
                    active['initial_candidates'] = sum(c['count'] for c in counts)
                    active['candidates_by_predicate'] = json.dumps(counts)
                elif event['status'] == 'round_end':
                    active['rounds'] += 1
                elif event['status'] == 'converged':
                    active['surviving_candidates'] = event.get('candidates')
                elif event['status'] == 'stage_end':
                    active.update(completed=True, accepted=event['accepted'])
                    active['elapsed_ms'] = event['mono_ms'] - active['start_ms']
                    if active['start_heartbeats_raw'] is not None:
                        active['heartbeats'] = (event['heartbeats_raw'] - active['start_heartbeats_raw']) / 1000
                    rows.append(active)
                    active = None
        if active is not None:
            rows.append(active)
    report.write_csv(output/'scraping_stages.csv', rows,
                     ['case', 'stage_id', 'mode', 'completed', 'accepted'])
    report.write_csv(output/'escalation.csv', query_rows,
                     ['case', 'levels_reached', 'retained_levels', 'status'])
    rq3.save(output/'scraping_summary.json', {
        'completed_queries': coverage['completed_runs'],
        'stages': {mode: {
            'queries_reaching': len({r['case'] for r in rows if r['mode'] == mode}),
            'attempts': sum(r['mode'] == mode for r in rows),
            'accepted_attempts': sum(r['mode'] == mode and r['accepted'] for r in rows),
            'queries_retaining': len({r['case'] for r in rows if r['mode'] == mode and r['retained']}),
            'interrupted_attempts': sum(r['mode'] == mode and not r['completed'] for r in rows),
            'elapsed_ms': report.distribution([r.get('elapsed_ms') for r in rows if r['mode'] == mode])
        } for mode in ['bank', 'basic', 'standard', 'deep']},
        'interpretation': 'bank means no scraping. Accepted is synthesis acceptance; final retained '
                          'invariants and head elimination require checked terminal retention. '
                          'Unreached levels are untested, not failures.'})
    manifest = json.loads((output/'manifest.json').read_text())
    by_case = {r['case']: r for r in query_rows}
    def proved(case):
        result = by_case.get(case['case'], {})
        return result.get('kernel_checked') is True and result.get('fully_proved') is True
    full = [c for c in manifest['cases'] if proved(c)]
    fix_full = [c for c in full if by_case[c['case']]['retained_levels']]
    for filename, selected in [('fully_proved_manifest.json', full),
                               ('fix_proved_manifest.json', fix_full)]:
        rq3.save(output/filename, {
            'method': 'Screened with automatic escalating Zap + Fix; checked full proofs only. '
                      + ('Requires retained Fix synthesis.' if filename.startswith('fix_') else ''),
            'screening_manifest': str(output/'manifest.json'),
            'settings': str(output/'settings.json'),
            'complete': len(query_rows) == len(manifest['cases']),
            'total': len(selected), 'cases': selected})
    def corpus(case):
        if case['suite'] in {'rq1', 'imp'}:
            return case['suite']
        return 'chc-comp' if case.get('format') == 'smtlib_to_lean' else 'refinement'
    groups = sorted({corpus(c) for c in manifest['cases']})
    rq3.save(output/'selection_summary.json', {
        group: {'screening_total': sum(corpus(c) == group for c in manifest['cases']),
                'completed': sum(corpus(c) == group and c['case'] in by_case for c in manifest['cases']),
                'fully_proved': sum(corpus(c) == group for c in full),
                'fully_proved_with_fix_synthesis': sum(corpus(c) == group for c in fix_full)}
        for group in groups})


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--manifest', type=Path)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--workers', type=int, default=3)
    p.add_argument('--timeout', type=int, default=180)
    p.add_argument('--zap-timeout', type=int, default=0,
                   help='separate Zap stage cap; zero keeps the shared pipeline')
    p.add_argument('--fix-timeout', type=int, default=0,
                   help='separate Fix stage cap, including certification and discharge')
    p.add_argument('--progress', action='store_true')
    p.add_argument('--resume', action='store_true')
    args = p.parse_args()
    args.output = args.output.resolve()
    if args.progress:
        report.progress(args.output)
        summary = args.output/'scraping_summary.json'
        if summary.exists():
            for mode, values in json.loads(summary.read_text())['stages'].items():
                print(mode.title(), values['queries_reaching'],
                      'reached;', values['accepted_attempts'], 'accepted synthesis attempts')
        return
    if args.workers < 1 or args.timeout < 1 or min(args.zap_timeout, args.fix_timeout) < 0:
        p.error('workers and timeout must be positive')
    if args.zap_timeout and args.fix_timeout and args.timeout < args.zap_timeout + args.fix_timeout:
        p.error('shared timeout must allow both stage caps')
    args.output.mkdir(parents=True, exist_ok=True)
    lock = (args.output/'run.lock').open('a')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    settings = dict(workers=args.workers, flex_timeout=args.timeout,
                    combined_timeout=args.timeout, case_timeout=args.timeout+120,
                    heartbeats=4000000, proof_heartbeats=40000,
                    synth_heartbeats=200000, solver_timeout=90,
                    zap_timeout=args.zap_timeout, fix_timeout=args.fix_timeout,
                    scrape='auto', zap=True, external_solvers=False,
                    seed=20261112, timeout_policy='component_caps_v1'
                    if args.zap_timeout or args.fix_timeout else rq3.TIMEOUT_POLICY)
    if args.resume:
        if json.loads((args.output/'settings.json').read_text()) != settings:
            p.error('resume settings differ')
        selection = json.loads((args.output/'selection.json').read_text())
        for case in selection['cases']['scraping']:
            for field in ['source', 'generated']:
                if rq3.common.digest(Path(case[field])) != case[field+'_sha256']:
                    p.error('frozen input changed: '+case['case'])
    else:
        if (args.output/'selection.json').exists() or args.manifest is None:
            p.error('provide --manifest for a new run, or --resume')
        selection = prepare(args.manifest, args.output)
        rq3.save(args.output/'settings.json', settings)
    run_args = argparse.Namespace(**settings, output=args.output, study='scraping',
                                  diagnostic=True, skip_classification=False,
                                  no_figures=True, z3=shutil.which('z3') or 'z3', eldarica='eld')
    meta_path = args.output/'metadata.json'
    meta = json.loads(meta_path.read_text()) if meta_path.exists() else {
        'started_at': rq3.now(), 'complete': False, 'phase': 'build',
        'planned_runs': len(selection['cases']['scraping']),
        'flex_commit': rq3.common.capture(['git', 'rev-parse', 'HEAD']),
        'benchmarks_commit': selection['benchmarks_commit'],
        'timing': 'One trial per input; three workers by default. Builds, startup and '
                  'classification excluded from flex_ms; Imp VC preparation recorded separately.'}
    rq3.save(meta_path, meta)
    command, env, header = rq3.build_setup(run_args, selection)
    env['FLEX_PARITY_SYNTH_HEARTBEATS'] = str(settings['synth_heartbeats'])
    env['FLEX_PARITY_ZAP_SECONDS'] = str(settings['zap_timeout'])
    env['FLEX_PARITY_PA_SECONDS'] = str(settings['fix_timeout'])
    snapshot = args.output/'source/evaluation/Scraping'
    snapshot.mkdir(parents=True, exist_ok=True)
    for path in Path(__file__).parent.glob('*'):
        if path.suffix in {'.py', '.md'}:
            shutil.copy2(path, snapshot/path.name)
    cases = list(selection['cases']['scraping'])
    random.Random(settings['seed']).shuffle(cases)
    schedule = [('scraping', case, 'zap_fix') for case in cases]
    records = rq3.resume_records(args.output, schedule)
    done = {r['case'] for r in records}
    jobs = iter(c for c in cases if c['case'] not in done)
    active = {}
    meta.update(phase='trials', complete=False)
    rq3.save(meta_path, meta)
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        def refill():
            while len(active) < args.workers and not (args.output/'STOP').exists():
                case = next(jobs, None)
                if case is None:
                    break
                prep = case.get('preparation', '').replace('\\n', '; ').replace('\n', '; ')
                trial_env = dict(env)
                trial_env.pop('FLEX_PARITY_PREPARE', None)
                if prep:
                    trial_env['FLEX_PARITY_PREPARE'] = prep
                case_args = argparse.Namespace(**vars(run_args))
                case_args.skip_classification = case.get('classification_skip', False)
                future = pool.submit(rq3.trial, case, 'scraping', 'zap_fix', case_args,
                                     command, trial_env, header)
                active[future] = case['case']
                print('Start:', case['case'], flush=True)
            rq3.save(args.output/'active.json', {'jobs': list(active.values())})
        refill()
        while active:
            completed, _ = wait(active, timeout=1, return_when=FIRST_COMPLETED)
            for future in completed:
                case = active.pop(future)
                result = future.result()
                result['phase_events'] = report.phase_events(result, args.output)
                if result.get('artifacts'):
                    result['artifacts'] = str(Path(result['artifacts']).relative_to(args.output))
                with (args.output/'results.jsonl').open('a') as file:
                    file.write(json.dumps(result)+'\n')
                    file.flush()
                    os.fsync(file.fileno())
                records.append(result)
                print(f'{len(records)}/{len(cases)} {result["status"]}: {case}', flush=True)
            refill()
            if completed and (len(records) <= 3 or len(records) % 25 < len(completed)):
                summaries(args.output)
    meta.update(complete=len(records)==len(cases), phase='complete' if len(records)==len(cases) else 'stopped',
                finished_at=rq3.now())
    rq3.save(meta_path, meta)
    summaries(args.output)
    report.progress(args.output)


if __name__ == '__main__':
    main()
