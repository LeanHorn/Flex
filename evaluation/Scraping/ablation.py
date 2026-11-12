#!/usr/bin/env python3
"""Compare scraping configurations on screened Fix successes or a stratified pilot."""
from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'evaluation/RQ3a'))
import benchmark as rq3

CONFIGS = ('bank', 'basic', 'standard', 'deep', 'auto')
LEVELS = CONFIGS[:-1]
# Screening success level, deliberately balanced for diagnostic coverage.
QUOTAS = {'chc-comp': (8, 0, 8, 4), 'refinement': (6, 4, 1, 4),
          'rq1': (0, 4, 4, 0), 'imp': (0, 1, 0, 6)}


def load(path):
    return json.loads(path.read_text())


def read_records(path):
    return [json.loads(line) for line in path.read_text().splitlines(keepends=True)
            if line.endswith('\n') and line.strip()] if path.exists() else []


def fingerprint(text):
    return hashlib.sha256(text.encode()).hexdigest()


def terminal(record):
    return next((e for e in reversed(record.get('events', []))
                 if e.get('stage') == 'result'), {})


def screening_level(record):
    event = terminal(record)
    if not (event.get('kernel_checked') is True and event.get('fully_proved') is True):
        return None
    levels = {c.get('scrape_mode') for c in event.get('retention', {}).get('retained_candidates', [])
              if c.get('backend') == 'fix'}
    if not levels or not levels <= set(LEVELS):
        return None
    return max(levels, key=LEVELS.index)


def corpus(case):
    return case.get('corpus') or (case['suite'] if case['suite'] in {'rq1', 'imp'} else
                                 'chc-comp' if case.get('format') == 'smtlib_to_lean' else 'refinement')


def size(case):
    return case.get('bytes') or Path(case['generated']).stat().st_size


def select_cases(manifest, records, count, seed):
    """Balance families and three size bands within explicit corpus/level cells."""
    by_id = {r['case']: r for r in records}
    eligible = []
    for raw in manifest['cases']:
        level = screening_level(by_id.get(raw['case'], {}))
        if level:
            case = dict(raw)
            case.update(corpus=corpus(raw), screening_level=level,
                        screening_flex_ms=terminal(by_id[raw['case']]).get('flex_ms'))
            eligible.append(case)
    if count == 0:
        if not eligible:
            raise ValueError('screening has no eligible full Fix proofs')
        return eligible, {'eligible': len(eligible), 'requested': 'all',
                          'selected_cells': {g: dict(Counter(c['screening_level'] for c in eligible
                                                            if c['corpus'] == g)) for g in QUOTAS},
                          'selection': 'Every kernel-checked full screening success retaining Fix; '
                                       'no quotas, resampling or deduplication. Coverage is conditional '
                                       'on successful automatic scraping in the screening run.'}
    if len(eligible) < count:
        raise ValueError(f'only {len(eligible)} eligible full Fix proofs for {count} requested cases')
    cells = [(group, level, QUOTAS[group][i]) for group in QUOTAS
             for i, level in enumerate(LEVELS)]
    allocation = {(g, l): count * weight // 50 for g, l, weight in cells}
    remainder = count - sum(allocation.values())
    for g, l, _ in sorted(cells, key=lambda c: (-(count * c[2] % 50), c[0], c[1]))[:remainder]:
        allocation[g, l] += 1
    selected, seen = [], set()
    families = Counter()

    def choose(pool, amount):
        available = sorted((c for c in pool if c['case'] not in seen),
                           key=lambda c: (size(c), fingerprint(f'{seed}:{c["case"]}')))
        bands = {c['case']: min(2, 3 * i // max(1, len(available)))
                 for i, c in enumerate(available)}
        for i in range(min(amount, len(available))):
            chosen = min(available, key=lambda c: (
                abs(bands[c['case']] - i % 3),
                families[(c['corpus'], c.get('family', c.get('suite', '')))],
                fingerprint(f'{seed}:{c["case"]}')))
            chosen['selection_size_band'] = ('small', 'medium', 'large')[bands[chosen['case']]]
            selected.append(chosen)
            seen.add(chosen['case'])
            families[(chosen['corpus'], chosen.get('family', chosen.get('suite', '')))] += 1
            available.remove(chosen)

    for group in QUOTAS:
        target = sum(allocation[group, level] for level in LEVELS)
        before = len(selected)
        for level in LEVELS:
            choose([c for c in eligible if c['corpus'] == group and c['screening_level'] == level],
                   allocation[group, level])
        choose([c for c in eligible if c['corpus'] == group], target - (len(selected) - before))
    choose(eligible, count - len(selected))
    if len(selected) != count:
        raise ValueError('could not fill pilot selection')
    return selected, {'eligible': len(eligible), 'requested': count,
                      'requested_cells': {g: {l: allocation[g, l] for l in LEVELS} for g in QUOTAS},
                      'selected_cells': {g: dict(Counter(c['screening_level'] for c in selected
                                                        if c['corpus'] == g)) for g in QUOTAS},
                      'selection': 'Full kernel-checked proofs retaining Fix; corpus/retained-level '
                                   'quotas, family diversity and size bands. Deficits refill within '
                                   'corpus first, then globally. Not population-proportional sampling.'}


def wait_for_screening(after, output, meta):
    while True:
        if (output / 'STOP').exists():
            return False
        source_meta = load(after / 'metadata.json')
        manifest = load(after / 'manifest.json')
        records = read_records(after / 'results.jsonl')
        ids = [r['case'] for r in records]
        expected = {c['case'] for c in manifest['cases']}
        if len(ids) != len(set(ids)) or not set(ids) <= expected:
            raise ValueError('screening records contain duplicate or unknown case IDs')
        if source_meta.get('complete') is True:
            if set(ids) != expected:
                raise ValueError('screening marked complete but result records are missing')
            return True
        if source_meta.get('phase') in {'stopped', 'failed', 'error'} or (after / 'STOP').exists():
            raise RuntimeError('screening stopped before completion; pilot has not started')
        lock_path = after / 'run.lock'
        if lock_path.exists():
            with lock_path.open('a') as source_lock:
                try:
                    fcntl.flock(source_lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                except BlockingIOError:
                    pass
                else:
                    fcntl.flock(source_lock, fcntl.LOCK_UN)
                    raise RuntimeError('screening is incomplete and its runner is not active')
        meta.update(phase='waiting', screening_completed=len(records),
                    screening_total=len(expected), checked_at=rq3.now())
        rq3.save(output / 'metadata.json', meta)
        print(f'Waiting for screening: {len(records)}/{len(expected)}', flush=True)
        time.sleep(20)


def prepare_selection(args):
    source = load(args.after / 'manifest.json')
    records = read_records(args.after / 'results.jsonl')
    cases, details = select_cases(source, records, args.count, args.seed)
    by_case = {r['case']: r for r in records}
    for i, case in enumerate(cases):
        for field in ('source', 'generated'):
            path = Path(case[field])
            if rq3.common.digest(path) != case[field + '_sha256']:
                raise ValueError(f'changed screening {field}: {case["case"]}')
            target = args.output / 'corpus' / field / f'{i:03d}{path.suffix}'
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(path, target)
            case['screening_' + field] = str(path)
            case[field] = str(target)
    method = ('All completed automatic-scraping Fix successes; no resampling.' if args.count == 0 else
              'Stratified diagnostic pilot from completed automatic-scraping Fix successes.')
    selection = {'method': method, 'cases': {'scraping': cases},
                 'benchmarks_commit': load(args.after / 'metadata.json').get('benchmarks_commit')}
    rq3.save(args.output / 'manifest.json', {'method': method, 'cases': cases, 'complete': True})
    rq3.save(args.output / 'selection_details.json', details)
    rq3.save(args.output / 'screening_results.json', [by_case[c['case']] for c in cases])
    rq3.save(args.output / 'selection.json', selection)
    return selection


def measured_child(command):
    """Measure the Lean child without system utilities or sampling overhead."""
    started = time.monotonic()
    process = subprocess.Popen(command)
    _, status, usage = os.wait4(process.pid, 0)
    code = os.waitstatus_to_exitcode(status)
    process.returncode = code
    directory = Path(command[-1]).parent
    rq3.save(directory / 'resource.json', {
        'resource_tool': 'wait4',
        'process_elapsed_seconds': time.monotonic() - started,
        'process_user_seconds': usage.ru_utime,
        'process_system_seconds': usage.ru_stime,
        'process_max_rss_bytes': int(usage.ru_maxrss * (1 if platform.system() == 'Darwin' else 1024)),
        'process_minor_faults': usage.ru_minflt,
        'process_major_faults': usage.ru_majflt,
        'process_voluntary_context_switches': usage.ru_nvcsw,
        'process_involuntary_context_switches': usage.ru_nivcsw,
        'resource_scope': 'wait4 accounting for the Lean child, including imports and kernel checks; '
                          'RSS is not aggregate peak of Lean plus child solvers'})
    return code if code >= 0 else 128 - code


def resource_command(command):
    if not hasattr(os, 'wait4'):
        return command, None
    return [sys.executable, str(Path(__file__).resolve()), '--measure', *command], 'wait4'


def resource_usage(directory, kind):
    path = directory / 'resource.json'
    if kind and path.exists():
        return load(path)
    return dict(resource_tool=kind, process_elapsed_seconds=None,
                process_user_seconds=None, process_system_seconds=None,
                process_max_rss_bytes=None,
                resource_scope='Unavailable: child did not report accounting, or wait4 is unsupported')


def verify_dependencies(dependencies):
    for item in dependencies:
        if rq3.common.digest(Path(item['path'])) != item['sha256']:
            raise ValueError(f'changed frozen runtime dependency: {item["path"]}')


def verify_inputs(selection):
    for case in selection['cases']['scraping']:
        for field in ('source', 'generated'):
            if rq3.common.digest(Path(case[field])) != case[field + '_sha256']:
                raise ValueError(f'changed frozen {field}: {case["case"]}')


def host_snapshot():
    result = dict(platform=platform.platform(), machine=platform.machine(),
                  python=sys.version, logical_cpus=os.cpu_count(), physical_cpus=None,
                  memory_bytes=None, power=None, captured_at=rq3.now())
    if platform.system() == 'Darwin':
        for key, name in [('physical_cpus', 'hw.physicalcpu'), ('memory_bytes', 'hw.memsize')]:
            try:
                probe = subprocess.run(['/usr/sbin/sysctl', '-n', name], capture_output=True,
                                       text=True, timeout=3)
                if probe.returncode == 0: result[key] = int(probe.stdout.strip())
            except (OSError, ValueError, subprocess.TimeoutExpired):
                pass
        try:
            probe = subprocess.run(['/usr/bin/pmset', '-g', 'batt'], capture_output=True,
                                   text=True, timeout=3)
            if probe.returncode == 0: result['power'] = probe.stdout.strip()
        except (OSError, subprocess.TimeoutExpired):
            pass
    else:
        try:
            result['memory_bytes'] = os.sysconf('SC_PHYS_PAGES') * os.sysconf('SC_PAGE_SIZE')
        except (ValueError, OSError):
            pass
    return result


def verify_runtime(output, selection, boundary):
    verify_inputs(selection)
    runtime = load(output / 'runtime.json')
    verify_dependencies(runtime['dependencies'])
    path = output / 'runtime_checks.json'
    checks = load(path) if path.exists() else []
    checks.append(dict(boundary=boundary, verified_at=rq3.now(),
                       dependencies=len(runtime['dependencies']),
                       cases=len(selection['cases']['scraping']), host=host_snapshot()))
    rq3.save(path, checks)


def append_record(output, record):
    with (output / 'results.jsonl').open('a') as file:
        file.write(json.dumps(record) + '\n')
        file.flush()
        os.fsync(file.fileno())


def freeze_runtime(args):
    """Reference the completed screening snapshot; hash imports without duplicating them."""
    after, output = args.after, args.output
    runtime_root = output if args.fresh_runtime else after
    provenance = output / 'runtime.json'
    header_path = runtime_root / 'source/evaluation/RQ3a/RQ3.lean'
    command = load(runtime_root / 'frozen-command.json')
    frozen_env = load(runtime_root / 'frozen-environment.json')
    if provenance.exists():
        recorded = load(provenance)
        verify_dependencies(recorded['dependencies'])
    else:
        paths = {header_path, Path(command[0]), Path(__file__).resolve(),
                 ROOT / 'evaluation/RQ3a/benchmark.py', ROOT / 'evaluation/RQ3a/report.py',
                 ROOT / 'scripts/chc_parity.py', runtime_root / 'lean-setup.json',
                 runtime_root / 'frozen-command.json', runtime_root / 'frozen-environment.json',
                 runtime_root / 'compiled-hashes.json', after / 'settings.json',
                 output / 'settings.json', output / 'manifest.json', output / 'selection.json',
                 after / 'metadata.json', after / 'manifest.json', after / 'results.jsonl'}
        def collect(value):
            if isinstance(value, str) and Path(value).is_file():
                paths.add(Path(value))
            elif isinstance(value, list):
                for item in value: collect(item)
            elif isinstance(value, dict):
                for item in value.values(): collect(item)
        collect(load(runtime_root / 'lean-setup.json'))
        for executable in ('z3', 'cvc5'):
            resolved = shutil.which(executable, path=frozen_env.get('PATH'))
            if resolved: paths.add(Path(resolved).resolve())
        expected = load(runtime_root / 'compiled-hashes.json')
        for relative, digest in expected.items():
            artifact = runtime_root / 'compiled' / Path(relative).relative_to('.lake/build')
            if rq3.common.digest(artifact) != digest:
                raise ValueError(f'changed screened compiled artifact: {artifact}')
        dependencies = [{'path': str(path), 'sha256': rq3.common.digest(path),
                         'bytes': path.stat().st_size} for path in sorted(paths)]
        rq3.save(provenance, {'screening': str(after), 'runtime_root': str(runtime_root),
                             'fresh_runtime': args.fresh_runtime, 'command': command,
                             'dependencies': dependencies,
                             'python': sys.version, 'platform': platform.platform(),
                             'note': 'Compiled runtime root and screening provenance are recorded separately. '
                                     'Keep both directories and dependency packages intact. '
                                     'Hashes checked before trials, on resume and after trials.'})
        snapshot = output / 'source/evaluation/Scraping'
        snapshot.mkdir(parents=True, exist_ok=True)
        for path in HERE.iterdir():
            if path.suffix in {'.py', '.md'}:
                shutil.copy2(path, snapshot / path.name)
        helpers = output / 'source/evaluation/RQ3a'
        helpers.mkdir(parents=True, exist_ok=True)
        for path in (ROOT / 'evaluation/RQ3a').glob('*.py'):
            shutil.copy2(path, helpers / path.name)
        if header_path.resolve() != (helpers / 'RQ3.lean').resolve():
            shutil.copy2(header_path, helpers / 'RQ3.lean')
        scripts = output / 'source/scripts'
        scripts.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / 'scripts/chc_parity.py', scripts / 'chc_parity.py')
        rq3.save(output / 'frozen-command.json', command)
        rq3.save(output / 'frozen-environment.json', frozen_env)
        recorded = load(provenance)
        recorded['dependencies'].extend(
            {'path': str(path), 'sha256': rq3.common.digest(path), 'bytes': path.stat().st_size}
            for path in sorted((output / 'source').rglob('*')) if path.is_file())
        rq3.save(provenance, recorded)
    # Prevent ambient settings from contaminating a supposedly fixed configuration.
    env = {k: v for k, v in os.environ.items() if not k.startswith(('FLEX_PARITY_', 'RQ3_'))}
    env.update(frozen_env)
    env.update(FLEX_PARITY_SYNTH_HEARTBEATS='200000', FLEX_PARITY_ZAP_SECONDS='60',
               FLEX_PARITY_PA_SECONDS='120')
    wrapped, kind = resource_command(command)
    return wrapped, env, header_path.read_text(), kind


def summarize(output, figures=False):
    path = output / 'source/evaluation/Scraping/report.py'
    if not path.exists(): path = HERE / 'report.py'
    spec = importlib.util.spec_from_file_location('scr_report', path)
    module = importlib.util.module_from_spec(spec)
    sys.modules['scr_report'] = module
    spec.loader.exec_module(module)
    module.summarize(output, figures=figures)


def progress(output):
    meta = load(output / 'metadata.json')
    rows = read_records(output / 'results.jsonl')
    print(f'Phase: {meta["phase"]}; complete={meta.get("complete", False)}')
    if meta['phase'] == 'waiting':
        print(f'Screening: {meta.get("screening_completed", "?")}/{meta.get("screening_total", "?")}')
    print(f'{len(rows)}/{meta["planned_runs"]} trials')
    for mode in CONFIGS:
        selected = [r for r in rows if r['configuration'] == mode]
        print(mode, dict(Counter(r['status'] for r in selected)))
    active = output / 'active.json'
    if active.exists(): print('Active:', load(active))
    if meta.get('error'): print('Error:', meta['error'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--after', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--workers', type=int, default=2)
    parser.add_argument('--count', type=int, default=50, help='sample size; 0 selects every eligible Fix success')
    parser.add_argument('--seed', type=int, default=20261112)
    parser.add_argument('--fresh-runtime', action='store_true',
                        help='build and freeze current instrumented Flex; inputs still come from screening')
    parser.add_argument('--prepare-only', action='store_true',
                        help='freeze selection, runtime and schedule without starting trials')
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--progress', action='store_true')
    args = parser.parse_args()
    args.output = args.output.resolve()
    if args.progress:
        progress(args.output)
        return
    if args.after is None or args.count < 0 or args.workers < 1:
        parser.error('--after is required; count must be nonnegative and workers positive')
    args.after = args.after.resolve()
    args.output.mkdir(parents=True, exist_ok=True)
    lock = (args.output / 'run.lock').open('a')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    settings = dict(workers=args.workers, count=args.count, seed=args.seed,
                    screening=str(args.after), configurations=list(CONFIGS), repeats=1,
                    flex_timeout=180, combined_timeout=180, case_timeout=300,
                    zap_timeout=60, fix_timeout=120, heartbeats=4000000,
                    proof_heartbeats=40000, synth_heartbeats=200000, solver_timeout=90,
                    external_solvers=False, timeout_policy='component_caps_v1')
    if args.fresh_runtime:
        settings['fresh_runtime'] = True
    meta_path = args.output / 'metadata.json'
    if args.resume:
        if load(args.output / 'settings.json') != settings:
            parser.error('resume settings differ')
        meta = load(meta_path)
    else:
        if meta_path.exists(): parser.error('output already contains a run; use --resume')
        meta = dict(started_at=rq3.now(), complete=False, phase='waiting',
                    planned_runs=args.count * len(CONFIGS) if args.count else None,
                    timing=f'Fresh process per trial; imports and kernel checks measured separately; '
                           f'{args.workers} worker(s); no builds or statistical reports during measurements.')
        rq3.save(args.output / 'settings.json', settings)
        rq3.save(meta_path, meta)
    try:
        selection_path = args.output / 'selection.json'
        if not selection_path.exists():
            if not wait_for_screening(args.after, args.output, meta):
                meta.update(phase='stopped', complete=False)
                rq3.save(meta_path, meta)
                return
            meta.update(phase='prepare')
            rq3.save(meta_path, meta)
            selection = prepare_selection(args)
        else:
            selection = load(selection_path)
        verify_inputs(selection)
        meta.update(selected_cases=len(selection['cases']['scraping']),
                    planned_runs=len(selection['cases']['scraping']) * len(CONFIGS))
        rq3.save(meta_path, meta)
        if args.fresh_runtime and not (args.output / 'frozen-command.json').exists():
            meta.update(phase='build')
            rq3.save(meta_path, meta)
            rq3.build_setup(argparse.Namespace(output=args.output, study='scraping'), selection)
        command, env, header, resource_kind = freeze_runtime(args)
        verify_runtime(args.output, selection, 'before_trials')
        rq3.CONFIGS.update({mode: (True, True, False) for mode in CONFIGS})
        schedule = rq3.schedule_cases(selection, list(CONFIGS), args.seed)
        rq3.save(args.output / 'schedule.json', [dict(study=s, case=c['case'], configuration=cfg)
                                               for s, c, cfg in schedule])
        records = rq3.resume_records(args.output, schedule)
        if args.prepare_only:
            meta.update(phase='prepared', complete=False, prepared_at=rq3.now())
            rq3.save(meta_path, meta)
            progress(args.output)
            return
        done = {(r['study'], r['case'], r['configuration']) for r in records}
        jobs = iter(job for job in schedule if (job[0], job[1]['case'], job[2]) not in done)
        run_args = argparse.Namespace(**settings, output=args.output, study='scraping', diagnostic=True,
                                      skip_classification=False, no_figures=True,
                                      z3=shutil.which('z3') or 'z3', eldarica='eld')
        active = {}
        source_meta = load(args.after / 'metadata.json')
        meta.update(phase='trials', complete=False, trials_started_at=meta.get('trials_started_at', rq3.now()),
                    flex_commit=rq3.common.git_info(['rev-parse', 'HEAD'])
                        if args.fresh_runtime else source_meta.get('flex_commit'),
                    screening_flex_commit=source_meta.get('flex_commit'),
                    benchmarks_commit=source_meta.get('benchmarks_commit'), resource_tool=resource_kind)
        rq3.save(meta_path, meta)
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            def refill():
                while len(active) < args.workers and not (args.output / 'STOP').exists():
                    job = next(jobs, None)
                    if job is None: break
                    study, case, config = job
                    local_args = argparse.Namespace(**vars(run_args))
                    local_args.scrape = 'no' if config == 'bank' else config
                    local_args.skip_classification = case.get('classification_skip', False)
                    local_env = dict(env)
                    local_env.pop('FLEX_PARITY_PREPARE', None)
                    prep = case.get('preparation', '').replace('\\n', '; ').replace('\n', '; ')
                    if prep: local_env['FLEX_PARITY_PREPARE'] = prep
                    future = pool.submit(rq3.trial, case, study, config, local_args, command, local_env, header)
                    active[future] = dict(study=study, case=case['case'], configuration=config,
                                          started_at=rq3.now())
                    print(f'Start {config}: {case["case"]}', flush=True)
                rq3.save(args.output / 'active.json', {'jobs': list(active.values())})
            refill()
            while active:
                completed, _ = wait(active, timeout=1, return_when=FIRST_COMPLETED)
                for future in completed:
                    job = active.pop(future)
                    try:
                        record = future.result()
                    except Exception as exc:
                        failure = {**job, 'status': 'runner_failed', 'wall_ms': None, 'events': [],
                                   'error': f'{type(exc).__name__}: {exc}', 'failed_at': rq3.now()}
                        append_record(args.output, failure)
                        meta['failed_trial'] = job
                        raise
                    record['phase_events'] = rq3.report.phase_events(record, args.output)
                    if record.get('artifacts'):
                        directory = Path(record['artifacts'])
                        record.update(resource_usage(directory, resource_kind))
                        record['artifacts'] = str(directory.relative_to(args.output))
                        rq3.save(directory / 'result.json', record)
                    append_record(args.output, record)
                    records.append(record)
                    print(f'{len(records)}/{len(schedule)} {record["configuration"]} '
                          f'{record["status"]}: {record["case"]}', flush=True)
                refill()
        finished = len(records) == len(schedule)
        meta.update(complete=False, phase='reporting', trials_finished_at=rq3.now())
        rq3.save(meta_path, meta)
        verify_runtime(args.output, selection, 'after_trials')
        summarize(args.output, figures=True)
        meta.update(complete=finished, phase='complete' if finished else 'stopped', finished_at=rq3.now())
        rq3.save(meta_path, meta)
        progress(args.output)
    except Exception as exc:
        meta.update(phase='failed', complete=False, error=f'{type(exc).__name__}: {exc}', failed_at=rq3.now())
        rq3.save(meta_path, meta)
        raise


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == '--measure':
        raise SystemExit(measured_child(sys.argv[2:]))
    main()
