#!/usr/bin/env python3
"""RQ3a: refinement-typechecker coverage from a flex-benchmarks checkout."""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from datetime import datetime, timezone
import json
import fcntl
import os
from pathlib import Path
import platform
import random
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
import chc_parity as common
from benchmark_flex import freeze
import corpus
import report
from rq1_corpus import imports as lean_imports

HERE = Path(__file__).resolve().parent
CONFIGS = {'zap_fix': (True, True, False), 'se': (False, False, True),
           'flex': (True, True, True), 'se_zap_fix': (True, True, True)}
DEFAULTS = {'a': ['zap_fix', 'se', 'flex'],
            'b': ['native_spacer', 'native_eldarica', 'se', 'zap_fix', 'se_zap_fix']}
TIMEOUT_POLICY = 'reserved_blocks_v1'


def budgets(config, args):
    _, fix, se = CONFIGS[config]
    internal = args.combined_timeout if fix and se else args.flex_timeout
    watchdog = args.case_timeout if args.case_timeout is not None else internal + 120
    return internal, watchdog


def stage_budget(config, args):
    _, fix, se = CONFIGS[config]
    return args.flex_timeout if fix and se else 0


def now():
    return datetime.now(timezone.utc).isoformat()


def save(path, data):
    common.write_json(path, data)


def schedule_cases(selection, configs, seed):
    schedule = []
    for study, cases in selection['cases'].items():
        order = list(cases)
        random.Random(seed).shuffle(order)
        for i, case in enumerate(order):
            offset = i % len(configs)
            schedule.extend((study, case, c) for c in configs[offset:] + configs[:offset])
    return schedule


def resume_records(output, schedule):
    path = output / 'results.jsonl'
    if path.exists():
        data = path.read_bytes()
        if data and not data.endswith(b'\n'):
            end = data.rfind(b'\n') + 1
            path.with_name(f'results.interrupted-{time.time_ns()}.jsonl').write_bytes(data[end:])
            with path.open('r+b') as f:
                f.truncate(end)
    records = report.read(output)
    expected = {(s, c['case'], cfg) for s, c, cfg in schedule}
    keys = [(r['study'], r['case'], r['configuration']) for r in records]
    if len(keys) != len(set(keys)) or not set(keys) <= expected:
        raise ValueError('saved results contain duplicate or unscheduled trials')
    return records


def archive_attempt(directory):
    if directory.exists():
        directory.rename(directory.with_name(directory.name + '.interrupted-' + str(time.time_ns())))


def invoke(path, directory, command, environment, seconds):
    started = time.perf_counter()
    with (directory / 'lean.log').open('w') as log:
        proc = subprocess.Popen([*command, str(path)], cwd=ROOT, env=environment,
                                stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            code = proc.wait(timeout=seconds)
        except subprocess.TimeoutExpired:
            common.terminate_case(proc)
            code = 'process_timeout'
    return code, (time.perf_counter() - started) * 1000


def setup(args):
    output = args.output
    output.mkdir(parents=True, exist_ok=True)
    selection_path = output / 'selection.json'
    if selection_path.exists():
        selection = json.loads(selection_path.read_text())
        for study, cases in selection['cases'].items():
            for case in cases:
                for field in (('source', 'generated') if study == 'b' else ('generated',)):
                    expected = case.get(field + '_sha256')
                    if expected and common.digest(Path(case[field])) != expected:
                        raise ValueError(f'changed frozen {field}: {case["case"]}')
        return selection
    selection = corpus.build(args.benchmarks, output, args.count, args.seed, args.study)
    save(selection_path, selection)
    print('Selected', {s: len(cases) for s, cases in selection['cases'].items()}, flush=True)
    return selection


def build_setup(args, selection):
    output = args.output
    if (output / 'frozen-command.json').exists():
        header = output/'source/evaluation/RQ3a/RQ3.lean'
        if not header.exists():
            # Completed runs retain the original frozen source layout.
            header = output/'source/evaluation/RQ3/RQ3.lean'
        return (json.loads((output/'frozen-command.json').read_text()),
                {**os.environ, **json.loads((output/'frozen-environment.json').read_text())},
                header.read_text())
    subprocess.run(['lake', '--log-level=error', 'build', 'Flex.Tactic.Tactics.Flex'], cwd=ROOT, check=True)
    header = (HERE/'RQ3.lean').read_text()
    imports = []
    for cases in selection['cases'].values():
        for case in cases:
            if case.get('generated'):
                imports += lean_imports(Path(case['generated']).read_text())
    header = common.with_imports(header, imports)
    modules = [m for m in lean_imports(header)
               if m.split('.')[0] not in {'Init', 'Lean', 'Std'}]
    # Build imported helpers once; cases never invoke Lake during timing.
    subprocess.run(['lake', '--log-level=error', 'build', *modules], cwd=ROOT, check=True)
    subprocess.run(['lake', '--log-level=error', 'lean', str(HERE/'RQ3.lean'),
                    '--', '--error=hasSorry'], cwd=ROOT, check=True)
    command, env = common.lean_setup(output, True, header)
    command, env = freeze(output, command, env)
    frozen = output / 'source/evaluation/RQ3a'
    frozen.mkdir(parents=True, exist_ok=True)
    for p in HERE.iterdir():
        if p.suffix in {'.py', '.lean', '.md'}:
            shutil.copy2(p, frozen/p.name)
    (frozen/'RQ3.lean').write_text(header)
    if args.study == 'b':
        shutil.copytree(ROOT/'evaluation/RQ3b', output/'source/evaluation/RQ3b',
                        ignore=shutil.ignore_patterns('results', '__pycache__'))
    return command, env, header


def native(case, backend, args, command, env, header):
    directory = args.output/'native'/backend/case['case'].removesuffix('.lean')
    archive_attempt(directory)
    directory.mkdir(parents=True, exist_ok=True)
    file = directory/'Case.lean'
    file.write_text(header+'\nrun_elab FlexParity.native\n')
    executable = args.z3 if backend == 'spacer' else args.eldarica
    code, ms = invoke(file, directory, command, {**env,
        'FLEX_PARITY_OUTPUT': str(directory), 'FLEX_PARITY_INPUT': case['source'],
        'FLEX_PARITY_EXECUTABLE': executable, 'FLEX_PARITY_SOLVER_SECONDS': str(args.solver_timeout),
        'RQ3_NATIVE': backend}, args.solver_timeout + 30)
    result = {'study': 'b', 'case': case['case'], 'configuration': 'native_' + backend,
              'exit_code': code, 'wall_ms': ms, 'status': 'native_failed', 'artifacts': str(directory)}
    if code == 0 and (directory/'native.json').exists():
        result.update(json.loads((directory/'native.json').read_text()))
    else:
        if code == 'process_timeout': result['status'] = 'process_timeout'
        result['error'] = (directory/'lean.log').read_text()[-2000:]
    return result


def trial(case, study, config, args, command, env, header):
    if case['inventory_status'] != 'translated':
        return {'study': study, 'case': case['case'], 'configuration': config,
                'status': 'preparation_failed', 'wall_ms': None,
                'error': case.get('preparation_error', case.get('error', 'source preparation failed'))}
    zap, fix, se = CONFIGS[config]
    internal, watchdog = budgets(config, args)
    run_args = argparse.Namespace(**vars(args))
    run_args.output = args.output/'runs'/study
    run_args.mode, run_args.proof_timeout, run_args.smt_timeout = 'flex', 0, internal
    run_args.case_timeout = watchdog
    directory = run_args.output/'cases'/config/case['case'].removesuffix('.lean')
    archive_attempt(directory)
    record = common.run_case(case, config, run_args, command, {**env,
        'FLEX_PARITY_ZAP': str(int(zap)), 'FLEX_PARITY_FULL': str(int(fix)),
        'FLEX_PARITY_SE': str(int(se)), 'FLEX_PARITY_SCRAPE': 'auto',
        'RQ3_CHC_FIRST': str(int(config == 'se_zap_fix')),
        'RQ3_STAGE_SECONDS': str(stage_budget(config, args)),
        'FLEX_PARITY_PROFILE_PA': '1', 'FLEX_PARITY_CASE_SECONDS': str(watchdog),
        'RQ3_DIAGNOSTIC': str(int(args.diagnostic)),
        'FLEX_PARITY_FLEX_SECONDS': str(internal),
        'FLEX_PARITY_SOLVER_SECONDS': str(args.solver_timeout),
        'RQ3_CLASSIFY': '0' if args.skip_classification else '1'}, header)
    record.update(study=study, configuration=config)
    return record


def run_trials(schedule, args, command, env, header, records, meta):
    """Bound concurrency; only the coordinator writes shared results and progress."""
    done = {(r['study'], r['case'], r['configuration']) for r in records}
    jobs = iter(job for job in schedule if (job[0], job[1]['case'], job[2]) not in done)
    active = {}
    report_interval = max(25, len(schedule) // 20)
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        def refill():
            while len(active) < args.workers and not (args.output/'STOP').exists():
                job = next(jobs, None)
                if job is None: break
                study, case, config = job
                fn = native if config.startswith('native_') else trial
                params = (case, config.removeprefix('native_')) if fn is native else (case, study, config)
                future = pool.submit(fn, *params, args, command, env, header)
                active[future] = {'study': study, 'case': case['case'],
                                  'configuration': config, 'started_at': now()}
                print(f'Start {study}/{config}: {case["case"]}', flush=True)
            save(args.output/'active.json', {'jobs': list(active.values())})

        refill()
        while active:
            completed, _ = wait(active, timeout=1, return_when=FIRST_COMPLETED)
            if not completed: continue
            previous = len(records)
            for future in completed:
                job = active.pop(future)
                try:
                    result = future.result()
                except (OSError, subprocess.SubprocessError) as error:
                    result = {**job, 'status': 'runner_failed', 'error': str(error), 'wall_ms': None}
                result['phase_events'] = report.phase_events(result, args.output)
                if result.get('artifacts'):
                    result['artifacts'] = str(Path(result['artifacts']).relative_to(args.output))
                records.append(result)
                with (args.output/'results.jsonl').open('a') as f:
                    f.write(json.dumps(result)+'\n'); f.flush(); os.fsync(f.fileno())
                ms = result.get('wall_ms')
                print(f'Done {len(records)}/{len(schedule)} {result["status"]} '
                      f'{"unmeasured" if ms is None else f"{ms:.0f} ms"}', flush=True)
            refill()
            if len(records)//report_interval != previous//report_interval: report.tables(args.output)
    meta.update(complete=len(records)==len(schedule), finished_at=now(),
                phase='complete' if len(records)==len(schedule) else 'stopped')
    save(args.output/'metadata.json', meta)
    (args.output/'active.json').unlink(missing_ok=True)
    report.tables(args.output)
    if not args.no_figures: report.figures(args.output)
    report.progress(args.output)


def main(study='a'):
    description = (__doc__ if study == 'a' else
                   'RQ3b: CHC-COMP solver and Flex coverage from a flex-benchmarks checkout.')
    p = argparse.ArgumentParser(description=description)
    p.add_argument('--benchmarks', type=Path, default=Path.cwd())
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--count', type=int, default=100, help='query count; zero selects the full corpus')
    p.add_argument('--study', choices=[study], default=study, help=argparse.SUPPRESS)
    p.add_argument('--configs', nargs='+',
                   choices=list(CONFIGS) + (['native_spacer', 'native_eldarica'] if study == 'b' else []),
                   help='select explicit arms; RQ3b defaults to both native solvers plus se, zap_fix, se_zap_fix')
    p.add_argument('--diagnostic', action='store_true', help='retain pipeline failure traces')
    p.add_argument('--skip-classification', action='store_true', help='skip the in-trial graph classification for pipeline diagnosis')
    plotting = p.add_mutually_exclusive_group()
    plotting.add_argument('--no-figures', action='store_true', help='CSV/JSON only (default for RQ3b)')
    plotting.add_argument('--figures', dest='no_figures', action='store_false', help='also generate PDF plots')
    p.set_defaults(no_figures=study == 'b')
    p.add_argument('--seed', type=int, default=20261104)
    p.add_argument('--workers', type=int, default=1, help='concurrent query processes (default: 1)')
    p.add_argument('--flex-timeout', type=int, default=180,
                   help='shared seconds for Zap + Fix or S/E only (default: 180)')
    p.add_argument('--combined-timeout', type=int, default=360,
                   help='shared seconds when Fix and S/E are both enabled (default: 360)')
    p.add_argument('--solver-timeout', type=int, default=90,
                   help='seconds per native solver call, capped by remaining backend time (default: 90)')
    p.add_argument('--case-timeout', type=int,
                   help='outer process watchdog; defaults to the configuration budget plus 120 seconds')
    p.add_argument('--heartbeats', type=int, default=4000000)
    p.add_argument('--proof-heartbeats', type=int, default=40000)
    p.add_argument('--z3', default='z3')
    p.add_argument('--eldarica', default='eld')
    p.add_argument('--prepare-only', action='store_true')
    p.add_argument('--progress', action='store_true')
    p.add_argument('--resume', action='store_true')
    args = p.parse_args()
    args.output, args.benchmarks = args.output.resolve(), args.benchmarks.resolve()
    if args.progress:
        report.progress(args.output)
        return
    if args.workers < 1 or args.count < 0:
        p.error('--workers must be positive and --count nonnegative')
    if args.configs and len(set(args.configs)) != len(args.configs):
        p.error('--configs must not contain duplicates')
    args.output.mkdir(parents=True, exist_ok=True)
    lock = (args.output/'run.lock').open('a')
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        p.error('another runner already owns this output directory')
    if any(f.name != 'run.lock' for f in args.output.iterdir()) and not args.resume:
        p.error('nonempty output; use --resume to continue the frozen run')
    if min(args.flex_timeout, args.combined_timeout, args.solver_timeout) <= 0:
        p.error('invalid budgets')
    configs = args.configs or DEFAULTS[study]
    if any(c in {'flex','se_zap_fix'} for c in configs) and args.combined_timeout < 2 * args.flex_timeout:
        p.error('--combined-timeout must allow two --flex-timeout blocks')
    if args.case_timeout is not None and any(args.case_timeout <= budgets(c, args)[0]
                                            for c in configs if c in CONFIGS):
        p.error('--case-timeout must exceed the selected internal Flex budgets')
    if args.heartbeats < 0 or args.proof_heartbeats < 0:
        p.error('heartbeat limits must be nonnegative')
    for field in ('z3','eldarica'):
        executable = shutil.which(getattr(args,field))
        if executable is None:
            p.error(f'{field} executable unavailable')
        setattr(args,field,executable)
    selection = setup(args)
    settings = {k:str(v) if isinstance(v,Path) else v for k,v in vars(args).items()
                if k not in {'resume','progress','prepare_only'}}
    settings['configuration_budgets'] = {
        config: {'flex_timeout': internal, 'case_timeout': watchdog,
                 'stage_timeout': stage_budget(config, args)}
        for config in CONFIGS for internal, watchdog in [budgets(config, args)]}
    settings['timeout_policy'] = TIMEOUT_POLICY
    settings_path = args.output/'settings.json'
    if settings_path.exists() and json.loads(settings_path.read_text()) != settings:
        p.error('resume settings differ from the frozen run')
    save(settings_path,settings)
    # Do not mix coordinator implementations when resuming an interrupted run.
    scripts = [*HERE.glob('*.py'), *(ROOT/'evaluation/RQ3b').glob('*.py'), ROOT/'scripts/chc_parity.py',
               ROOT/'scripts/benchmark_flex.py', ROOT/'scripts/rq1_corpus.py',
               ROOT/'lean-toolchain', ROOT/'lake-manifest.json']
    hashes = {str(path.relative_to(ROOT)): common.digest(path) for path in scripts}
    hashes_path = args.output/'runner-hashes.json'
    if hashes_path.exists() and json.loads(hashes_path.read_text()) != hashes:
        p.error('runner or dependency pins changed; restore the recorded revision before resuming')
    save(hashes_path, hashes)
    command, env, header = build_setup(args,selection)
    meta_path = args.output/'metadata.json'
    meta = json.loads(meta_path.read_text()) if meta_path.exists() else {
        'started_at':now(), 'complete':False, 'flex_commit':common.capture(['git','rev-parse','HEAD']),
        'flex_diff':common.capture(['git','diff','--stat']), 'benchmarks_commit':selection['benchmarks_commit'],
        'platform':platform.platform(), 'python':sys.version, 'lean':common.capture([command[0],'--version']),
        'spacer':common.binary_info(args.z3,['--version']), 'eldarica':common.binary_info(args.eldarica,['-h']),
        'workers': args.workers, 'logical_cpus': os.cpu_count(),
        'timeout_policy': TIMEOUT_POLICY,
        'timing': f'{args.workers} concurrent query processes, one trial per configuration/query. '
                  'Builds excluded; classification runs in each trial process before the measured '
                  'tactic (excluded from flex_ms, included in wall_ms), as is process startup. '
                  'Concurrent workers or other machine activity can affect timings.',
        'classification_skipped':args.skip_classification,
        'proof_depth':'Lean approxDepth, not an exact DAG-depth measurement.',
        'proof_metrics_scope':'Final bridge expression and its kernel check; referenced auxiliary bodies are not expanded.',
        'recursion':'Configured limit recorded; peak recursion is not available and remains null.'}
    save(meta_path,meta)
    for key, executable in [('spacer', args.z3), ('eldarica', args.eldarica)]:
        if meta[key]['sha256'] != common.digest(Path(executable)):
            p.error(f'{key} executable changed since preparation')
    schedule = schedule_cases(selection, configs, args.seed)
    save(args.output/'schedule.json',[{'study':s,'case':c['case'],'configuration':cfg} for s,c,cfg in schedule])
    records = resume_records(args.output, schedule)
    meta['planned_runs'] = len(schedule)
    if args.prepare_only:
        meta['phase'] = 'prepared'
        save(meta_path, meta)
        print('Prepared and frozen:',args.output,flush=True)
        return
    if meta.get('complete') and len(records) == len(schedule):
        report.tables(args.output)
        if not args.no_figures: report.figures(args.output)
        report.progress(args.output)
        return
    # Classification runs inside each trial, before the measured tactic; it never
    # changes selection.
    meta.update(phase='trials', complete=False)
    meta.setdefault('trials_started_at', now())
    save(meta_path,meta)
    run_trials(schedule, args, command, env, header, records, meta)


if __name__=='__main__':
    main()
