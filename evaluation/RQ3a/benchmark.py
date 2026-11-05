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
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
import chc_parity as common
from benchmark_flex import freeze
import corpus
from rq1_corpus import imports as lean_imports

HERE = Path(__file__).resolve().parent
CONFIGS = {'zap_fix': (True, True, False), 'se': (False, False, True),
           'flex': (True, True, True)}


def budgets(config, args):
    _, fix, se = CONFIGS[config]
    internal = args.combined_timeout if fix and se else args.flex_timeout
    watchdog = args.case_timeout if args.case_timeout is not None else internal + 120
    return internal, watchdog


def now():
    return datetime.now(timezone.utc).isoformat()


def save(path, data):
    common.write_json(path, data)


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


def classify_case(case, study, output, header, command, env):
    directory = output / 'classification' / study / common.hashlib.sha256(case['case'].encode()).hexdigest()[:16]
    directory.mkdir(parents=True, exist_ok=True)
    if (directory / 'record.json').exists():
        return json.loads((directory / 'record.json').read_text())
    if case['inventory_status'] != 'translated':
        row = {'case': case['case'], 'study': study, 'status': case['inventory_status']}
    else:
        source, error = common.case_source(case, header)
        path = directory / 'Case.lean'
        path.write_text(source)
        code, ms = invoke(path, directory, command, {**env, 'RQ3_MODE': 'classify',
            'FLEX_PARITY_OUTPUT': str(directory)}, 120)
        row = {'case': case['case'], 'study': study, 'exit_code': code, 'wall_ms': ms,
               'status': 'classified' if code == 0 and (directory/'classification.json').exists() else 'classification_failed',
               'log': str(directory/'lean.log')}
        if row['status'] == 'classified':
            row.update(json.loads((directory/'classification.json').read_text()))
    save(directory / 'record.json', row)
    return row


def setup(args):
    output = args.output
    output.mkdir(parents=True, exist_ok=True)
    selection_path = output / 'selection.json'
    if selection_path.exists():
        return json.loads(selection_path.read_text())
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
    if (directory/'native.json').exists():
        result.update(json.loads((directory/'native.json').read_text()))
    else:
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
    if directory.exists():
        # Incomplete attempts are preserved rather than silently overwritten.
        backup = directory.with_name(directory.name + '.interrupted-' + str(time.time_ns()))
        directory.rename(backup)
    record = common.run_case(case, config, run_args, command, {**env,
        'FLEX_PARITY_ZAP': str(int(zap)), 'FLEX_PARITY_FULL': str(int(fix)),
        'FLEX_PARITY_SE': str(int(se)), 'FLEX_PARITY_SCRAPE': 'auto',
        'FLEX_PARITY_PROFILE_PA': '1', 'FLEX_PARITY_CASE_SECONDS': str(watchdog),
        'RQ3_DIAGNOSTIC': str(int(args.diagnostic)),
        'FLEX_PARITY_FLEX_SECONDS': str(internal),
        'FLEX_PARITY_SOLVER_SECONDS': str(args.solver_timeout)}, header)
    record.update(study=study, configuration=config)
    return record


def run_trials(schedule, args, command, env, header, records, meta):
    """Bound concurrency; only the coordinator writes shared results and progress."""
    import report
    done = {(r['study'], r['case'], r['configuration']) for r in records}
    jobs = iter(job for job in schedule if (job[0], job[1]['case'], job[2]) not in done)
    active = {}
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
                active.pop(future)
                result = future.result()
                records.append(result)
                with (args.output/'results.jsonl').open('a') as f:
                    f.write(json.dumps(result)+'\n'); f.flush(); os.fsync(f.fileno())
                ms = result.get('wall_ms')
                print(f'Done {len(records)}/{len(schedule)} {result["status"]} '
                      f'{"unmeasured" if ms is None else f"{ms:.0f} ms"}', flush=True)
            refill()
            if len(records)//25 != previous//25: report.tables(args.output)
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
    p.add_argument('--configs', nargs='+', choices=list(CONFIGS),
                   help='Lean configurations to run; native baselines are included only for default RQ3b runs')
    p.add_argument('--diagnostic', action='store_true', help='retain pipeline failure traces')
    p.add_argument('--skip-classification', action='store_true', help='skip graph classification for pipeline diagnosis')
    p.add_argument('--no-figures', action='store_true', help='write records and tables without generating figures')
    p.add_argument('--seed', type=int, default=20261104)
    p.add_argument('--workers', type=int, default=1, help='concurrent query processes (default: 1)')
    p.add_argument('--flex-timeout', type=int, default=180,
                   help='shared seconds for Zap + Fix or S/E only (default: 180)')
    p.add_argument('--combined-timeout', type=int, default=360,
                   help='shared seconds when Fix and S/E are both enabled (default: 360)')
    p.add_argument('--solver-timeout', type=int, default=180,
                   help='seconds per native solver call, capped by remaining Flex time (default: 180)')
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
        import report
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
    configs = args.configs or list(CONFIGS)
    if args.case_timeout is not None and any(args.case_timeout <= budgets(c, args)[0] for c in configs):
        p.error('--case-timeout must exceed the selected internal Flex budgets')
    for field in ('z3','eldarica'):
        executable = shutil.which(getattr(args,field))
        if executable is None:
            p.error(f'{field} executable unavailable')
        setattr(args,field,executable)
    selection = setup(args)
    settings = {k:str(v) if isinstance(v,Path) else v for k,v in vars(args).items()
                if k not in {'resume','progress','prepare_only'}}
    settings['configuration_budgets'] = {
        config: {'flex_timeout': internal, 'case_timeout': watchdog}
        for config in CONFIGS for internal, watchdog in [budgets(config, args)]}
    settings_path = args.output/'settings.json'
    if settings_path.exists() and json.loads(settings_path.read_text()) != settings:
        p.error('resume settings differ from the frozen run')
    save(settings_path,settings)
    command, env, header = build_setup(args,selection)
    meta_path = args.output/'metadata.json'
    meta = json.loads(meta_path.read_text()) if meta_path.exists() else {
        'started_at':now(), 'complete':False, 'flex_commit':common.capture(['git','rev-parse','HEAD']),
        'flex_diff':common.capture(['git','diff','--stat']), 'benchmarks_commit':selection['benchmarks_commit'],
        'platform':platform.platform(), 'lean':common.capture([command[0],'--version']),
        'spacer':common.binary_info(args.z3,['--version']), 'eldarica':common.binary_info(args.eldarica,['-h']),
        'workers': args.workers, 'logical_cpus': os.cpu_count(),
        'timing': f'{args.workers} concurrent query processes, one trial per configuration/query. '
                  'Builds and classification excluded; process startup included in wall_ms. '
                  'Concurrent workers or other machine activity can affect timings.',
        'classification_skipped':args.skip_classification,
        'proof_depth':'Lean approxDepth, not an exact DAG-depth measurement.',
        'recursion':'Configured limit recorded; peak recursion is not available and remains null.'}
    save(meta_path,meta)
    if args.prepare_only:
        print('Prepared and frozen:',args.output,flush=True)
        return
    # Classification is separate from timed trials and never changes selection.
    jobs=[] if args.skip_classification else [(c,s) for s,cs in selection['cases'].items() for c in cs]
    meta['phase']='classification'; save(meta_path,meta)
    with ThreadPoolExecutor(max_workers=min(2,args.workers)) as pool:
        futures=[pool.submit(classify_case,c,s,args.output,header,command,env) for c,s in jobs]
        rows=[]
        for i,f in enumerate(futures):
            rows.append(f.result()); save(args.output/'classification.json',rows)
            if (i+1)%10==0:print(f'Classified {i+1}/{len(jobs)}',flush=True)
    schedules={}
    for study,cases in selection['cases'].items():
        schedules[study]=[]
        order=list(cases); random.Random(args.seed).shuffle(order)
        for i,case in enumerate(order):
            configs=args.configs or (['zap_fix','se','flex'] if study=='a' else ['native_spacer','native_eldarica','se'])
            offset=i%len(configs)
            configs=configs[offset:]+configs[:offset]
            schedules[study].append([(study,case,cfg) for cfg in configs])
    # Seeded submission order; completions may differ with multiple workers.
    schedule=[]
    for i in range(max(map(len,schedules.values()))):
        for blocks in schedules.values():
            if i < len(blocks): schedule.extend(blocks[i])
    save(args.output/'schedule.json',[{'study':s,'case':c['case'],'configuration':cfg} for s,c,cfg in schedule])
    result_path=args.output/'results.jsonl'
    records=[json.loads(l) for l in result_path.read_text().splitlines()] if result_path.exists() else []
    meta.update(phase='trials',planned_runs=len(schedule));save(meta_path,meta)
    run_trials(schedule, args, command, env, header, records, meta)


if __name__=='__main__':
    main()
