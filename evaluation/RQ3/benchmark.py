#!/usr/bin/env python3
"""Reproducible RQ3a/RQ3b pilots from a flex-benchmarks checkout."""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import json
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
    selection = corpus.build(args.benchmarks, output, args.count, args.seed)
    save(selection_path, selection)
    print('Selected', {s: len(cases) for s, cases in selection['cases'].items()}, flush=True)
    return selection


def build_setup(args, selection):
    output = args.output
    if (output / 'frozen-command.json').exists():
        return (json.loads((output/'frozen-command.json').read_text()),
                {**os.environ, **json.loads((output/'frozen-environment.json').read_text())},
                (output/'source/evaluation/RQ3/RQ3.lean').read_text())
    subprocess.run(['lake', '--log-level=error', 'build', 'Flex.Tactic.Tactics.Flex'], cwd=ROOT, check=True)
    header = (HERE/'RQ3.lean').read_text()
    imports = []
    for cases in selection['cases'].values():
        for case in cases:
            if case.get('generated'):
                imports += re.findall(r'^import (.*)$', Path(case['generated']).read_text(), re.M)
    header = common.with_imports(header, imports)
    modules = [m for m in re.findall(r'^import (.*)$', header, re.M)
               if m.split('.')[0] not in {'Init', 'Lean', 'Std'}]
    # Build imported helpers once; cases never invoke Lake during timing.
    subprocess.run(['lake', '--log-level=error', 'build', *modules], cwd=ROOT, check=True)
    subprocess.run(['lake', '--log-level=error', 'lean', str(HERE/'RQ3.lean'),
                    '--', '--error=hasSorry'], cwd=ROOT, check=True)
    command, env = common.lean_setup(output, True, header)
    command, env = freeze(output, command, env)
    frozen = output / 'source/evaluation/RQ3'
    frozen.mkdir(parents=True, exist_ok=True)
    for p in HERE.iterdir():
        if p.suffix in {'.py', '.lean', '.md'}:
            shutil.copy2(p, frozen/p.name)
    (frozen/'RQ3.lean').write_text(header)
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
                'status': 'preparation_failed', 'wall_ms': 0,
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
        'FLEX_PARITY_FLEX_SECONDS': str(internal),
        'FLEX_PARITY_SOLVER_SECONDS': str(args.solver_timeout)}, header)
    record.update(study=study, configuration=config)
    return record


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--benchmarks', type=Path, default=Path.cwd())
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--count', type=int, default=100, help='per study; zero selects the full corpus')
    p.add_argument('--seed', type=int, default=20261104)
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
    if args.output.exists() and any(args.output.iterdir()) and not args.resume:
        p.error('nonempty output; use --resume to continue the frozen run')
    if min(args.flex_timeout, args.combined_timeout, args.solver_timeout) <= 0:
        p.error('invalid budgets')
    if args.case_timeout is not None and args.case_timeout <= max(args.flex_timeout, args.combined_timeout):
        p.error('--case-timeout must exceed both internal Flex budgets')
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
        'timing':'Serial trials, one repetition; builds and source classification excluded; solver startup included.',
        'proof_depth':'Lean approxDepth, not an exact DAG-depth measurement.',
        'recursion':'Configured limit recorded; peak recursion is not available and remains null.'}
    save(meta_path,meta)
    if args.prepare_only:
        print('Prepared and frozen:',args.output,flush=True)
        return
    # Classification is separate from timed trials and never changes selection.
    jobs=[(c,s) for s,cs in selection['cases'].items() for c in cs]
    meta['phase']='classification'; save(meta_path,meta)
    with ThreadPoolExecutor(max_workers=2) as pool:
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
            configs=['zap_fix','se','flex'] if study=='a' else ['native_spacer','native_eldarica','se']
            configs=configs[i%3:]+configs[:i%3]
            schedules[study].append([(study,case,cfg) for cfg in configs])
    # Alternate studies while keeping all timings serial.
    schedule=[]
    for i in range(max(map(len,schedules.values()))):
        for blocks in schedules.values():
            if i < len(blocks): schedule.extend(blocks[i])
    save(args.output/'schedule.json',[{'study':s,'case':c['case'],'configuration':cfg} for s,c,cfg in schedule])
    result_path=args.output/'results.jsonl'
    records=[json.loads(l) for l in result_path.read_text().splitlines()] if result_path.exists() else []
    done={(r['study'],r['case'],r['configuration']) for r in records}
    meta.update(phase='trials',planned_runs=len(schedule));save(meta_path,meta)
    import report
    for study,case,config in schedule:
        if (study,case['case'],config) in done:continue
        if (args.output/'STOP').exists():break
        save(args.output/'active.json',{'study':study,'case':case['case'],'configuration':config,'started_at':now()})
        print(f'Start {len(records)+1}/{len(schedule)} {study}/{config}: {case["case"]}',flush=True)
        if config.startswith('native_'):
            result=native(case,config.removeprefix('native_'),args,command,env,header)
        else:
            result=trial(case,study,config,args,command,env,header)
        records.append(result)
        with result_path.open('a') as f:
            f.write(json.dumps(result)+'\n');f.flush();os.fsync(f.fileno())
        report.tables(args.output)
        print(f'Done {len(records)}/{len(schedule)} {result["status"]} {result.get("wall_ms",0):.0f} ms',flush=True)
        if len(records)%30==0:
            report.figures(args.output)
    meta.update(complete=len(records)==len(schedule),finished_at=now(),phase='complete' if len(records)==len(schedule) else 'stopped')
    save(meta_path,meta)
    (args.output/'active.json').unlink(missing_ok=True)
    report.figures(args.output)
    report.progress(args.output)


if __name__=='__main__':
    main()
