#!/usr/bin/env python3
"""Replay RQ3a with isolated persistent Lean workers, or compare against fresh processes."""
from __future__ import annotations
import argparse, collections, csv, importlib.util, json, os
from pathlib import Path
import queue, random, re, statistics, subprocess, threading, time
from types import SimpleNamespace


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def choose(cases, count, seed):
    groups = {}
    for case in cases:
        if case['inventory_status'] == 'translated':
            groups.setdefault(case['suite'], []).append(case)
    size = sum(map(len, groups.values()))
    if not 0 < count <= size: raise ValueError('count exceeds translated population')
    quotas = {s: count * len(g) // size for s, g in groups.items()}
    for s in sorted(groups, key=lambda s: (-(count * len(groups[s]) / size - quotas[s]), s))[:count-sum(quotas.values())]:
        quotas[s] += 1
    selected = []
    for s, g in sorted(groups.items()):
        g = sorted(g, key=lambda c: c['case'])
        random.Random(seed).shuffle(g)
        selected.extend(g[:quotas[s]])
    random.Random(seed).shuffle(selected)
    return selected, size, quotas


def worker_source(header, implementation):
    before = 'def run (targetName : Option Name := none) : TermElabM Unit := do\n  let some output ← IO.getEnv "FLEX_PARITY_OUTPUT"'
    after = ('def run (targetName : Option Name := none) (outputDir : Option System.FilePath := none) : TermElabM Unit := do\n'
             '  let output? ← match outputDir with\n'
             '    | some path => pure (some path.toString)\n'
             '    | none => IO.getEnv "FLEX_PARITY_OUTPUT"\n'
             '  let some output := output?')
    if header.count(before) != 1: raise ValueError('unsupported frozen harness signature')
    return header.replace(before, after) + '\n' + implementation.removeprefix('import Lean\n') + '\nrq3_batch_worker\n'


class Worker:
    def __init__(self, command, env, output, common, index):
        self.common, self.output, self.index = common, output, index
        self.messages = queue.Queue()
        self.log = (output / f'worker-{index}.log').open('w')
        begin = time.perf_counter()
        self.process = subprocess.Popen([*command, str(output/'Worker.lean')], cwd=common.ROOT,
            env=env, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, bufsize=1, start_new_session=True)
        def consume():
            for line in self.process.stdout:
                self.log.write(line); self.log.flush()
                # Profiling can flush a partial line before this independently written frame.
                _, marker, payload = line.partition('RQ3_WORKER ')
                if marker:
                    try: self.messages.put(json.JSONDecoder().raw_decode(payload)[0])
                    except ValueError: self.messages.put({'kind':'error', 'error':'malformed protocol'})
            self.messages.put({'kind':'eof'})
        self.reader = threading.Thread(target=consume, daemon=True); self.reader.start()
        try:
            ready = self.messages.get(timeout=60)
            if ready.get('kind') != 'ready': raise RuntimeError(f'worker startup failed: {ready}')
        except BaseException:
            self.stop(force=True); raise
        self.startup_ms = (time.perf_counter()-begin)*1000

    def request(self, id, source, log, timeout):
        self.process.stdin.write(json.dumps({'id':id, 'source':str(source), 'log':str(log)})+'\n')
        self.process.stdin.flush()
        response = self.messages.get(timeout=timeout)
        if response.get('kind') != 'done' or response.get('id') != id:
            raise RuntimeError(f'worker protocol failure: {response}')
        return response

    def stop(self, force=False):
        if self.process.poll() is None:
            if force: self.common.terminate_case(self.process)
            else:
                self.process.stdin.close()
                try: self.process.wait(timeout=10)
                except subprocess.TimeoutExpired: self.common.terminate_case(self.process)
        self.reader.join(timeout=5)
        self.log.close()


def smoke(worker, output):
    sources = [
        'def pilot_leaked : Nat := 7\nset_option pp.universes true\nexample : pilot_leaked = 7 := rfl\n',
        'run_elab do\n  if (← getEnv).contains `pilot_leaked then throwError "environment leaked"\n  if (← getOptions).getBool `pp.universes false then throwError "options leaked"\ndef pilot_leaked : Nat := 11\nexample : pilot_leaked = 11 := rfl\n',
        'example : False := by exact True.intro\n',
        'def pilot_leaked : Nat := 13\nexample : pilot_leaked = 13 := rfl\n']
    results=[]
    for i, source in enumerate(sources):
        path=output/f'smoke-{i}.lean';path.write_text(source)
        result=worker.request(f'smoke-{i}',path,path.with_suffix('.log'),30)
        if result['has_errors'] != (i==2): raise RuntimeError(f'isolation check failed: {result}')
        results.append(result)
    write(output/'isolation-checks.json',results)


def terminal(record):
    return next((e for e in reversed(record.get('events',[])) if e['stage']=='result'),{})


def observations(record):
    end=terminal(record)
    return {k: (record['status'] if k=='status' else end.get(k)) for k in
        ['status','kernel_checked','fully_proved','original_predicates','remaining_predicates','goals']}


def run_batch(cases, previous, command, env, out, common, watchdog, workers, meta):
    """One long-lived Lean process per worker; append results instead of rewriting CSVs."""
    from concurrent.futures import ThreadPoolExecutor
    jobs, finished = queue.Queue(), queue.Queue()
    for case in cases: jobs.put(case)
    starts, shutdowns, active = {}, {}, {}
    lock = threading.Lock()
    started = time.perf_counter()
    def work(slot):
        worker, generation = None, 0
        try:
            while True:
                try: case = jobs.get_nowait()
                except queue.Empty: return
                with lock: active[slot] = {'case':case['case'],'started_seconds':time.perf_counter()-started}
                if case['inventory_status'] != 'translated':
                    record={'case':case['case'],'suite':case['suite'],'status':'preparation_failed',
                            'error':case.get('preparation_error',''),'wall_ms':None,'events':[]}
                else:
                    if worker is None:
                        worker=Worker(command,env,out,common,f'{slot}-{generation}');generation+=1
                        with lock: starts[worker.index]=worker.startup_ms
                    begin=time.perf_counter(); dispatched=time.time_ns()//1000000
                    directory=out/'batch'/case['case'].removesuffix('.lean');directory.mkdir(parents=True)
                    path=directory/'Case.lean'
                    statements=re.sub(r'^import .*\n','',Path(case['generated']).read_text(),flags=re.M)
                    path.write_text(statements+f'\nrun_elab FlexParity.run (some ``{case["declaration"]}) (some ⟨{json.dumps(str(directory))}⟩)\n')
                    record={'case':case['case'],'suite':case['suite'],'artifacts':str(directory),
                            'worker':worker.index,'error':'','events':[]}
                    try:
                        response=worker.request(case['case'],path,directory/'lean.log',watchdog)
                        record['events'],record['error']=common.read_events(directory/'events.jsonl')
                        record['status']='lean_failed' if response['has_errors'] else terminal(record).get('status','missing_result')
                        if record['error']: record['status']='invalid_events'
                        record['request_ns']=response['request_ns']
                    except (queue.Empty,RuntimeError,BrokenPipeError) as error:
                        record['status']='case_timeout' if isinstance(error,queue.Empty) else 'worker_failed'
                        record['error']=str(error);worker.stop(force=True);worker=None
                        record['events'],_=common.read_events(directory/'events.jsonl')
                    record['wall_ms']=(time.perf_counter()-begin)*1000
                    event=next((e for e in record['events'] if e['stage']=='start'),{})
                    record['dispatch_to_start_ms']=event.get('unix_ms',dispatched)-dispatched
                    write(directory/'result.json',record)
                record['preparation_refreshed']=bool(case.get('preparation_refresh'))
                finished.put(record)
                with lock: active.pop(slot,None)
        finally:
            if worker:
                begin=time.perf_counter();worker.stop()
                with lock: shutdowns[worker.index]=(time.perf_counter()-begin)*1000
    records=[];counts=collections.Counter();matched=0;writer=None;last_report=0
    def progress(state='running'):
        with lock: running=dict(active); start_times=dict(starts)
        value={'state':state,'completed':len(records),'total':len(cases),'remaining':len(cases)-len(records),
               'wall_seconds':round(time.perf_counter()-started,3),'outcomes':dict(counts),
               'cumulative_query_seconds':round(sum(r.get('wall_ms') or 0 for r in records)/1000,3),
               'worker_startup_ms':start_times,'active':running}
        write(out/'progress.json',value)
        return value
    with (out/'records.jsonl').open('w') as raw, (out/'results.csv').open('w',newline='') as csvfile:
        with ThreadPoolExecutor(max_workers=workers) as pool:
            futures=[pool.submit(work,i) for i in range(workers)]
            while len(records)<len(cases):
                try: record=finished.get(timeout=1)
                except queue.Empty:
                    for future in futures:
                        if future.done(): future.result()
                    if time.perf_counter()-last_report>=5:
                        progress();last_report=time.perf_counter()
                    continue
                records.append(record);counts[record['status']]+=1
                prior=previous[record['case']];same=observations(record)==observations(prior);matched+=same
                row={'case':record['case'],'suite':record['suite'],'preparation_refreshed':record['preparation_refreshed'],
                     **observations(record),'wall_ms':record.get('wall_ms'),'flex_ms':terminal(record).get('flex_ms'),
                     'kernel_ms':next((e.get('elapsed_ms') for e in reversed(record.get('events',[])) if e['stage']=='kernel' and e['status']=='ok'),None),
                     'worker':record.get('worker'),'previous_status':prior['status'],
                     'previous_wall_ms':prior.get('wall_ms'),'previous_outcome_matches':same}
                if writer is None: writer=csv.DictWriter(csvfile,fieldnames=list(row));writer.writeheader()
                writer.writerow(row);csvfile.flush()
                raw.write(json.dumps(record)+'\n');raw.flush()
                if len(records)%25==0 or len(records)==len(cases):
                    os.fsync(raw.fileno());value=progress()
                    print(f'{len(records)}/{len(cases)} in {value["wall_seconds"]:.1f}s: {dict(counts)}',flush=True)
                elif time.perf_counter()-last_report>=5:
                    progress();last_report=time.perf_counter()
            for future in futures:future.result()
    summary=progress('complete')
    summary.update(complete=True,workers=workers,kernel_checked=sum(terminal(r).get('kernel_checked') is True for r in records),
        fully_proved=sum(r['status']=='proved' and terminal(r).get('kernel_checked') is True for r in records),
        matching_previous_outcomes=matched,preparation_refreshed=sum(r['preparation_refreshed'] for r in records),
        worker_shutdown_ms=shutdowns,
        cumulative_processing_seconds=(sum(r.get('wall_ms') or 0 for r in records)+sum(starts.values())+sum(shutdowns.values()))/1000,
        previous_cumulative_query_seconds=sum(previous[c['case']].get('wall_ms') or 0 for c in cases)/1000,
        time_accounting='Wall includes worker startup, processing, result recording and worker shutdown. Cumulative processing sums per-query times, worker startup and shutdown across workers. Setup is recorded separately.')
    summary['setup_seconds']=meta['setup_seconds']
    summary['total_elapsed_seconds']=summary['wall_seconds']+meta['setup_seconds']
    write(out/'summary.json',summary);write(out/'progress.json',summary)
    meta.update(complete=True,finished_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()))
    write(out/'metadata.json',meta)
    print(json.dumps(summary,indent=2),flush=True)


def main():
    setup_started=time.perf_counter()
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--previous',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--count',type=int,default=50)
    parser.add_argument('--seed',type=int,default=20261109)
    parser.add_argument('--batch-only',action='store_true')
    parser.add_argument('--workers',type=int,default=2)
    parser.add_argument('--minimal-metrics',action='store_true')
    parser.add_argument('--refresh-failures',type=Path)
    args=parser.parse_args(); old=args.previous.resolve(); out=args.output.resolve()
    if args.workers < 1: raise ValueError('workers must be positive')
    if args.count == 0 and not args.batch_only: raise ValueError('--count 0 requires --batch-only')
    if out.exists() and any(out.iterdir()): raise ValueError('use a new output directory')
    out.mkdir(parents=True,exist_ok=True)
    root=old.parents[3]
    spec=importlib.util.spec_from_file_location('pilot_common',old/'source/scripts/chc_parity.py')
    common=importlib.util.module_from_spec(spec);spec.loader.exec_module(common);common.ROOT=root
    settings=json.loads((old/'settings.json').read_text())
    if settings['configs'] != ['zap_fix']: raise ValueError('pilot expects the frozen Zap + Fix run')
    selection=json.loads((old/'selection.json').read_text())
    if args.count == 0:
        cases=selection['cases']['a'];population=len(cases)
        counts=dict(collections.Counter(c['suite'] for c in cases))
    else: cases,population,counts=choose(selection['cases']['a'],args.count,args.seed)
    if args.refresh_failures:
        import corpus
        repo=args.refresh_failures.resolve()
        revision=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip()
        for i,case in enumerate(cases):
            if case['inventory_status']=='translated': continue
            source=repo/case['repo_path']
            if common.digest(source)!=case['source_sha256']: raise ValueError(f'VC changed: {case["case"]}')
            text,dependencies=corpus.flatten(source,repo)
            target=out/'refreshed-statements'/f'{i:03}.lean';target.parent.mkdir(exist_ok=True)
            target.write_text(text)
            case.update(generated=str(target),generated_sha256=common.digest(target),
                inventory_status='translated',dependencies=dependencies,
                preparation_refresh={'revision':revision,'vc_unchanged':True,
                    'previous_error':case.get('preparation_error','')})
    previous={r['case']:r for r in map(json.loads,(old/'results.jsonl').read_text().splitlines())}
    if args.batch_only:
        cases.sort(key=lambda c: (-float(previous[c['case']].get('wall_ms') or 0),c['case']))
    for case in cases:
        if case['inventory_status']!='translated': continue
        if common.digest(Path(case['generated'])) != case['generated_sha256']: raise ValueError('changed statement')
        if case['format'] != 'lean_statement': raise ValueError('pilot requires prepared Lean statements')
    write(out/'selection.json',{'seed':args.seed,'population':population,'counts':counts,
        'method':('All inputs; longest historical runs scheduled first' if args.count==0 else 'Proportional stratified random sample; no filtering by outcome or runtime'),'cases':cases})
    header=(old/'source/evaluation/RQ3a/RQ3.lean').read_text()
    implementation=Path(__file__).with_name('Batch.lean').read_text()
    generated_worker=worker_source(header,implementation)
    if args.minimal_metrics:
        before='              residuals := residuals ++ [(← Meta.ppGoal goal).pretty]'
        if generated_worker.count(before)!=1: raise ValueError('unexpected residual formatter')
        generated_worker=generated_worker.replace('            let mut residuals := []\n','')
        generated_worker=generated_worker.replace(before+'\n','')
        generated_worker=generated_worker.replace('            IO.FS.writeFile (output / "residual.txt") (String.intercalate "\\n\\n---\\n\\n" residuals)\n','')
        generated_worker=generated_worker.replace('          let after ← measure output "checkpoint/format"','          let after ← measure output "checkpoint/count"')
    (out/'Worker.lean').write_text(generated_worker)
    command=json.loads((old/'frozen-command.json').read_text())
    env={**os.environ,**json.loads((old/'frozen-environment.json').read_text()),'LEAN_NUM_THREADS':'2',
        'FLEX_PARITY_ZAP':'1','FLEX_PARITY_FULL':'1','FLEX_PARITY_SE':'0','FLEX_PARITY_SCRAPE':'auto',
        'RQ3_CHC_FIRST':'0','RQ3_STAGE_SECONDS':'0','FLEX_PARITY_PROFILE_PA':'1','RQ3_DIAGNOSTIC':'0',
        'FLEX_PARITY_FLEX_SECONDS':str(settings['flex_timeout']),
        'FLEX_PARITY_SOLVER_SECONDS':str(settings['solver_timeout']),
        'FLEX_PARITY_HEARTBEATS':str(settings['heartbeats']),
        'FLEX_PARITY_PROOF_HEARTBEATS':str(settings['proof_heartbeats']),
        'FLEX_PARITY_RECURSION_LIMIT':'16384','FLEX_PARITY_EXECUTABLE':settings['z3'],
        'FLEX_PARITY_ELDARICA_EXECUTABLE':settings['eldarica'],
        'RQ3_CLASSIFY':'0' if settings['skip_classification'] else '1'}
    if args.minimal_metrics:
        env.update(FLEX_PARITY_PROFILE_PA='0',RQ3_CLASSIFY='0')
    watchdog=settings['configuration_budgets']['zap_fix']['case_timeout']
    env['FLEX_PARITY_CASE_SECONDS']=str(watchdog)
    fresh_args=SimpleNamespace(output=out/'fresh',mode='flex',eldarica=settings['eldarica'],z3=settings['z3'],
        solver_timeout=settings['solver_timeout'],heartbeats=settings['heartbeats'],
        proof_heartbeats=settings['proof_heartbeats'],proof_timeout=0,smt_timeout=settings['flex_timeout'],case_timeout=watchdog)
    meta={'previous':str(old),'previous_metadata':json.loads((old/'metadata.json').read_text()),
        'count':len(cases),'seed':args.seed,'workers':1,'lean_threads':2,'watchdog_seconds':watchdog,
        'method':'Alternating fresh/batch order per paired query; one active query at a time; same frozen inputs, Flex artifacts, options and proof checks. Batch time includes startup once, excludes idle time while fresh arm runs.',
        'harness_change':'Only optional per-request output path; solver and kernel-checking logic unchanged.',
        'worker_sha256':common.digest(out/'Worker.lean'),'script_sha256':common.digest(Path(__file__)),
        'started_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
    if args.batch_only:
        meta.update(workers=args.workers,minimal_metrics=args.minimal_metrics,
            method='Persistent workers; same frozen solver and proof checks; longest known jobs first; no fresh-process comparison arm.')
    source=out/'source';source.mkdir()
    (source/'startup.py').write_text(Path(__file__).read_text())
    (source/'Batch.lean').write_text(implementation)
    meta['setup_seconds']=time.perf_counter()-setup_started
    write(out/'metadata.json',meta)
    if args.batch_only:
        run_batch(cases,previous,command,env,out,common,watchdog,args.workers,meta)
        return
    smoke_worker=Worker(command,env,out,common,'smoke')
    try: smoke(smoke_worker,out)
    finally: smoke_worker.stop()
    # A separate worker avoids warming the measured one with smoke examples.
    worker=None; startups=[]; records=[]; paired=[]; began=time.perf_counter()
    try:
        for i,case in enumerate(cases):
            results={}
            for arm in (['fresh','batch'] if i%2==0 else ['batch','fresh']):
                write(out/'progress.json',{'state':'running','completed_pairs':i,'total_pairs':len(cases),'case':case['case'],'arm':arm,'wall_seconds':round(time.perf_counter()-began,2)})
                if arm=='fresh':
                    record=common.run_case(case,'zap_fix',fresh_args,command,env,header)
                else:
                    if worker is None:
                        worker=Worker(command,env,out,common,len(startups));startups.append(worker.startup_ms)
                    begin=time.perf_counter();dispatch_unix_ms=time.time_ns()//1000000
                    directory=out/'batch'/case['case'].removesuffix('.lean');directory.mkdir(parents=True)
                    path=directory/'Case.lean'
                    statements=re.sub(r'^import .*\n','',Path(case['generated']).read_text(),flags=re.M)
                    path.write_text(statements+f'\nrun_elab FlexParity.run (some ``{case["declaration"]}) (some ⟨{json.dumps(str(directory))}⟩)\n')
                    record={'case':case['case'],'artifacts':str(directory),'events':[],'error':'','worker':worker.index}
                    try:
                        response=worker.request(case['case'],path,directory/'lean.log',watchdog)
                        record['events'],record['error']=common.read_events(directory/'events.jsonl')
                        end=terminal(record)
                        record['status']='lean_failed' if response['has_errors'] else end.get('status','missing_result')
                        if record['error']: record['status']='invalid_events'
                        record['request_ns']=response['request_ns']
                    except (queue.Empty,RuntimeError,BrokenPipeError) as error:
                        record['status']='case_timeout' if isinstance(error,queue.Empty) else 'worker_failed'
                        record['error']=str(error);worker.stop(force=True);worker=None
                        record['events'],_=common.read_events(directory/'events.jsonl')
                    record['wall_ms']=(time.perf_counter()-begin)*1000
                    start=next((e for e in record['events'] if e['stage']=='start'),{})
                    record['dispatch_to_start_ms']=start.get('unix_ms',dispatch_unix_ms)-dispatch_unix_ms
                    write(directory/'result.json',record)
                record.update(arm=arm,suite=case['suite'])
                results[arm]=record;records.append(record)
                with (out/'records.jsonl').open('a') as stream:
                    stream.write(json.dumps(record)+'\n');stream.flush();os.fsync(stream.fileno())
            fresh,batch=results['fresh'],results['batch'];prior=previous[case['case']]
            row={'case':case['case'],'suite':case['suite'],
                'outcomes_match':observations(fresh)==observations(batch),
                'previous_outcome_matches':observations(prior)==observations(batch)}
            for arm,record in [('previous',prior),('fresh',fresh),('batch',batch)]:
                row.update({f'{arm}_{k}':v for k,v in observations(record).items()})
                for k in ['wall_ms','startup_ms','dispatch_to_start_ms']:
                    row[f'{arm}_{k}']=record.get(k)
                row[f'{arm}_flex_ms']=terminal(record).get('flex_ms')
                row[f'{arm}_kernel_ms']=next((e.get('elapsed_ms') for e in reversed(record.get('events',[])) if e['stage']=='kernel' and e['status']=='ok'),None)
            paired.append(row)
            with (out/'results.csv').open('w',newline='') as stream:
                writer=csv.DictWriter(stream,fieldnames=list(row));writer.writeheader();writer.writerows(paired)
            print(f'{i+1}/{len(cases)} {case["suite"]}: {fresh["status"]}/{batch["status"]}, {fresh["wall_ms"]:.0f}ms -> {batch["wall_ms"]:.0f}ms, match={row["outcomes_match"]}',flush=True)
    finally:
        if worker: worker.stop()
    def summary_arm(arm):
        rows=[r for r in records if r['arm']==arm]
        ms=[r['wall_ms'] for r in rows];flex=[terminal(r).get('flex_ms') for r in rows]
        flex=[v for v in flex if v is not None]
        return {'outcomes':dict(collections.Counter(r['status'] for r in rows)),
                'fully_proved':sum(terminal(r).get('fully_proved') is True and terminal(r).get('kernel_checked') is True and r['status']=='proved' for r in rows),
                'sum_query_wall_ms':sum(ms),'median_query_wall_ms':statistics.median(ms),
                'median_flex_ms':statistics.median(flex) if flex else None,'measured_flex_queries':len(flex)}
    fresh=summary_arm('fresh');batch=summary_arm('batch')
    batch['worker_startup_ms']=startups;batch['total_including_startup_ms']=batch['sum_query_wall_ms']+sum(startups)
    batch['amortized_mean_including_startup_ms']=batch['total_including_startup_ms']/len(cases)
    summary={'complete':True,'cases':len(cases),'fresh':fresh,'batch':batch,
        'speedup_including_startup':fresh['sum_query_wall_ms']/batch['total_including_startup_ms'],
        'matching_outcomes':sum(r['outcomes_match'] for r in paired),
        'matching_previous_outcomes':sum(r['previous_outcome_matches'] for r in paired),
        'previous_selected_sum_wall_ms':sum(previous[c['case']]['wall_ms'] for c in cases),
        'previous_comparison_note':'Historical run had two workers and potentially different contention; fresh paired replay is the controlled comparator.',
        'pilot_wall_seconds':time.perf_counter()-began}
    write(out/'summary.json',summary);write(out/'progress.json',{'state':'complete',**summary})
    print(json.dumps(summary,indent=2),flush=True)

if __name__=='__main__':main()
