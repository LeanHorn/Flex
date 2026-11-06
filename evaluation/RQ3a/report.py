"""Coverage tables and figures from the frozen RQ3 per-query records."""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import csv
import json
import os
from pathlib import Path
import statistics
import itertools
import math
import tempfile

LABELS={'zap_fix':'Zap + Fix', 'se':'S/E only', 'flex':'Full Flex',
        'se_zap_fix':'S/E → Zap + Fix',
        'native_spacer':'Spacer (SMT)', 'native_eldarica':'Eldarica (SMT)'}


def read_jsonl(path):
    return [json.loads(l) for l in path.read_text().splitlines(keepends=True)
            if l.endswith('\n') and l.strip()] if path.exists() else []


def read(output):
    return read_jsonl(output/'results.jsonl')


def phase_events(record, output):
    if 'phase_events' in record:
        return record['phase_events']
    # Older runs stored absolute paths. Prefer artifacts inside a copied result folder.
    local = output/'runs'/record['study']/'cases'/record['configuration']/record['case'].removesuffix('.lean')
    candidates = [local, output/record.get('artifacts', '')]
    if record.get('record_source'):
        candidates.insert(1, Path(record['record_source']).parent/'runs'/record['study']/
                          'cases'/record['configuration']/record['case'].removesuffix('.lean'))
    for directory in candidates:
        path = directory/'phases.jsonl'
        if path.is_file(): return read_jsonl(path)
    return []


def budget_caption(settings):
    single = settings['flex_timeout']
    combined = settings.get('combined_timeout', single)
    internal = (f'{single} s internal Flex budget' if single == combined else
                f'{single} s Zap + Fix / S/E only; {combined} s combined')
    return f'{internal} · {settings["solver_timeout"]} s per S/E call · {settings.get("workers", 1)} worker(s)'


def stage_budget(config, settings):
    configured=settings.get('configuration_budgets',{}).get(config,{})
    if 'stage_timeout' in configured:
        return configured['stage_timeout'] or None
    # Earlier S/E-first runs had a block cap; the original internal-first arm did not.
    return settings['flex_timeout'] if config=='se_zap_fix' else None


def backend_usage(phases, events):
    usage={}
    for backend in ['fix','spacer','eldarica']:
        rows=[e for e in phases if e['phase']=='attempt/'+backend]
        starts=[e for e in rows if e['status']=='start']
        calls=[e for e in events if e['stage']=='chc/solver' and e.get('solver_backend')==backend]
        usage[backend+'_attempts']=len(starts)
        skipped=[e['status'] for e in rows if e['status'].startswith('skipped_')]
        usage[backend+'_skipped']=len(skipped)
        usage[backend+'_skip_reasons']=';'.join(sorted(set(skipped)))
        if backend!='fix':
            usage[backend+'_calls_completed']=len(calls)
            counts=Counter(e['backend_attempt'] for e in calls if 'backend_attempt' in e)
            usage[backend+'_retries_completed']=sum(max(0,count-1) for count in counts.values())
    return usage


def distribution(values):
    values = sorted(v for v in values if v is not None and math.isfinite(v))
    if not values: return {'n': 0}
    def percentile(q):
        position = (len(values)-1)*q
        lower = int(position)
        upper = min(lower+1, len(values)-1)
        return values[lower] + (position-lower)*(values[upper]-values[lower])
    return {'n': len(values), 'sum': sum(values), 'mean': statistics.mean(values),
            'min': values[0], 'p25': percentile(.25), 'median': percentile(.5),
            'p75': percentile(.75), 'p90': percentile(.90), 'p95': percentile(.95),
            'max': values[-1]}


def row(record, cases, classes, phases):
    key=(record['study'],record['case']); case=cases[key]
    terminal=next((e for e in reversed(record.get('events',[])) if e['stage']=='result'),{})
    checked=terminal.get('kernel_checked') is True and record['status'] in {'proved','partial'}
    proved=checked and terminal.get('fully_proved') is True
    all_inst=checked and terminal.get('all_predicates_instantiated') is True
    retention=terminal.get('retention',{})
    all_heads=proved or (all_inst and retention.get('heads_known') is True and retention.get('remaining_heads')==0)
    events=record.get('events',[])
    model=any(e['stage']=='chc/solver' and e['status']=='sat' for e in events)
    imported=any(e['stage']=='chc/import' and e['status']=='ok' for e in events)
    before=terminal.get('original_predicates')
    after=terminal.get('remaining_predicates')
    removed=max(0,before-after) if checked and before is not None and after is not None else 0
    category=('proved' if proved else 'heads_eliminated' if all_heads else
              'instantiated' if all_inst else 'some_predicates' if removed else
              'preparation_failed' if record['status']=='preparation_failed' else 'no_certified_progress')
    starts=defaultdict(list); durations=defaultdict(float); beats=defaultdict(float)
    completed=Counter()
    for e in phases:
        if e['status']=='start':
            starts[e['phase']].append(e)
        elif starts[e['phase']]:
            start=starts[e['phase']].pop()
            completed[e['phase']]+=1
            durations[e['phase']]+=e.get('elapsed_ms',0)
            beats[e['phase']]+=(e.get('heartbeats_raw',0)-start.get('heartbeats_raw',0))/1000
    base={'study':record['study'],'case':record['case'],'suite':case['suite'],
          'configuration':record['configuration'],'status':record['status'],'category':category,
          'structure':classes.get(key,{}).get('kind','unclassified'),'input_bytes':case['bytes'],
          'family':case.get('family'), 'track':case.get('track'),
          'source_sha256':case.get('source_sha256'), 'generated_sha256':case.get('generated_sha256'),
          **{f'classified_{k}':classes.get(key,{}).get(k) for k in ['acyclic','cyclic','eliminable','cut']},
          'model_obtained_attempt':model,'imported_attempt':imported,'kernel_checked':checked,
          'all_predicates_instantiated':all_inst,'all_heads_eliminated':all_heads,'fully_proved':proved,
          'original_predicates':before,'remaining_predicates':after,'instantiated_count':removed,
          'remaining_heads':retention.get('remaining_heads'),'heads_known':retention.get('heads_known'),
          'wall_ms':record.get('wall_ms'),'startup_ms':record.get('startup_ms'),
          'flex_ms':terminal.get('flex_ms'),'tactic_heartbeats':terminal.get('tactic_heartbeats'),
          'total_heartbeats':terminal.get('heartbeats'),'recursion_limit':terminal.get('recursion_limit'),
          'peak_recursion_depth':terminal.get('peak_recursion_depth'),
          'native_ms':record.get('elapsed_ms'),
          'native_model_obtained':record.get('model_obtained',False),'error':record.get('error',''),
          'artifacts':record.get('artifacts'),
          **{k:terminal.get('proof_metrics',{}).get(k) for k in
             ['kernel_ns','proof_nodes','proof_depth','proof_constants']}}
    if record['status']=='preparation_failed':base['wall_ms']=None
    base['predicate_progress'] = category in {'proved','heads_eliminated','instantiated','some_predicates'}
    base['genuine_partial_progress'] = base['predicate_progress'] and not proved
    base['solver_calls'] = sum(e['stage']=='chc/solver' for e in events)
    base['record_source'] = record.get('record_source')
    for metric, match in [('solver',lambda k:k.endswith('/solver')),
                          ('fix',lambda k:k=='fix'), ('zap',lambda k:k=='zap'),
                          ('discharge',lambda k:k=='discharge'), ('kernel',lambda k:k=='verify/kernel')]:
        base[metric+'_ms']=(sum(v for k,v in durations.items() if match(k))
            if phases and not any(v for k,v in starts.items() if match(k)) else None)
    base['internal_timeout']=any(e['status']=='timeout' for e in phases)
    base['phase_log_complete']=bool(phases) and not any(starts.values())
    base['last_event_stage']=events[-1]['stage'] if events else None
    base['solver_timeouts']=sum(e['stage']=='chc/solver' and e['status']=='timeout' for e in events)
    base['tactic_time_measured'] = base['flex_ms'] is not None
    base['external_timeout'] = record['status'] in {'case_timeout','process_timeout'}
    return base,[{'study':base['study'],'case':base['case'],'configuration':base['configuration'],
                  'phase':k,'ms':durations[k] if not starts[k] else None,
                  'completed_ms':durations[k], 'completed_calls':completed[k],
                  'unfinished_calls':len(starts[k]),
                  'heartbeats':beats[k] if not starts[k] else None}
                 for k in sorted(durations.keys() | starts.keys())]


def write_csv(path,rows,fields=()):
    fields=list(dict.fromkeys([*fields, *(k for r in rows for k in r)]))
    with tempfile.NamedTemporaryFile(mode='w',newline='',dir=path.parent,
                                     prefix=path.name+'.',suffix='.tmp',delete=False) as f:
        temporary=Path(f.name)
        writer=csv.DictWriter(f,fieldnames=fields)
        writer.writeheader();writer.writerows(rows)
    temporary.replace(path)


def detailed_statistics(output, rows):
    metrics = ['flex_ms','wall_ms','startup_ms','native_ms','zap_ms','fix_ms','solver_ms',
               'discharge_ms','kernel_ms','tactic_heartbeats','total_heartbeats',
               'proof_nodes','proof_depth','proof_constants','kernel_ns','solver_calls']
    stats, comparisons = [], []
    for study, config in sorted({(r['study'],r['configuration']) for r in rows}):
        group = [r for r in rows if (r['study'],r['configuration'])==(study,config)]
        for suite in ['ALL'] + sorted({r['suite'] for r in group}):
            selected = [r for r in group if suite=='ALL' or r['suite']==suite]
            populations=(['all_measured','model_returned','no_model'] if config.startswith('native_')
                         else ['all_measured','proved','not_proved'])
            for population in populations:
                field='native_model_obtained' if config.startswith('native_') else 'fully_proved'
                subset = [r for r in selected if population=='all_measured' or
                          r[field]==(population in {'proved','model_returned'})]
                for metric in metrics:
                    stats.append({'study':study,'configuration':config,'suite':suite,
                                  'population':population,'metric':metric,
                                  'queries':len(subset),
                                  **distribution([r.get(metric) for r in subset])})
    for study in sorted({r['study'] for r in rows}):
        configs = sorted({r['configuration'] for r in rows if r['study']==study
                          and not r['configuration'].startswith('native_')})
        for first, second in itertools.combinations(configs,2):
            a = {r['case']:r for r in rows if r['study']==study and r['configuration']==first}
            b = {r['case']:r for r in rows if r['study']==study and r['configuration']==second}
            shared = a.keys() & b.keys()
            joint = [c for c in shared if a[c]['fully_proved'] and b[c]['fully_proved']]
            for metric in ['flex_ms','wall_ms']:
                pairs = [(a[c][metric],b[c][metric]) for c in joint
                         if a[c].get(metric) is not None and b[c].get(metric) is not None]
                ratios = [x/y for x,y in pairs if y>0]
                comparisons.append({'study':study,'first':first,'second':second,
                    'completed_pairs':len(shared),'both_proved':len(joint),
                    'first_only_proved':sum(a[c]['fully_proved'] and not b[c]['fully_proved'] for c in shared),
                    'second_only_proved':sum(b[c]['fully_proved'] and not a[c]['fully_proved'] for c in shared),
                    'metric':metric,'timed_pairs':len(pairs),
                    **{f'first_{k}':v for k,v in distribution([x for x,y in pairs]).items()},
                    **{f'second_{k}':v for k,v in distribution([y for x,y in pairs]).items()},
                    'ratio_pairs':len(ratios),
                    'median_first_over_second':statistics.median(ratios) if ratios else None})
    write_csv(output/'statistics.csv',stats,['study','configuration','suite','population','metric','n'])
    write_csv(output/'comparisons.csv',comparisons,['study','first','second','completed_pairs'])


def flatten_event(event, prefix=''):
    fields={}
    for key,value in event.items():
        name=prefix+key
        if isinstance(value,dict): fields.update(flatten_event(value,name+'_'))
        else: fields[name]=json.dumps(value) if isinstance(value,list) else value
    return fields


def coverage_table(rows, selected):
    result=[]
    milestones=['all_predicates_instantiated','all_heads_eliminated','fully_proved',
                'genuine_partial_progress','predicate_progress','native_model_obtained']
    for study,cases in selected.items():
        for config in sorted({r['configuration'] for r in rows if r['study']==study}):
            for suite in ['ALL']+sorted({c['suite'] for c in cases}):
                total=sum(suite=='ALL' or c['suite']==suite for c in cases)
                group=[r for r in rows if r['study']==study and r['configuration']==config
                       and (suite=='ALL' or r['suite']==suite)]
                item={'study':study,'configuration':config,'suite':suite,
                      'queries':total,'completed':len(group),'pending':total-len(group),
                      'outer_timeouts':sum(r['external_timeout'] for r in group)}
                for metric in milestones:
                    count=sum(bool(r[metric]) for r in group)
                    item[metric]=count
                    item[metric+'_percent']=100*count/total if total else None
                result.append(item)
    return result


def tables(output):
    selection=json.loads((output/'selection.json').read_text())
    cases={(s,c['case']):c for s,cs in selection['cases'].items() for c in cs}
    cp=output/'classification.json'
    classes={(r['study'],r['case']):r for r in json.loads(cp.read_text())} if cp.exists() else {}
    settings=json.loads((output/'settings.json').read_text())
    rows=[];phases=[];events=[];phase_rows=[]
    for record in read(output):
        raw_phases=phase_events(record,output)
        r,p=row(record,cases,classes,raw_phases)
        native=record['configuration'].startswith('native_')
        combined=record['configuration'] in {'flex','se_zap_fix'}
        budget=settings.get('combined_timeout',settings['flex_timeout']) if combined else settings['flex_timeout']
        r.update(flex_budget_seconds=None if native else budget,
                 solver_budget_seconds=settings['solver_timeout'],
                 stage_budget_seconds=stage_budget(record['configuration'],settings),
                 timeout_policy=settings.get('timeout_policy','legacy_shared_deadline'),
                 phase_heartbeat_limit=None if native else settings['heartbeats'],
                 proof_heartbeat_limit=None if native else settings['proof_heartbeats'],
                 watchdog_seconds=settings['solver_timeout']+30 if native else
                     settings.get('case_timeout') or budget+120,
                 workers=settings.get('workers',1))
        if settings.get('timeout_policy')=='reserved_blocks_v1' and not native:
            r.update(backend_usage(raw_phases, record.get('events',[])))
        rows.append(r);phases+=p
        identity={k:r[k] for k in ['study','case','configuration']}
        events.extend({**identity,'event_index':i,**flatten_event(e)}
                      for i,e in enumerate(record.get('events',[])))
        phase_rows.extend({**identity,'event_index':i,**e} for i,e in enumerate(raw_phases))
    identity=['study','case','configuration']
    write_csv(output/'results.csv',rows,identity)
    write_csv(output/'phases.csv',phases,[*identity,'phase','ms','heartbeats'])
    write_csv(output/'events.csv',events,[*identity,'event_index','stage','status'])
    write_csv(output/'phase_events.csv',phase_rows,[*identity,'event_index','phase','status'])
    selected={s:cs for s,cs in selection['cases'].items() if cs}
    write_csv(output/'coverage.csv',coverage_table(rows,selected),['study','configuration','suite','queries','completed'])
    summary={'selected':{s:len(cs) for s,cs in selected.items()},'completed_runs':len(rows),
             'by_configuration':{},'structure':{s:dict(Counter(classes.get((s,c['case']),{}).get('kind','unclassified') for c in cs)) for s,cs in selected.items()}}
    for study in selected:
        observed = sorted({r['configuration'] for r in rows if r['study']==study})
        for config in observed:
            group=[r for r in rows if r['study']==study and r['configuration']==config]
            timings=[r['flex_ms'] for r in group if r.get('flex_ms') is not None]
            summary['by_configuration'][study+'/'+config]={
                'completed':len(group),'outcomes':dict(Counter(r['status'] for r in group)),
                'categories':dict(Counter(r['category'] for r in group)),
                **{field:sum(bool(r[field]) for r in group) for field in
                   ['model_obtained_attempt','imported_attempt','all_predicates_instantiated','all_heads_eliminated','fully_proved','genuine_partial_progress']},
                'native_sat':sum(r['status'] in {'sat','sat_no_model'} for r in group),
                'native_models':sum(r['native_model_obtained'] for r in group),
                'median_flex_ms_all_terminal':statistics.median(timings) if timings else None,
                'tactic_timing_all_measured_ms':distribution(timings),
                'tactic_timing_proved_ms':distribution([r['flex_ms'] for r in group if r['fully_proved']]),
                'process_timing_all_measured_ms':distribution([r['wall_ms'] for r in group]),
                'unmeasured_tactic_times':sum(r['flex_ms'] is None for r in group)}
    native={c['case']:{} for c in selected.get('b',[])}
    for r in rows:
        if r['configuration'].startswith('native_'):native[r['case']][r['configuration']]=r['status']
    if native:
        summary['native_union']={'paired_completed':sum(len(v)==2 for v in native.values()),
                                 'either_model_observed':sum(any(s == 'sat' for s in v.values()) for v in native.values()),
                                 'either_sat_observed':sum(any(s in {'sat','sat_no_model'} for s in v.values()) for v in native.values())}
    discrepancy=[]
    for r in rows:
        if r['study']=='b' and r['configuration']=='se' and any(s in {'sat','sat_no_model'} for s in native[r['case']].values()) and not r['all_predicates_instantiated']:
            discrepancy.append({**r,'native_spacer':native[r['case']].get('native_spacer'),
                                'native_eldarica':native[r['case']].get('native_eldarica')})
    if native:
        write_csv(output/'discrepancies.csv',discrepancy,[*identity,'native_spacer','native_eldarica'])
    detailed_statistics(output,rows)
    (output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    return rows,summary


def figures(output):
    os.environ.setdefault('MPLCONFIGDIR',str(output/'matplotlib-cache'))
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.backends.backend_pdf import PdfPages
    rows, summary = tables(output)
    if not rows: return
    destination = output/'figures'; destination.mkdir(exist_ok=True)
    meta = json.loads((output/'metadata.json').read_text())
    settings = json.loads((output/'settings.json').read_text())
    caption = 'Completed' if meta.get('complete') else 'Provisional: completed trials only'
    if meta.get('consolidated'): caption += ' · consolidated diagnostic runs'
    caption += '\n' + budget_caption(settings)
    cats = ['proved','heads_eliminated','instantiated','some_predicates',
            'no_certified_progress','preparation_failed']
    labels = ['Full proof','All heads; residual open','All invariants; heads remain',
              'Some predicates eliminated','No predicate progress','Source preparation failed']
    colors = ['#237a57','#64ac89','#e0b349','#d78b55','#c2c8ce','#875e7f']
    plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,
                         'axes.spines.top':False,'axes.spines.right':False})
    with PdfPages(output/'report.pdf') as pdf:
        for study in sorted({r['study'] for r in rows}):
            configs = [c for c in ['zap_fix','se','se_zap_fix','flex']
                       if any(r['study']==study and r['configuration']==c for r in rows)]
            if not configs: continue
            fig, axes = plt.subplots(1,2,figsize=(12,5.3))
            ax = axes[0]
            for i, config in enumerate(configs):
                group = [r for r in rows if r['study']==study and r['configuration']==config]
                left = 0
                for cat, color, label in zip(cats,colors,labels):
                    n = sum(r['category']==cat for r in group)
                    ax.barh(i,n,left=left,color=color,label=label if i==0 else None)
                    if n: ax.text(left+n/2,i,str(n),ha='center',va='center',fontsize=8)
                    left += n
            ax.set_yticks(range(len(configs)),[LABELS[c] for c in configs]); ax.invert_yaxis()
            ax.set_xlim(0,summary['selected'][study]*1.05)
            ax.set_xlabel('Queries (disjoint outcomes)'); ax.set_title('Coverage')
            ax.legend(loc='upper left',bbox_to_anchor=(-.15,-.20),frameon=False,fontsize=8,ncol=2)
            ax = axes[1]
            for config in configs:
                values = sorted(r['flex_ms']/1000 for r in rows if r['study']==study
                                and r['configuration']==config and r['fully_proved']
                                and r['flex_ms'] is not None)
                if values: ax.step(values,range(1,len(values)+1),where='post',label=LABELS[config])
            ax.set_xlabel('Flex tactic time (seconds)'); ax.set_ylabel('Cumulative full proofs')
            ax.set_title('Proof completion'); ax.grid(alpha=.2); ax.legend(frameon=False)
            fig.suptitle('RQ3'+study+' · coverage and time',fontsize=16)
            fig.text(.5,.025,caption,ha='center',fontsize=8)
            fig.subplots_adjust(left=.12,right=.97,wspace=.4,top=.85,bottom=.30)
            fig.savefig(destination/f'coverage-{study}.pdf'); pdf.savefig(fig); plt.close(fig)
            native = [r for r in rows if r['study']==study and r['configuration'].startswith('native_')]
            if native:
                fig, ax = plt.subplots(figsize=(8,4))
                names = sorted({r['configuration'] for r in native})
                values = [sum(r['native_model_obtained'] for r in native if r['configuration']==c) for c in names]
                ax.barh([LABELS[c] for c in names],values,color='#8193b7')
                for i,n in enumerate(values):ax.text(n+.5,i,str(n),va='center')
                ax.set_xlabel('Original SMT queries with a returned model')
                ax.set_title('Native solver reference · no Lean proof checking')
                fig.tight_layout(); pdf.savefig(fig); plt.close(fig)


def progress(output):
    metadata=json.loads((output/'metadata.json').read_text()) if (output/'metadata.json').exists() else {}
    print('Phase:',metadata.get('phase','preparation'),'complete:',metadata.get('complete',False))
    if metadata.get('phase')=='classification' and (output/'classification.json').exists():
        print('Classified:',len(json.loads((output/'classification.json').read_text())))
    records=read(output)
    print(f'{len(records)}/{metadata.get("planned_runs", "?")} trials')
    for key in sorted({(r['study'],r['configuration']) for r in records}):
        counts=Counter()
        for r in records:
            if (r['study'],r['configuration'])!=key:continue
            final=next((e for e in reversed(r.get('events',[])) if e.get('stage')=='result'),{})
            checked=final.get('kernel_checked') is True
            full=checked and final.get('fully_proved') is True and r['status']=='proved'
            partial=checked and not full and (final.get('all_predicates_instantiated') is True or
                                              (final.get('predicate_count_reduction') or 0)>0)
            category=('proved' if full else 'genuine_partial' if partial else
                      'preparation_failed' if r['status']=='preparation_failed' else
                      r['status'] if key[1].startswith('native_') else 'no_predicate_progress')
            counts[category]+=1
        print('/'.join(key),dict(counts))
    if (output/'active.json').exists():print('Active:',json.loads((output/'active.json').read_text()))


def merge(output, sources):
    """Explicitly overlay later retries, retaining each query's measurement provenance."""
    if output.exists() and any(output.iterdir()):
        raise ValueError('merge output must be new or empty')
    selected, records, source_meta = {}, {}, []
    settings = None
    for source in sources:
        source = source.resolve()
        selection = json.loads((source/'selection.json').read_text())
        current = json.loads((source/'settings.json').read_text())
        if settings is None:settings=current
        for k in ['flex_timeout','combined_timeout','solver_timeout','heartbeats','proof_heartbeats','timeout_policy']:
            if settings.get(k)!=current.get(k):raise ValueError(f'incompatible {k} in {source}')
        for study, cases in selection['cases'].items():
            for case in cases:
                key=study,case['case']
                if key in selected:
                    for field in ['source_sha256','generated_sha256','declaration']:
                        if selected[key].get(field)!=case.get(field):
                            raise ValueError(f'input differs: {key} {field}')
                selected[key]=case
        for record in read(source):
            record={**record,'record_source':str(source/'results.jsonl')}
            records[record['study'],record['case'],record['configuration']]=record
        meta=json.loads((source/'metadata.json').read_text())
        source_meta.append({'path':str(source),'metadata':meta})
    output.mkdir(parents=True,exist_ok=True)
    selection={'cases':{s:[c for (study,_),c in sorted(selected.items()) if study==s] for s in ['a','b']},
               'method':'Overlay of measured runs; later records replace earlier attempts for the same query/configuration.'}
    metadata={'complete':all(s['metadata'].get('complete') for s in source_meta),
              'consolidated':True,'phase':'consolidated','planned_runs':len(records),
              'timing':'Diagnostic measurements from distinct runs; code versions and machine contention may differ.',
              'sources':source_meta}
    for name,data in [('selection.json',selection),('settings.json',settings),('metadata.json',metadata)]:
        (output/name).write_text(json.dumps(data,indent=2)+'\n')
    (output/'results.jsonl').write_text(''.join(json.dumps(r)+'\n' for _,r in sorted(records.items())))


def main(default_figures=True):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('output',type=Path)
    p.add_argument('--progress',action='store_true')
    plotting=p.add_mutually_exclusive_group()
    plotting.add_argument('--tables-only',action='store_true',help='CSV/JSON only')
    plotting.add_argument('--figures',dest='tables_only',action='store_false',help='also generate PDF plots')
    p.set_defaults(tables_only=not default_figures)
    p.add_argument('--merge',nargs='+',type=Path,help='source runs in precedence order; latest record wins')
    a=p.parse_args()
    if a.merge:merge(a.output,a.merge)
    if a.progress:progress(a.output)
    elif a.tables_only:tables(a.output)
    else:figures(a.output)


if __name__=='__main__':
    main()
