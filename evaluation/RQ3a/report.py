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

LABELS={'zap_fix':'Zap + Fix', 'se':'S/E only', 'flex':'Full Flex',
        'native_spacer':'Spacer (SMT)', 'native_eldarica':'Eldarica (SMT)'}


def read(output):
    p=output/'results.jsonl'
    return [json.loads(l) for l in p.read_text().splitlines(keepends=True)
            if l.endswith('\n') and l.strip()] if p.exists() else []


def budget_caption(settings):
    single = settings['flex_timeout']
    combined = settings.get('combined_timeout', single)
    internal = (f'{single} s internal Flex budget' if single == combined else
                f'{single} s Zap + Fix / S/E only; {combined} s combined')
    return f'{internal} · {settings["solver_timeout"]} s per S/E call · {settings.get("workers", 1)} worker(s)'


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


def row(record, cases, classes):
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
    phases=[]
    path=Path(record.get('artifacts',''))/'phases.jsonl'
    if path.is_file():
        phases=[json.loads(l) for l in path.read_text().splitlines()]
    starts=defaultdict(list); durations=defaultdict(float); beats=defaultdict(float)
    for e in phases:
        if e['status']=='start':
            starts[e['phase']].append(e)
        elif starts[e['phase']]:
            start=starts[e['phase']].pop()
            durations[e['phase']]+=e.get('elapsed_ms',0)
            beats[e['phase']]+=(e.get('heartbeats_raw',0)-start.get('heartbeats_raw',0))/1000
    base={'study':record['study'],'case':record['case'],'suite':case['suite'],
          'configuration':record['configuration'],'status':record['status'],'category':category,
          'structure':classes.get(key,{}).get('kind','unclassified'),'input_bytes':case['bytes'],
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
          **terminal.get('proof_metrics',{})}
    if record['status']=='preparation_failed':base['wall_ms']=None
    base['predicate_progress'] = category in {'proved','heads_eliminated','instantiated','some_predicates'}
    base['genuine_partial_progress'] = base['predicate_progress'] and not proved
    base['solver_calls'] = sum(e['stage']=='chc/solver' for e in events)
    base['record_source'] = record.get('record_source')
    base['solver_ms']=sum(v for k,v in durations.items() if k.endswith('/solver'))
    base['fix_ms']=durations.get('fix',0)
    base['zap_ms']=durations.get('zap',0)
    base['discharge_ms']=durations.get('discharge',0)
    base['kernel_ms']=durations.get('verify/kernel',0)
    if not phases:
        for key in ['solver_ms','fix_ms','zap_ms','discharge_ms','kernel_ms']:base[key]=None
    base['tactic_time_measured'] = base['flex_ms'] is not None
    base['external_timeout'] = record['status'] in {'case_timeout','process_timeout'}
    return base,[{'study':base['study'],'case':base['case'],'configuration':base['configuration'],
                  'phase':k,'ms':v,'heartbeats':beats[k]} for k,v in durations.items()]


def write_csv(path,rows):
    fields=list(dict.fromkeys(k for r in rows for k in r))
    temporary=path.with_suffix('.tmp')
    with temporary.open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=fields)
        writer.writeheader();writer.writerows(rows)
    temporary.replace(path)


def detailed_statistics(output, rows):
    metrics = ['flex_ms','wall_ms','startup_ms','zap_ms','fix_ms','solver_ms',
               'discharge_ms','kernel_ms','tactic_heartbeats','total_heartbeats',
               'proof_nodes','proof_depth','solver_calls']
    stats, comparisons = [], []
    for study, config in sorted({(r['study'],r['configuration']) for r in rows}):
        group = [r for r in rows if (r['study'],r['configuration'])==(study,config)]
        for suite in ['ALL'] + sorted({r['suite'] for r in group}):
            selected = [r for r in group if suite=='ALL' or r['suite']==suite]
            for population in ['all_measured','proved','not_proved']:
                subset = [r for r in selected if population=='all_measured' or
                          r['fully_proved']==(population=='proved')]
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
    write_csv(output/'statistics.csv',stats)
    write_csv(output/'comparisons.csv',comparisons)


def tables(output):
    selection=json.loads((output/'selection.json').read_text())
    cases={(s,c['case']):c for s,cs in selection['cases'].items() for c in cs}
    cp=output/'classification.json'
    classes={(r['study'],r['case']):r for r in json.loads(cp.read_text())} if cp.exists() else {}
    rows=[];phases=[]
    for record in read(output):
        r,p=row(record,cases,classes);rows.append(r);phases+=p
    write_csv(output/'results.csv',rows);write_csv(output/'phases.csv',phases)
    selected={s:cs for s,cs in selection['cases'].items() if cs}
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
                                 'either_sat_observed':sum(any(s in {'sat','sat_no_model'} for s in v.values()) for v in native.values())}
    discrepancy=[]
    for r in rows:
        if r['study']=='b' and r['configuration']=='se' and any(s in {'sat','sat_no_model'} for s in native[r['case']].values()) and not r['all_predicates_instantiated']:
            discrepancy.append({**r,'native_spacer':native[r['case']].get('native_spacer'),
                                'native_eldarica':native[r['case']].get('native_eldarica')})
    if native:
        write_csv(output/'discrepancies.csv',discrepancy)
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
            configs = [c for c in ['zap_fix','se','flex']
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
        for k in ['flex_timeout','combined_timeout','solver_timeout','heartbeats','proof_heartbeats']:
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


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('output',type=Path)
    p.add_argument('--progress',action='store_true')
    p.add_argument('--tables-only',action='store_true')
    p.add_argument('--merge',nargs='+',type=Path,help='source runs in precedence order; latest record wins')
    a=p.parse_args()
    if a.merge:merge(a.output,a.merge)
    if a.progress:progress(a.output)
    elif a.tables_only:tables(a.output)
    else:figures(a.output)
