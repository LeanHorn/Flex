"""Coverage tables and figures from the frozen RQ3 per-query records."""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import csv
import json
import os
from pathlib import Path
import statistics

LABELS={'zap_fix':'Zap + Fix', 'se':'S/E only', 'flex':'Full Flex',
        'native_spacer':'Spacer (SMT)', 'native_eldarica':'Eldarica (SMT)'}


def read(output):
    p=output/'results.jsonl'
    return [json.loads(l) for l in p.read_text().splitlines()] if p.exists() else []


def budget_caption(settings):
    single = settings['flex_timeout']
    combined = settings.get('combined_timeout', single)
    internal = (f'{single} s internal Flex budget' if single == combined else
                f'{single} s Zap + Fix / S/E only; {combined} s combined')
    return f'{internal} · {settings["solver_timeout"]} s per S/E call · serial trials · one repetition'


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
    category='proved' if proved else 'heads_eliminated' if all_heads else 'instantiated' if all_inst else 'some_predicates' if removed else 'no_certified_progress'
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
    base['solver_ms']=sum(v for k,v in durations.items() if k.endswith('/solver'))
    base['fix_ms']=durations.get('fix',0)
    base['zap_ms']=durations.get('zap',0)
    base['discharge_ms']=durations.get('discharge',0)
    base['kernel_ms']=durations.get('verify/kernel',0)
    return base,[{'study':base['study'],'case':base['case'],'configuration':base['configuration'],
                  'phase':k,'ms':v,'heartbeats':beats[k]} for k,v in durations.items()]


def write_csv(path,rows):
    fields=list(dict.fromkeys(k for r in rows for k in r))
    temporary=path.with_suffix('.tmp')
    with temporary.open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=fields)
        writer.writeheader();writer.writerows(rows)
    temporary.replace(path)


def tables(output):
    selection=json.loads((output/'selection.json').read_text())
    cases={(s,c['case']):c for s,cs in selection['cases'].items() for c in cs}
    cp=output/'classification.json'
    classes={(r['study'],r['case']):r for r in json.loads(cp.read_text())} if cp.exists() else {}
    rows=[];phases=[]
    for record in read(output):
        r,p=row(record,cases,classes);rows.append(r);phases+=p
    write_csv(output/'results.csv',rows);write_csv(output/'phases.csv',phases)
    summary={'selected':{s:len(cs) for s,cs in selection['cases'].items()},'completed_runs':len(rows),
             'by_configuration':{},'structure':{s:dict(Counter(classes.get((s,c['case']),{}).get('kind','unclassified') for c in cs)) for s,cs in selection['cases'].items()}}
    for study in ('a','b'):
        defaults = ['zap_fix','se','flex'] if study=='a' else ['native_spacer','native_eldarica','se']
        observed = sorted({r['configuration'] for r in rows if r['study']==study})
        for config in dict.fromkeys(defaults + observed):
            group=[r for r in rows if r['study']==study and r['configuration']==config]
            timings=[r['flex_ms'] for r in group if r.get('flex_ms') is not None]
            summary['by_configuration'][study+'/'+config]={
                'completed':len(group),'outcomes':dict(Counter(r['status'] for r in group)),
                'categories':dict(Counter(r['category'] for r in group)),
                **{field:sum(bool(r[field]) for r in group) for field in
                   ['model_obtained_attempt','imported_attempt','all_predicates_instantiated','all_heads_eliminated','fully_proved']},
                'native_sat':sum(r['status'] in {'sat','sat_no_model'} for r in group),
                'native_models':sum(r['native_model_obtained'] for r in group),
                'median_flex_ms_all_terminal':statistics.median(timings) if timings else None}
    native={c['case']:{} for c in selection['cases']['b']}
    for r in rows:
        if r['configuration'].startswith('native_'):native[r['case']][r['configuration']]=r['status']
    summary['native_union']={'paired_completed':sum(len(v)==2 for v in native.values()),
                             'either_sat_observed':sum(any(s in {'sat','sat_no_model'} for s in v.values()) for v in native.values())}
    discrepancy=[]
    for r in rows:
        if r['study']=='b' and r['configuration']=='se' and any(s in {'sat','sat_no_model'} for s in native[r['case']].values()) and not r['all_predicates_instantiated']:
            discrepancy.append({**r,'native_spacer':native[r['case']].get('native_spacer'),
                                'native_eldarica':native[r['case']].get('native_eldarica')})
    write_csv(output/'discrepancies.csv',discrepancy)
    (output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    return rows,summary


def figures(output):
    os.environ.setdefault('MPLCONFIGDIR',str(output/'matplotlib-cache'))
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.backends.backend_pdf import PdfPages
    rows,summary=tables(output)
    if not rows:return
    figures=output/'figures';figures.mkdir(exist_ok=True)
    plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'axes.spines.top':False,'axes.spines.right':False})
    meta=json.loads((output/'metadata.json').read_text())
    settings=json.loads((output/'settings.json').read_text())
    caption='Completed pilot' if meta.get('complete') else 'RUNNING — provisional results; pending trials excluded'
    colors=['#237a57','#64ac89','#e0b349','#d78b55','#c2c8ce']
    cats=['proved','heads_eliminated','instantiated','some_predicates','no_certified_progress']
    labels=['Full proof','All predicates + heads','All predicates; heads remain/unknown','Some predicates','No certified predicate progress']
    with PdfPages(output/'pilot-report.pdf') as pdf:
        fig,axes=plt.subplots(1,2,figsize=(12,5.4),gridspec_kw={'width_ratios':[1.2,1]})
        ax=axes[0]
        for i,config in enumerate(['zap_fix','se','flex']):
            group=[r for r in rows if r['study']=='a' and r['configuration']==config]
            left=0
            for cat,color,label in zip(cats,colors,labels):
                n=sum(r['category']==cat for r in group)
                ax.barh(i,n,left=left,color=color,label=label if i==0 else None)
                if n:ax.text(left+n/2,i,str(n),ha='center',va='center',fontsize=9)
                left+=n
            ax.text(left+1,i,f'{len(group)}/{summary["selected"]["a"]}',va='center',fontsize=8)
        ax.set_yticks(range(3),['Zap + Fix','S/E only','Full Flex']);ax.invert_yaxis()
        ax.set_xlim(0,summary['selected']['a']+18);ax.set_xlabel('Queries (exclusive outcome categories)')
        ax.set_title('RQ3a · verifier-generated CHCs')
        ax.legend(loc='lower left',bbox_to_anchor=(-.25,-.62),frameon=False,fontsize=9)
        ax=axes[1]
        sg=summary['by_configuration'];b=[r for r in rows if r['study']=='b' and r['configuration']=='se']
        names=['Spacer (original SMT)','Eldarica (original SMT)','Either (original SMT)',
               'S/E: model returned','S/E: predicates imported','S/E: all predicates retained','S/E: all heads eliminated','S/E: full Lean proof']
        values=[sg['b/native_spacer']['native_sat'],sg['b/native_eldarica']['native_sat'],summary['native_union']['either_sat_observed'],
                sum(r['model_obtained_attempt'] for r in b),sum(r['imported_attempt'] for r in b),
                sum(r['all_predicates_instantiated'] for r in b),sum(r['all_heads_eliminated'] for r in b),sum(r['fully_proved'] for r in b)]
        ax.barh(range(len(names)),values,color=['#8193b7']*3+['#c2c8ce']*2+['#e0b349','#64ac89','#237a57'])
        for i,n in enumerate(values):ax.text(n+.7,i,str(n),va='center')
        ax.set_yticks(range(len(names)),names,fontsize=9);ax.invert_yaxis();ax.set_xlim(0,summary['selected']['b']+12)
        ax.set_xlabel('Queries (cumulative milestones)');ax.set_title('RQ3b · CHC-COMP')
        fig.suptitle('RQ3 coverage pilot',fontsize=17)
        fig.text(.5,.015,caption+'\n'+budget_caption(settings),ha='center',fontsize=9)
        fig.subplots_adjust(left=.12,right=.97,wspace=.75,top=.85,bottom=.34)
        fig.savefig(figures/'coverage.pdf');fig.savefig(figures/'coverage.png',dpi=170);pdf.savefig(fig);plt.close(fig)
        fig,axes=plt.subplots(1,2,figsize=(11.7,5.2))
        for ax,study in zip(axes,('a','b')):
            configs=['zap_fix','se','flex'] if study=='a' else ['se']
            for config in configs:
                values=sorted(r['flex_ms']/1000 for r in rows if r['study']==study and r['configuration']==config and r['fully_proved'] and r['flex_ms'] is not None)
                if values:ax.step(values,range(1,len(values)+1),where='post',label=LABELS[config])
            ax.set_xlabel('Flex tactic time (seconds)');ax.set_ylabel('Cumulative full proofs');ax.grid(alpha=.2)
            ax.set_title('RQ3'+study+' · proof completion');ax.legend(frameon=False)
        fig.suptitle('Timing and input structure',fontsize=17)
        structures=' | '.join('RQ3'+s+': '+', '.join(f'{k.replace("_"," ")} {v}' for k,v in counts.items()) for s,counts in summary['structure'].items())
        fig.text(.5,.03,caption+'\n'+structures,ha='center',fontsize=8,wrap=True)
        fig.tight_layout(rect=(0,.12,1,.9));fig.savefig(figures/'timing.pdf');pdf.savefig(fig);plt.close(fig)
        fig,axes=plt.subplots(1,2,figsize=(11.7,5.2))
        for ax,study,config in [(axes[0],'a','flex'),(axes[1],'b','se')]:
            group=[r for r in rows if r['study']==study and r['configuration']==config]
            for level,(cat,color) in enumerate(zip(cats,colors)):
                xs=[r['input_bytes'] for r in group if r['category']==cat]
                ax.scatter(xs,[4-level]*len(xs),color=color,alpha=.7,s=22)
            ax.set_xscale('log');ax.set_xlabel('Input size (bytes, logarithmic scale)')
            ax.set_yticks(range(5),['No predicate progress','Some predicates','All predicates','All heads','Full proof'],fontsize=8)
            ax.set_title('RQ3'+study+' · '+LABELS[config]);ax.grid(alpha=.18)
        fig.suptitle('Progress versus input size',fontsize=17)
        fig.text(.5,.02,'Size uses original Flux VC / generated LiquidHaskell Lean / original CHC-COMP SMT; compare within each family.\n'+caption,ha='center',fontsize=8)
        fig.tight_layout(rect=(0,.12,1,.9));fig.savefig(figures/'size-coverage.pdf');pdf.savefig(fig);plt.close(fig)


def progress(output):
    metadata=json.loads((output/'metadata.json').read_text()) if (output/'metadata.json').exists() else {}
    print('Phase:',metadata.get('phase','preparation'),'complete:',metadata.get('complete',False))
    if metadata.get('phase')=='classification' and (output/'classification.json').exists():
        print('Classified:',len(json.loads((output/'classification.json').read_text())))
    if (output/'summary.json').exists():
        summary=json.loads((output/'summary.json').read_text())
        print(f'{summary["completed_runs"]}/{metadata.get("planned_runs",600)} trials')
        for key,row in summary['by_configuration'].items():
            if not row['completed']:continue
            print(key, 'completed=',row['completed'],'all predicates=',row['all_predicates_instantiated'],
                  'heads=',row['all_heads_eliminated'],'proved=',row['fully_proved'],'outcomes=',row['outcomes'])
    if (output/'active.json').exists():print('Active:',json.loads((output/'active.json').read_text()))


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('output',type=Path);p.add_argument('--progress',action='store_true')
    a=p.parse_args();progress(a.output) if a.progress else figures(a.output)
