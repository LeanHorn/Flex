#!/usr/bin/env python3
"""Summarize RQ4 measurements without rerunning Lean or assuming particular outcomes."""
from __future__ import annotations

import argparse
import csv
import importlib.util
import itertools
import json
import math
from pathlib import Path
import statistics

HERE = Path(__file__).resolve().parent
CONFIGS = ('bank', 'basic', 'standard', 'deep', 'auto')
LABELS = dict(zip(CONFIGS, ('Bank', 'Basic', 'Standard', 'Deep', 'Incremental')))


def read(path):
    with path.open() as handle:
        return list(csv.DictReader(handle))


def proved(row):
    return row['fully_proved'] == 'True' and row['kernel_checked'] == 'True'


def describe(values):
    values = sorted(values)
    result = dict.fromkeys(('mean', 'p25', 'median', 'p75', 'p90', 'p95', 'max'))
    if values:
        def percentile(p):
            i = (len(values) - 1) * p
            return values[math.floor(i)] + (values[math.ceil(i)] - values[math.floor(i)]) * (i % 1)
        result.update(mean=statistics.mean(values), p25=percentile(.25), median=percentile(.5),
                      p75=percentile(.75), p90=percentile(.9), p95=percentile(.95), max=max(values))
    return {'n': len(values), **result}


def write_csv(path, rows):
    with path.open('w', newline='') as handle:
        fields = list(dict.fromkeys(k for row in rows for k in row))
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


def summarize(results, output, figures=False):
    selection = json.loads((results / 'selection.json').read_text())
    cases = {c['case'] for cs in selection['cases'].values() for c in cs}
    rows = read(results / 'ablation_results.csv')
    keys = [(r['case'], r['configuration']) for r in rows]
    expected = {(case, mode) for case in cases for mode in CONFIGS}
    if len(set(keys)) != len(keys) or not set(keys) <= expected:
        raise ValueError('duplicate or unscheduled RQ4 results')
    output.mkdir(parents=True, exist_ok=True)
    groups = {mode: [r for r in rows if r['configuration'] == mode] for mode in CONFIGS}
    coverage, timings, candidates = [], [], []
    for mode, group in groups.items():
        successes = [r for r in group if proved(r)]
        coverage.append({'configuration': mode, 'selected': len(cases), 'completed': len(group),
                         'fully_proved': len(successes), 'percent_of_selected': 100 * len(successes) / len(cases),
                         'all_predicates_instantiated': sum(r['all_predicates_instantiated'] == 'True' for r in group),
                         'all_heads_eliminated': sum(r['all_heads_eliminated'] == 'True' for r in group)})
        for population, subset in [('fully_proved', successes), ('all_measured', group)]:
            for metric in ('flex_ms', 'wall_ms', 'stage_zap_ms', 'stage_fix_ms',
                           'scrape_ms', 'synthesis_ms', 'certificate_ms', 'discharge_ms'):
                values = [float(r[metric]) / 1000 for r in subset if r.get(metric)]
                timings.append({'configuration': mode, 'population': population, 'metric': metric,
                                'unit': 'seconds', 'population_n': len(subset), **describe(values)})
        for metric in ('max_stage_initial_candidates', 'max_stage_surviving_candidates', 'pa_rounds'):
            candidates.append({'configuration': mode, 'metric': metric, 'population_n': len(group),
                               **describe([float(r[metric]) for r in group if r.get(metric)])})
    lookup = {key: row for key, row in zip(keys, rows)}
    paired = []
    for first, second in itertools.combinations(CONFIGS, 2):
        matches = [(lookup[c, first], lookup[c, second]) for c in sorted(cases)
                   if (c, first) in lookup and (c, second) in lookup
                   and proved(lookup[c, first]) and proved(lookup[c, second])]
        ratios = [float(a['flex_ms']) / float(b['flex_ms']) for a, b in matches
                  if a.get('flex_ms') and b.get('flex_ms') and float(a['flex_ms']) > 0 and float(b['flex_ms']) > 0]
        paired.append({'first': first, 'second': second, 'jointly_proved': len(matches),
                       'timed_pairs': len(ratios), 'geomean_first_over_second':
                       math.exp(statistics.mean(map(math.log, ratios))) if ratios else None})
    summary = {'selected_chcs': len(cases), 'completed_trials': len(rows),
               'complete': set(keys) == expected, 'coverage': coverage, 'timing': timings,
               'candidates': candidates, 'paired_tactic_time': paired,
               'note': 'Fixed population selected using earlier Incremental successes. Fresh failures stay '
                       'in the denominator. Missing metrics are null, not zero. Timings are in seconds; '
                       'quantiles use linear interpolation; paired ratios use jointly proved queries only.'}
    for name, values in [('coverage', coverage), ('times', timings), ('candidates', candidates), ('paired', paired)]:
        write_csv(output / f'{name}.csv', values)
    (output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    if figures:
        if any(proved(r) and (not r.get('flex_ms') or float(r['flex_ms']) <= 0) for r in rows):
            raise ValueError('numeric summaries saved; coverage figure requires a positive tactic time for every full proof')
        spec = importlib.util.spec_from_file_location('rq4_plot', HERE.parent / 'Scraping/paper_appendix.py')
        plot = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(plot)
        plot.coverage_graph(groups, len(cases), output, compact=True)
        pools = {r['configuration']: r for r in candidates if r['metric'] == 'max_stage_initial_candidates'}
        if all(v['n'] for v in pools.values()):
            plot.candidate_summary_graph(pools, len(cases), output, compact=True)
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--results', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--figures', action='store_true')
    parser.add_argument('--rebuild', action='store_true', help='re-extract detailed CSVs from raw events and logs')
    args = parser.parse_args()
    if args.rebuild:
        spec = importlib.util.spec_from_file_location('rq4_details', HERE.parent / 'Scraping/report.py')
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        module.summarize(args.results, figures=False)
    summary = summarize(args.results, args.output or args.results / 'rq4-summary', args.figures)
    print(f'{summary["completed_trials"]}/{summary["selected_chcs"] * 5} trials; complete={summary["complete"]}')
    for c in summary['coverage']:
        print(f'{LABELS[c["configuration"]]}: {c["fully_proved"]}/{c["selected"]} fully proved')


if __name__ == '__main__':
    main()
