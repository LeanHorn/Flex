#!/usr/bin/env python3
"""Reproduce the paper appendix for 391 CHCs retained from the completed local pilot.

Usage: python3 evaluation/Scraping/paper_appendix.py --results RUN --output DIR
Outputs a LaTeX subsection with numeric tables and a JSON summary.
Use --graph for a standalone cumulative-coverage plot (NumPy, SciPy, Matplotlib).
"""
from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
import statistics


CONFIGS = ('bank', 'basic', 'standard', 'deep', 'auto')
LABELS = ('Bank', 'Basic', 'Standard', 'Deep', 'Incremental')
CORPORA = (('refinement', 'Refinement-typechecker'), ('chc-comp', 'CHC-COMP'),
           ('rq1', 'RQ1 case studies'))


def read_csv(path):
    with path.open() as handle:
        return list(csv.DictReader(handle))


def fully_proved(row):
    return row['fully_proved'] == 'True' and row['kernel_checked'] == 'True'


def percentile(values, p):
    ordered = sorted(values)
    rank = (len(ordered) - 1) * p
    low = math.floor(rank)
    high = math.ceil(rank)
    return ordered[low] + (ordered[high] - ordered[low]) * (rank - low)


def describe(values):
    return dict(n=len(values), mean=statistics.mean(values),
                p25=percentile(values, .25), median=statistics.median(values),
                p75=percentile(values, .75), p90=percentile(values, .90), max=max(values))


def coverage_graph(by_config, n, output, compact=False):
    """Plot visual interpolations; retain every empirical event in a separate CSV."""
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    import numpy as np
    from scipy.interpolate import PchipInterpolator

    colors = ('#74777C', '#3579B1', '#C87900', '#8A61A8', '#007C70')
    styles = ((0, (3, 2)), (0, (7, 2)), (0, (4, 1.5, 1, 1.5)),
              (0, (10, 2)), 'solid')
    plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 9,
                         'axes.labelsize': 10, 'pdf.fonttype': 42,
                         'ps.fonttype': 42, 'axes.linewidth': .6})
    if compact:
        plt.rcParams.update({'font.size': 8, 'axes.labelsize': 8.5})
    fig, ax = plt.subplots(figsize=(3.22, 2.55) if compact else (6.8, 3.6))
    fig.subplots_adjust(left=.16, right=.98, bottom=.20, top=.79) if compact else \
        fig.subplots_adjust(left=.105, right=.77, bottom=.17, top=.95)
    events, anchors, diagnostics = [], [], {}
    for config, label, color, style in zip(CONFIGS, LABELS, colors, styles):
        times = np.sort([float(r['flex_ms']) / 1000
                         for r in by_config[config] if fully_proved(r)])
        assert len(times) and np.all(times > 0)
        empirical_times = np.unique(times)
        empirical_counts = np.searchsorted(times, empirical_times, side='right')
        events.extend((config, float(t), int(count))
                      for t, count in zip(empirical_times, empirical_counts))

        # Nearest-rank anchors at 5% intervals, plus exact time thresholds.
        ranks = sorted({1, len(times), *(math.ceil(j * len(times) / 20)
                                        for j in range(1, 20))})
        knots = np.unique([*(times[rank - 1] for rank in ranks),
                           *(t for t in (1., 10., 30., 50.)
                             if times[0] < t < times[-1])])
        counts = np.searchsorted(times, knots, side='right')
        curve = PchipInterpolator(np.log10(knots), counts, extrapolate=False)
        grid = np.unique(np.r_[np.geomspace(times[0], times[-1], 1200), knots])
        heights = curve(np.log10(grid))
        assert np.all(np.diff(heights) >= -1e-9)
        assert heights.min() >= counts[0] - 1e-9
        assert abs(heights[-1] - len(times)) < 1e-9
        assert np.allclose(curve(np.log10(knots)), counts)
        anchors.extend((config, float(t), int(count)) for t, count in zip(knots, counts))

        # The curve begins at the first observed proof and never rises before it.
        ax.plot(np.r_[grid, 120.], np.r_[heights, len(times)], color=color,
                linestyle=style, linewidth=(1.5 if config == 'auto' else 1.1) if compact else
                (1.85 if config == 'auto' else 1.5), label=label,
                solid_capstyle='round', dash_capstyle='round',
                zorder=4 if config == 'auto' else 3)
        ax.plot(times[-1], len(times), 'o', color=color, markersize=3, zorder=5)
        if not compact:
            ax.annotate(f'{label}  {len(times)}', (120., len(times)), xytext=(7, 0),
                        textcoords='offset points', va='center', color=color,
                        fontsize=9, fontweight='bold' if config == 'auto' else 'normal',
                        annotation_clip=False)
        # Report visual-interpolation error; these coordinates are not new trials.
        probe = np.unique(np.r_[np.geomspace(times[0], times[-1], 10000),
                                empirical_times, np.nextafter(empirical_times[1:], 0)])
        errors = np.abs(curve(np.log10(probe)) -
                        np.searchsorted(times, probe, side='right'))
        diagnostics[config] = dict(proved=len(times), first_proof_seconds=float(times[0]),
                                   last_proof_seconds=float(times[-1]), anchors=len(knots),
                                   sampled_max_interpolation_error_chcs=float(np.max(errors)))

    ax.set_xscale('log')
    ax.set_xlim(.05, 120.)
    ax.set_ylim(0, n + 18)
    ax.set_xticks([.1, 1, 10, 100], ['0.1', '1', '10', '100'])
    ax.set_yticks([0, 100, 200, 300, n])
    ax.set_xlabel('Tactic time per CHC (s, log scale)', labelpad=6 if compact else 8)
    ax.set_ylabel('Fully proved CHCs', labelpad=7)
    if compact:
        ax.legend(loc='lower left', bbox_to_anchor=(-.15, 1.06), ncol=3, frameon=False,
                  borderaxespad=0, handlelength=1.7, columnspacing=.8,
                  handletextpad=.4, fontsize=7.5)
    ax.set_axisbelow(True)
    ax.grid(axis='y', color='#D8DADD', linewidth=.55)
    ax.tick_params(which='major', length=3, color='#70757A', labelcolor='#34383C')
    ax.tick_params(which='minor', bottom=False)
    for side in ('top', 'right'):
        ax.spines[side].set_visible(False)
    for side in ('left', 'bottom'):
        ax.spines[side].set_color('#B2B5B8')
    figures = output / 'figures'
    figures.mkdir(exist_ok=True)
    stem = figures / ('scraping-coverage-compact' if compact else 'scraping-coverage')
    fig.savefig(stem.with_suffix('.pdf'), bbox_inches=None if compact else 'tight', pad_inches=.08)
    fig.savefig(stem.with_suffix('.png'), dpi=240, bbox_inches=None if compact else 'tight', pad_inches=.08)
    plt.close(fig)
    for name, data in [('empirical', events), ('anchors', anchors)]:
        with (output / f'scraping-coverage-{name}.csv').open('w', newline='') as handle:
            writer = csv.writer(handle)
            writer.writerow(['configuration', 'tactic_time_seconds', 'fully_proved'])
            writer.writerows(data)
    (output / 'scraping-coverage-plot.json').write_text(json.dumps(
        dict(selected_chcs=n, interpolation='monotone PCHIP in log10 time',
             anchors='nearest-rank 5% intervals, observed endpoints, 1/10/30/50 seconds',
             configurations=diagnostics), indent=2) + '\n')
    (output / 'scraping-coverage-caption.txt').write_text(
        f'Cumulative kernel-checked full proofs on {n} selected CHCs. '
        'Lines are monotone visual interpolations between empirical anchors; '
        'dots mark the last observed proof and labels give exact final counts. '
        'Tactic times exclude process startup, imports, and final kernel checking.\n')


def candidate_summary_graph(metrics, n, output, compact=False):
    """A common linear count axis makes typical and large pools directly comparable."""
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt

    plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 10,
                         'axes.labelsize': 10, 'pdf.fonttype': 42, 'ps.fonttype': 42})
    if compact:
        plt.rcParams.update({'font.size': 8, 'axes.labelsize': 8.5})
    fig, ax = plt.subplots(figsize=(3.22, 2.55) if compact else (6.8, 3.6))
    fig.subplots_adjust(left=.25, right=.98, bottom=.20, top=.79) if compact else \
        fig.subplots_adjust(left=.18, right=.975, bottom=.18, top=.84)
    for index, config in enumerate(CONFIGS):
        for offset, key, color, label in (
            (-.17, 'median', '#3579B1', 'Median'),
            (.17, 'p90', '#007C70', '90th percentile')):
            value = metrics[config][key]
            ax.barh(index + offset, value, height=.28, color=color,
                    label=label if index == 0 else None, zorder=3)
            ax.text(value + 23, index + offset, f'{value:,.0f}', va='center',
                    ha='left', fontsize=7.3 if compact else 9, color='#34383C')
    ax.set_yticks(range(len(CONFIGS)), LABELS)
    ax.invert_yaxis()
    ax.set_xlim(0, 2350 if compact else 2000)
    ax.set_xticks([0, 1000, 2000] if compact else [0, 500, 1000, 1500, 2000],
                 ['0', '1,000', '2,000'] if compact else ['0', '500', '1,000', '1,500', '2,000'])
    ax.set_xlabel('Peak instantiated candidates' if compact else
                  'Peak instantiated candidates per CHC', labelpad=6 if compact else 9)
    ax.legend(loc='lower left', bbox_to_anchor=(-.25, 1.06) if compact else (0, 1.035), ncol=2,
              frameon=False, borderaxespad=0, handlelength=1.5, columnspacing=2)
    ax.set_axisbelow(True)
    ax.grid(axis='x', color='#E3E5E7', linewidth=.6)
    ax.tick_params(axis='y', length=0, pad=8)
    ax.tick_params(axis='x', length=3, color='#A1A5A9', labelcolor='#34383C')
    for side in ('top', 'right', 'left'):
        ax.spines[side].set_visible(False)
    ax.spines['bottom'].set_color('#B2B5B8')
    stem = output / 'figures' / ('scraping-candidates-summary-compact' if compact
                                 else 'scraping-candidates-summary')
    stem.parent.mkdir(exist_ok=True)
    fig.savefig(stem.with_suffix('.pdf'), bbox_inches=None if compact else 'tight', pad_inches=.08)
    fig.savefig(stem.with_suffix('.png'), dpi=240, bbox_inches=None if compact else 'tight', pad_inches=.08)
    plt.close(fig)
    with (output / 'scraping-candidates-summary.csv').open('w', newline='') as handle:
        writer = csv.writer(handle)
        writer.writerow(['configuration', 'chcs', 'median_peak_candidates', 'p90_peak_candidates'])
        writer.writerows((config, n, metrics[config]['median'], metrics[config]['p90'])
                         for config in CONFIGS)
    (output / 'scraping-candidates-summary-caption.txt').write_text(
        f'Median and 90th-percentile peak instantiated candidate counts across all {n} selected CHCs, '
        'including unsuccessful runs. Each count is the largest initial PA-stage pool observed for a CHC, '
        'summed over predicates; repeated stages are not summed. Percentiles use linear interpolation.\n')


def candidate_graph(by_config, n, output, template_counts=None):
    """Compare observed pools on a common population, preserving zeros and failures."""
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    import numpy as np
    from scipy.interpolate import PchipInterpolator

    colors = ('#74777C', '#3579B1', '#C87900', '#8A61A8', '#007C70')
    styles = ((0, (3, 2)), (0, (7, 2)), (0, (4, 1.5, 1, 1.5)),
              (0, (10, 2)), 'solid')
    plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 9,
                         'axes.labelsize': 10, 'pdf.fonttype': 42,
                         'ps.fonttype': 42, 'axes.linewidth': .6})
    fig, ax = plt.subplots(figsize=(6.8, 3.7))
    fig.subplots_adjust(left=.11, right=.975, bottom=.17, top=.85)
    templates = template_counts is not None
    name = 'scraping-templates' if templates else 'scraping-candidates'
    measure = ('maximum scraped qualifier templates reported by any visited PA stage'
               if templates else 'maximum observed initial PA-stage pool, summed across predicates')
    percentiles = np.linspace(0., 100., n)
    grid = np.unique(np.r_[np.linspace(0., 100., 1601), percentiles])
    observations, anchors, metrics = [], [], {}
    for config, label, color, style in zip(CONFIGS, LABELS, colors, styles):
        def count(row):
            return (template_counts[(row['case'], config)] if templates
                    else int(row['max_stage_initial_candidates']))
        records = sorted(by_config[config], key=lambda r: (count(r), r['case']))
        counts = np.array([count(r) for r in records])
        assert len(counts) == n and np.all(counts >= 0)
        # Interpolate every order statistic, retaining ties, plateaus, and tails.
        curve = PchipInterpolator(percentiles, np.log1p(counts))
        heights = np.expm1(curve(grid))
        assert np.all(np.diff(heights) >= -1e-8)
        assert np.allclose(np.expm1(curve(percentiles)), counts)
        assert abs(heights[0] - counts[0]) < 1e-8
        assert abs(heights[-1] - counts[-1]) < 1e-8
        ax.plot(grid, heights, color=color, linestyle=style, label=label,
                linewidth=1.9 if config == 'auto' else 1.5,
                solid_capstyle='round', dash_capstyle='round')
        for p in (50., 90.):
            ax.plot(p, percentile(counts.tolist(), p / 100), 'o',
                    markersize=3, color=color, zorder=5)
        observations.extend((config, rank, 100 * (rank - 1) / (n - 1),
                             r['case'], count(r), fully_proved(r))
                            for rank, r in enumerate(records, 1))
        anchors.extend((config, float(p), int(v)) for p, v in zip(percentiles, counts))
        metrics[config] = dict(n=n, zero_counts=int(sum(counts == 0)),
                              mean=float(np.mean(counts)), median=float(np.median(counts)),
                              p90=percentile(counts.tolist(), .9), maximum=int(counts[-1]),
                              at_most_500=int(sum(counts <= 500)))

    if not templates:
        candidate_summary_graph(metrics, n, output)

    # Explicit zero tick; raw candidate counts remain the tick labels.
    ax.set_yscale('function', functions=(np.log1p, np.expm1))
    ax.set_ylim(0, 80 if templates else 6500)
    ax.set_yticks([0, 1, 5, 10, 20, 50] if templates else [0, 10, 100, 1000, 5000],
                 ['0', '1', '5', '10', '20', '50'] if templates else ['0', '10', '100', '1,000', '5,000'])
    ax.set_xlim(0, 100)
    ax.set_xticks([0, 25, 50, 75, 90, 100])
    ax.set_xlabel('CHCs ranked within each configuration (%)', labelpad=8)
    ax.set_ylabel('Peak scraped qualifier templates' if templates else
                  'Peak instantiated candidates', labelpad=8)
    ax.text(0, 1.025, 'log(1 + count) scale', transform=ax.transAxes,
            fontsize=8, color='#555A60')
    ax.legend(loc='lower left', bbox_to_anchor=(0, 1.10), ncol=5, frameon=False,
              borderaxespad=0, handlelength=2.6, columnspacing=1.05, handletextpad=.5)
    ax.set_axisbelow(True)
    ax.grid(axis='y', color='#D8DADD', linewidth=.55)
    for p in (50, 90):
        ax.axvline(p, color='#D8DADD', linewidth=.55, zorder=0)
    ax.tick_params(length=3, color='#70757A', labelcolor='#34383C')
    for side in ('top', 'right'):
        ax.spines[side].set_visible(False)
    for side in ('left', 'bottom'):
        ax.spines[side].set_color('#B2B5B8')
    figures = output / 'figures'
    figures.mkdir(exist_ok=True)
    stem = figures / name
    fig.savefig(stem.with_suffix('.pdf'), bbox_inches='tight', pad_inches=.08)
    fig.savefig(stem.with_suffix('.png'), dpi=240, bbox_inches='tight', pad_inches=.08)
    plt.close(fig)
    for name, columns, data in (
        ('observations', ['configuration', 'rank', 'percentile', 'case', 'peak_count', 'fully_proved'], observations),
        ('anchors', ['configuration', 'percentile', 'peak_count'], anchors)):
        with (output / f'{stem.name}-{name}.csv').open('w', newline='') as handle:
            writer = csv.writer(handle)
            writer.writerow(columns)
            writer.writerows(data)
    (output / f'{stem.name}-metrics.json').write_text(json.dumps(
        dict(selected_chcs=n, population='all outcomes including unsuccessful runs',
             measure=measure,
             interpolation='monotone PCHIP in log(1 + count) through every empirical order statistic',
             configurations=metrics), indent=2) + '\n')
    detail = ('Counts are the maximum scraped-template count reported by a visited stage; '
              'they exclude the 19 built-in templates and separately generated position-specific candidates. '
              if templates else
              'Counts are the largest observed initial PA-stage pool, summed over predicates, not scraped '
              'templates or the sum of reused pools across stages. ')
    (output / f'{stem.name}-caption.txt').write_text(
        f'{"Scraped qualifier templates" if templates else "Instantiated candidate pools"} over {n} selected CHCs, '
        'including unsuccessful runs. '
        'Each configuration is sorted separately; matching percentiles need not denote the same CHC. '
        'Curves interpolate all sorted observations monotonically; dots mark the median and 90th percentile. '
        + detail + 'The log(1 + count) axis retains zeros.\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--results', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--graph', action='store_true',
                        help='also produce a smooth coverage PDF/PNG and empirical CSVs')
    parser.add_argument('--candidate-graph', action='store_true',
                        help='also produce standalone candidate/template-distribution PDFs/PNGs and CSVs')
    parser.add_argument('--rq4-panels', action='store_true',
                        help='produce compact coverage and candidate plots for side-by-side placement')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    source_rows = read_csv(args.results / 'ablation_results.csv')
    included_corpora = {corpus for corpus, _ in CORPORA}
    rows = [r for r in source_rows if r['corpus'] in included_corpora]
    selected_cases = {r['case'] for r in rows}
    stages = [s for s in read_csv(args.results / 'scraping_stages.csv')
              if s['case'] in selected_cases]
    by_config = {c: [r for r in rows if r['configuration'] == c] for c in CONFIGS}
    cases = {r['case'] for r in by_config['auto']}
    n = len(cases)
    assert n == 391, 'This appendix describes the 391 cases in the retained paper suites.'
    assert len(rows) == n * len(CONFIGS)
    assert len({(r['case'], r['configuration']) for r in rows}) == len(rows)
    assert all({r['case'] for r in by_config[c]} == cases for c in CONFIGS)
    assert all(fully_proved(r) for r in by_config['auto']), 'Expected the selected pilot population.'
    assert all(r['max_stage_initial_candidates'] for r in rows)
    assert all(r['flex_ms'] for r in rows if fully_proved(r))

    if args.graph:
        coverage_graph(by_config, n, args.output)
    if args.rq4_panels:
        coverage_graph(by_config, n, args.output, compact=True)
        candidate_summary_graph(
            {c: describe([int(r['max_stage_initial_candidates']) for r in by_config[c]])
             for c in CONFIGS}, n, args.output, compact=True)
    if args.candidate_graph:
        candidate_graph(by_config, n, args.output)
        template_counts = {}
        for s in stages:
            key = s['case'], s['configuration']
            assert s['scraped_templates']
            template_counts[key] = max(template_counts.get(key, 0), int(s['scraped_templates']))
        assert len(template_counts) == n * len(CONFIGS)
        candidate_graph(by_config, n, args.output, template_counts)

    auto_stages = [s for s in stages if s['configuration'] == 'auto']
    retained = [s for s in auto_stages if s['retained'] == 'True']
    assert len(retained) == n and len({s['case'] for s in retained}) == n
    assert all(s['accepted'] == 'True' and s['remaining_heads'] == '0' for s in retained)
    reached = {c: sum(s['mode'] == c for s in auto_stages) for c in CONFIGS[:-1]}
    stopped = {c: sum(s['mode'] == c for s in retained) for c in CONFIGS[:-1]}
    timing = {}
    pools = {}
    for c in CONFIGS:
        timing[c] = {
            'returned': describe([float(r['flex_ms']) / 1000 for r in by_config[c] if r['flex_ms']]),
            'proved': describe([float(r['flex_ms']) / 1000 for r in by_config[c] if fully_proved(r)]),
        }
        pools[c] = [int(r['max_stage_initial_candidates']) for r in by_config[c]]
    lookup = {(r['case'], r['configuration']): r for r in rows}
    paired = {}
    for c in CONFIGS[:-1]:
        shared = [r for r in by_config[c] if fully_proved(r)]
        paired[c] = math.exp(statistics.mean(
            math.log(float(r['flex_ms']) / float(lookup[r['case'], 'auto']['flex_ms'])) for r in shared))

    coverage_rows = []
    for corpus, label in CORPORA:
        count = sum(r['corpus'] == corpus for r in by_config['auto'])
        counts = [sum(r['corpus'] == corpus and fully_proved(r) for r in by_config[c]) for c in CONFIGS]
        coverage_rows.append(' & '.join([label, str(count), *map(str, counts)]) + r' \\')
    counts = [sum(map(fully_proved, by_config[c])) for c in CONFIGS]
    assert counts == [285, 305, 333, 362, 391], 'Update the pilot discussion for changed results.'
    assert list(reached.values()) == [391, 106, 84, 32]
    assert list(stopped.values()) == [285, 22, 52, 32]
    coverage_rows += [r'\midrule', ' & '.join([r'\textbf{Total}', rf'\textbf{{{n}}}',
                       *[rf'\textbf{{{x}}}' for x in counts]]) + r' \\']
    timing_rows = []
    for c, label in zip(CONFIGS, LABELS):
        d = timing[c]['proved']
        timing_rows.append(' & '.join([label, str(d['n']), *[f"{d[k]:.2f}" for k in
                           ('mean', 'p25', 'median', 'p75', 'p90', 'max')]]) + r' \\')
    stage_rows = []
    for c, label in zip(CONFIGS[:-1], LABELS[:-1]):
        stage_rows.append(f'{label} & {stopped[c]} & {100 * stopped[c] / n:.1f}' + r'\% \\')
    stage_rows += [r'\midrule', rf'\textbf{{Total}} & \textbf{{{n}}} & \textbf{{100\%}} \\']

    thresholds = (1, 10, 120)
    threshold_counts = {
        c: [sum(fully_proved(r) and float(r['flex_ms']) / 1000 <= limit
                for r in by_config[c]) for limit in thresholds]
        for c in CONFIGS
    }

    template = r'''% Data: evaluation/results/Scraping/ablation406-20261112.
% Numeric summaries are reproduced by Flex/evaluation/Scraping/paper_appendix.py.
\clearpage
\subsection{RQ4 Scraping Results}
\label{app:scraping-ablation}

The @@N@@ CHCs comprise @@CYCLIC@@ cyclic-only and @@MIXED@@ mixed constraints.
We ran each CHC once per configuration, serially on macOS 26.2
(10 CPUs, 24\,GiB RAM). Tactic times exclude startup, imports,
and final kernel checking. Power was AC at the start and battery at the end.

\begin{table}[htbp]
\centering\small
\setlength{\tabcolsep}{4pt}
\begin{tabular}{@{}lr*{5}{r}@{}}
\toprule
Corpus & CHCs & Bank & Basic & Standard & Deep & Incremental \\
\midrule
@@COVERAGE@@
\bottomrule
\end{tabular}
\caption{Fully proved CHCs by scraping configuration.}
\label{tab:scraping-coverage}
\end{table}

\begin{table}[htbp]
\centering\small
\setlength{\tabcolsep}{4pt}
\begin{tabular}{@{}lr*{6}{r}@{}}
\toprule
Configuration & $n$ & Mean & P25 & Median & P75 & P90 & Max \\
\midrule
@@TIMING@@
\bottomrule
\end{tabular}
\caption{Tactic time in seconds over fully proved CHCs ($n$).
Quantiles use linear interpolation.}
\label{tab:scraping-times}
\end{table}

\begin{table}[htbp]
\centering\small
\setlength{\tabcolsep}{12pt}
\begin{tabular}{@{}lrr@{}}
\toprule
Level & CHCs & Share of @@N@@ \\
\midrule
@@STAGES@@
\bottomrule
\end{tabular}
\caption{First level where Incremental accepted an invariant.}
\label{tab:scraping-escalation}
\end{table}

One Standard and three Deep runs hit the 300\,s process watchdog.
Standard and Deep each eliminate all predicates in three further CHCs
but leave residual proof obligations.
'''
    inferred = {c: sum(r['all_predicates_instantiated'] == 'True' and
                       r['kernel_checked'] == 'True' for r in by_config[c]) for c in CONFIGS}
    bank_lost = sum(fully_proved(r) and not fully_proved(lookup[r['case'], 'deep'])
                    for r in by_config['bank'])
    replacements = {'@@N@@': str(n), '@@TRIALS@@': f'{len(rows):,}',
                    '@@CYCLIC@@': str(sum(r['structure'] == 'cyclic_only' for r in by_config['auto'])),
                    '@@MIXED@@': str(sum(r['structure'] == 'mixed' for r in by_config['auto'])),
                    '@@BANK_LOST@@': str(bank_lost),
                    '@@COVERAGE@@': '\n'.join(coverage_rows),
                    '@@STAGES@@': '\n'.join(stage_rows),
                    '@@TIMING@@': '\n'.join(timing_rows)}
    for key, value in replacements.items():
        template = template.replace(key, value)
    assert '@@' not in template
    sections = args.output / 'sections'
    sections.mkdir(exist_ok=True)
    (sections / 'scraping-ablation.tex').write_text(template)
    (args.output / 'scraping-appendix-metrics.json').write_text(json.dumps(
        dict(selected=n, included_corpora=sorted(included_corpora),
             source_cases=len({r['case'] for r in source_rows}),
             source_trials=len(source_rows), retained_trials=len(rows),
             all_predicates_instantiated=inferred, fully_proved=dict(zip(CONFIGS, counts)), timing=timing,
             candidate_pools={c: describe(pools[c]) for c in CONFIGS},
             reached=reached, stopped=stopped, paired_time_ratios=paired,
             time_thresholds_seconds=thresholds, proved_within_thresholds=threshold_counts), indent=2) + '\n')
    print(f'Generated appendix for {n} CHCs / {len(rows)} trials in {args.output}')


if __name__ == '__main__':
    main()
