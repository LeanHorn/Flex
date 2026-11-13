#!/usr/bin/env python3
"""Package measured RQ4 data for sharing; never run Lean or alter the measurements."""
import argparse
import csv
import gzip
import hashlib
import io
import json
from pathlib import Path
import tarfile

import report


def load(path):
    return json.loads(path.read_text())


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def archive(path, entries):
    with tarfile.open(path, 'w:gz') as tar:
        for name, data in entries:
            info = tarfile.TarInfo(name)
            info.size, info.mode, info.mtime = len(data), 0o644, 0
            tar.addfile(info, io.BytesIO(data))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--results', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    src, dst = args.results.resolve(), args.output.resolve()
    if dst.exists() and any(dst.iterdir()):
        parser.error('output must be empty; previous measurements are never overwritten')
    dst.mkdir(parents=True, exist_ok=True)
    original = load(src / 'selection.json')
    cases = [c for cs in original['cases'].values() for c in cs if c.get('corpus') in {'rq1', 'refinement', 'chc-comp'}]
    ids = {c['case'] for c in cases}
    manifest = load(Path(__file__).with_name('selection.json'))
    portable = [c for c in manifest['cases'] if c['case'] in ids]
    if {c['case'] for c in portable} != ids:
        raise ValueError('run contains inputs outside the RQ4 paper selection')
    write_json(dst / 'selection.json', {'method': manifest['method'], 'cases': {'scraping': portable},
                                      'screening_provenance': manifest['screening_provenance']})
    rows = [r for r in (json.loads(line) for line in (src / 'results.jsonl').read_text().splitlines())
            if r['case'] in ids]
    keys = {(r['case'], r['configuration']) for r in rows}
    if len(rows) != len(keys) or keys != {(c, cfg) for c in ids for cfg in report.CONFIGS}:
        raise ValueError('export requires exactly one completed trial per selected case and configuration')
    with gzip.open(dst / 'results.jsonl.gz', 'wt') as handle:
        for row in rows:
            handle.write(json.dumps(row) + '\n')
    detailed = []
    for path in sorted(src.glob('*.csv')):
        with path.open() as handle:
            reader = csv.DictReader(handle)
            if not reader.fieldnames or 'case' not in reader.fieldnames:
                continue  # Recompute aggregates, rather than copying ones that include removed inputs.
            selected = [r for r in reader if r['case'] in ids]
            buffer = io.StringIO(newline='')
            writer = csv.DictWriter(buffer, fieldnames=reader.fieldnames)
            writer.writeheader()
            writer.writerows(selected)
        data = buffer.getvalue().encode()
        if path.name in {'ablation_results.csv', 'scraping_stages.csv'}:
            (dst / path.name).write_bytes(data)
        else:
            detailed.append((path.name, data))
    archive(dst / 'detailed-metrics.tar.gz', detailed)

    def artifacts():
        for row in rows:
            directory = src / row['artifacts']
            for name in ('lean.log', 'events.jsonl', 'phases.jsonl', 'invocation.json',
                         'classification.json', 'input_metrics.json', 'resource.json', 'residual.txt'):
                path = directory / name
                if path.is_file():
                    yield str(path.relative_to(src)), path.read_bytes()
    archive(dst / 'trial-artifacts.tar.gz', artifacts())
    archive(dst / 'runtime-source.tar.gz', ((str(p.relative_to(src)), p.read_bytes())
            for p in sorted((src / 'source').rglob('*')) if p.is_file() and '__pycache__' not in p.parts))
    # Preserve the exact measured original inputs, independent of future benchmark edits.
    archive(dst / 'inputs.tar.gz', ((f'corpus/{field}/{i:03}{Path(c[field]).suffix}', Path(c[field]).read_bytes())
            for i, c in enumerate(cases) for field in ('source', 'generated')))
    write_json(dst / 'provenance.json', {
        'schema_version': 1, 'source_run': src.name, 'selected_chcs': len(ids),
        'exported_trials': len(rows), 'excluded_corpus': 'imp',
        'metadata': load(src / 'metadata.json'), 'settings': load(src / 'settings.json'),
        'runtime_checks': load(src / 'runtime_checks.json'),
        'runtime_dependencies': load(src / 'runtime.json'),
        'note': 'Original metadata describes the original run, before removing Imp. Raw selected trials '
                'are unchanged. Aggregates are recomputed for this export only. Absolute paths are '
                'historical provenance, not prerequisites. Frozen source is authoritative if the '
                'recorded Git revision did not include then-uncommitted instrumentation.'})
    report.summarize(dst, dst / 'summary')
    write_json(dst / 'checksums.json', {str(p.relative_to(dst)): hashlib.sha256(p.read_bytes()).hexdigest()
                for p in sorted(dst.rglob('*')) if p.is_file()})
    print(f'Exported {len(ids)} cases / {len(rows)} trials to {dst}')


if __name__ == '__main__':
    main()
