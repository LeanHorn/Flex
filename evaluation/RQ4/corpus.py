"""Reconstruct the fixed RQ4 inputs from flex-benchmarks; verify every source hash."""
from collections import Counter
import importlib.util
import json
from pathlib import Path
import shutil

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('rq4_shared_corpus', ROOT / 'evaluation/RQ3a/corpus.py')
shared = importlib.util.module_from_spec(spec)
spec.loader.exec_module(shared)


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def prepare(args):
    manifest = json.loads(args.manifest.read_text())
    cases = manifest['cases']
    if len({c['case'] for c in cases}) != len(cases):
        raise ValueError('duplicate case IDs in RQ4 selection')
    if any(c['corpus'] not in {'rq1', 'refinement', 'chc-comp'} for c in cases):
        raise ValueError('unexpected corpus in RQ4 selection')
    if args.smoke:
        selected = set(manifest['smoke_cases'])
        cases = [c for c in cases if c['case'] in selected]
        if len(cases) != 3 or {c['corpus'] for c in cases} != {'rq1', 'refinement', 'chc-comp'}:
            raise ValueError('smoke selection must contain one real query from each corpus')
    extracted = shared.unpack_chc(args.benchmarks, args.output)
    for i, case in enumerate(cases):
        if case['corpus'] == 'chc-comp':
            source = extracted / 'sources' / Path(case['case']).with_suffix('.smt2')
            generated = extracted / 'generated' / case['case']
            text = generated.read_text()
        else:
            source = args.benchmarks / case['repo_path']
            text, dependencies = shared.flatten(source, args.benchmarks)
            if dependencies != case['dependencies']:
                raise ValueError(f'changed specification dependencies: {case["case"]}')
        generated = args.output / 'corpus/generated' / f'{i:03}.lean'
        generated.parent.mkdir(parents=True, exist_ok=True)
        generated.write_text(text)
        if shared.sha(generated) != case['generated_sha256'] or shared.sha(source) != case['source_sha256']:
            raise ValueError(f'input hash mismatch: {case["case"]}; use the recorded benchmark revision')
        frozen_source = args.output / 'corpus/source' / f'{i:03}{source.suffix}'
        frozen_source.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, frozen_source)
        case.update(source=str(frozen_source), generated=str(generated), inventory_status='translated')
    # Only the selected inputs are needed after verification, not the extracted whole corpus.
    shutil.rmtree(extracted)
    selection = {'method': manifest['method'], 'cases': {'scraping': cases},
                 'benchmarks_commit': shared.git_revision(args.benchmarks),
                 'screening_provenance': manifest['screening_provenance']}
    save(args.output / 'selection.json', selection)
    save(args.output / 'manifest.json', {'method': manifest['method'], 'cases': cases, 'complete': True})
    save(args.output / 'selection_details.json', {
        'selected': len(cases), 'corpora': dict(Counter(c['corpus'] for c in cases)),
        'structures': dict(Counter(c['structure'] for c in cases)), 'smoke': args.smoke,
        'inputs_identical_to_local_run': True})
    return selection
