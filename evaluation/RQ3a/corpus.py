"""Prepare statement-only inputs from a flex-benchmarks checkout."""
from __future__ import annotations

from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import random
import re
import subprocess
import tarfile
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'scripts'))
from rq1_corpus import imports, strip_comments


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def tracked(repo):
    """Committed files; outside a git checkout (an archive), every file outside hidden folders."""
    try:
        return subprocess.check_output(['git', '-C', str(repo), 'ls-files'], text=True,
                                       stderr=subprocess.DEVNULL).splitlines()
    except (OSError, subprocess.CalledProcessError):
        return sorted(str(p.relative_to(repo)) for p in Path(repo).rglob('*') if p.is_file()
                      and not any(part.startswith('.') for part in p.relative_to(repo).parts))


def git_revision(repo):
    try:
        return subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True,
                                       stderr=subprocess.DEVNULL).strip()
    except (OSError, subprocess.CalledProcessError):
        return None


def flatten(path, repo):
    """Inline only local source dependencies; never load existing VC proofs."""
    seen, chunks, external, dependencies = set(), [], [], []

    def visit(p):
        if p in seen:
            return
        seen.add(p)
        text = strip_comments(p.read_text())
        if re.search(r'\b(sorry|admit|axiom)\b', text):
            raise ValueError(f'unproved source specification: {p.relative_to(repo)}')
        dependencies.append({'path': str(p.relative_to(repo)), 'sha256': sha(p)})
        for module in imports(text):
            relative = Path(*module.split('.')).with_suffix('.lean')
            local = next((parent / relative for parent in p.parents
                          if parent.is_relative_to(repo) and (parent / relative).is_file()), None)
            if local:
                if '/Proof/' in str(local):
                    raise ValueError(f'proof dependency forbidden: {local}')
                visit(local)
            elif module.split('.')[0] in {'Lean', 'Std', 'Init', 'Mathlib', 'Flex', 'Aesop', 'Smt', 'Auto'}:
                if module not in external:
                    external.append(module)
            else:
                raise ValueError(f'unresolved local import {module} in {p}')
        text = re.sub(r'^import\s+.*\n', '', text, flags=re.M)
        chunks.append(f'-- Source: {p.relative_to(repo)}\n{text}\n')

    visit(path)
    return ''.join(f'import {m}\n' for m in external) + '\n'.join(chunks), dependencies


def inventory_a(repo):
    cases = []
    for relative in tracked(repo):
        if not relative.startswith(('flux_tests/', 'flux-medium/', 'wave/')):
            continue
        if '/VC/' not in relative or not relative.endswith('.lean'):
            continue
        path = repo / relative
        text = path.read_text()
        predicates = len(re.findall(r'∃\s+k\d+\s*:', text))
        if not predicates:
            continue
        names = re.findall(r'^def\s+([^\s:(]+)\s*(?::=|:)', text, re.M)
        if len(names) != 1:
            raise ValueError(f'expected one generated VC in {relative}: {names}')
        cases.append({'case': relative, 'suite': relative.split('/')[0],
                      'family': relative.split('/')[0], 'repo_path': relative,
                      'source_sha256': sha(path), 'bytes': path.stat().st_size,
                      'predicates_static': predicates, 'declaration': 'F.' + names[0],
                      'format': 'lean_statement'})
    lf = repo / 'liquid-fixpoint'
    data = json.loads((lf / 'manifest.json').read_text())
    for item in data['cases']:
        path = lf / item['lean']
        if sha(path) != item['lean_sha256'] or sha(lf / item['source']) != item['source_sha256']:
            raise ValueError(f'Liquid Fixpoint hash mismatch: {item["case"]}')
        cases.append({'case': 'liquid-fixpoint/' + item['case'] + '.lean', 'suite': 'liquid-fixpoint',
                      'family': str(Path(item['case']).parent),
                      'repo_path': str(path.relative_to(repo)),
                      'upstream_source': 'liquid-fixpoint/' + item['source'],
                      'source_sha256': item['source_sha256'], 'bytes': path.stat().st_size,
                      'predicates_static': item['predicates'],
                      'declaration': item['declaration'], 'format': 'lean_statement'})
    return cases


def unpack_chc(repo, output):
    root = repo / 'CHC-COMP'
    target = output / 'corpus' / 'CHC-COMP'
    target.mkdir(parents=True, exist_ok=True)
    manifest = json.loads((root / 'manifest.json').read_text())
    for item in manifest['archives']:
        archive = root / item['path']
        if sha(archive) != item['sha256']:
            raise ValueError(f'archive hash mismatch: {archive}')
        with tarfile.open(archive) as tar:
            for member in tar:
                p = Path(member.name)
                if not member.isfile() or p.is_absolute() or '..' in p.parts:
                    raise ValueError(f'unsafe archive member {member.name}')
                if p.parts[0] not in {'generated', 'sources'}:
                    raise ValueError(f'unexpected archive member {member.name}')
                dest = target / p
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_bytes(tar.extractfile(member).read())
    return target


def inventory_b(repo, output):
    root = unpack_chc(repo, output)
    selected = json.loads((repo / 'CHC-COMP/selection.json').read_text())['inputs']
    translations = {}
    for path in (root / 'generated').glob('*-manifest.json'):
        data = json.loads(path.read_text())
        for item in data['files']:
            translations[data['project'] + '/' + item['input']] = (data, item)
    cases = []
    for entry in selected:
        source = root / 'sources' / entry['source_relative_path']
        data, item = translations[entry['source_relative_path']]
        generated = root / 'generated' / Path(entry['source_relative_path']).with_suffix('.lean')
        if sha(source) != entry['sha256'] or sha(generated) != item['output_sha256']:
            raise ValueError(f'CHC-COMP hash mismatch: {source}')
        case = {'case': entry['source_relative_path'].removesuffix('.smt2') + '.lean',
                'suite': entry['suite'], 'family': entry['source_relative_path'].split('/')[0],
                'track': entry['track'], 'source': str(source), 'generated': str(generated),
                'source_sha256': entry['sha256'], 'generated_sha256': sha(generated),
                'bytes': source.stat().st_size, 'namespace': item['namespace'],
                'queries': item['queries'], 'inventory_status': 'translated',
                'aliases': [entry['source_relative_path']]}
        cases.append(case)
    return cases


def balanced(cases, count, seed, rotate_sizes=False):
    """Round-robin source families and within-family size quartiles, then seeded draws."""
    if count >= len(cases):
        return sorted(cases, key=lambda x: x['case'])
    rng = random.Random(seed)
    families = defaultdict(list)
    for case in sorted(cases, key=lambda x: (x['bytes'], x['case'])):
        families[case['suite'] if case['suite'] != 'liquid-fixpoint' else case['family']].append(case)
    groups = {}
    for family, entries in families.items():
        buckets = defaultdict(list)
        for i, case in enumerate(entries):
            bucket = min(3, i * 4 // len(entries))
            case['size_quartile'] = bucket + 1
            buckets[bucket].append(case)
        for values in buckets.values():
            rng.shuffle(values)
        keys = sorted(buckets)
        # Small CHC-COMP pilots must also sample the largest quartile.
        if rotate_sizes:
            offset = len(groups) % len(keys)
            keys = keys[offset:] + keys[:offset]
        queue = []
        while any(buckets.values()):
            for key in keys:
                if buckets[key]:
                    queue.append(buckets[key].pop())
        groups[family] = queue
    names = sorted(groups)
    rng.shuffle(names)
    result = []
    while len(result) < count:
        for name in names:
            if groups[name] and len(result) < count:
                result.append(groups[name].pop(0))
    return result


def select(cases, study, count, seed):
    if count == 0:
        return sorted(cases, key=lambda x: x['case'])
    if study == 'b':
        return balanced(cases, count, seed, rotate_sizes=True)
    # Half Liquid Fixpoint; the other half includes all three Flux/Wave suites.
    lh = count // 2
    flux = count - lh
    quotas = {'flux_tests': round(flux * .60), 'flux-medium': round(flux * .24)}
    quotas['wave'] = flux - sum(quotas.values())
    quotas['liquid-fixpoint'] = lh
    result = []
    for i, (suite, n) in enumerate(quotas.items()):
        pool = [c for c in cases if c['suite'] == suite]
        if len(pool) < n:
            raise ValueError(f'only {len(pool)} cases in {suite}, requested {n}')
        result += balanced(pool, n, seed + i)
    return result


def prepare_a(cases, repo, output):
    root = output / 'corpus' / 'statements'
    root.mkdir(parents=True, exist_ok=True)
    for i, case in enumerate(cases):
        original = repo / case['repo_path']
        try:
            text, dependencies = flatten(original, repo)
            modules = imports(text)
            body = re.sub(r'^import .*\n', '', text, flags=re.M)
            text = ''.join(f'import {m}\n' for m in modules) + body
            target = root / f'{i:03}.lean'
            target.write_text(text)
            case.update(generated=str(target), generated_sha256=sha(target),
                        source=str(original), dependencies=dependencies, inventory_status='translated')
        except (ValueError, OSError) as error:
            case.update(source=str(original), inventory_status='preparation_failed',
                        preparation_error=str(error))
    return cases


def build(repo, output, count, seed, study='both'):
    a = inventory_a(repo) if study in ('a', 'both') else []
    b = inventory_b(repo, output) if study in ('b', 'both') else []
    chosen = {'a': select(a, 'a', count, seed) if a else [],
              'b': select(b, 'b', count, seed) if b else []}
    prepare_a(chosen['a'], repo, output)
    return {'seed': seed, 'benchmarks_commit': git_revision(repo),
            'pool_counts': {'a': dict(Counter(c['suite'] for c in a)),
                            'b_tasks': len(b)},
            'method': ('Full published corpus when count=0. RQ3b pilots round-robin suites '
                       'and rotate within-suite size quartiles; RQ3a pilots split equally '
                       'between Flux-Wave and Liquid Fixpoint. Seeded draws within strata. '
                       'No outcome filtering or SMT-content deduplication.'),
            'cases': chosen}
