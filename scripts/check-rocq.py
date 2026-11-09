#!/usr/bin/env python3
"""Compile Kattis specs, implementations and proofs in an isolated temporary build."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('problems', nargs='*', help='Problem slugs; defaults to all problems')
    parser.add_argument('--jobs', type=int, default=4)
    parser.add_argument('--lib', type=Path, default=ROOT.parent / 'kattis-private' / 'lib')
    parser.add_argument('--flocq', type=Path, help='Optional built Flocq tree (containing Core/)')
    parser.add_argument('--complexity', type=Path, default=ROOT.parent / 'rocq-speck/_build/default/vendor/complexity',
                        help='Compiled rocq-speck Complexity library (needed by complexity specs)')
    args = parser.parse_args()
    slugs = args.problems or sorted(p.parent.name for p in ROOT.glob('*/*.spec'))
    for slug in slugs:
        if not (ROOT / slug / (slug + '.spec')).is_file():
            parser.error(f'Unknown problem: {slug}')
    if args.jobs < 1:
        parser.error('--jobs must be positive')
    flags = ['-R', str(args.flocq.resolve()), 'Flocq'] if args.flocq else []

    needs_cost = any('Complexity ' in (ROOT / slug / (slug + '.spec')).read_text() for slug in slugs)
    if needs_cost:
        if not (args.complexity / 'Speck.vo').is_file():
            parser.error('Build the rocq-speck Complexity library, or pass its compiled directory with --complexity')
        flags += ['-Q', str(args.complexity.resolve()), 'Complexity']

    def run(command, cwd):
        result = subprocess.run(command, cwd=cwd, text=True, capture_output=True)
        if result.returncode:
            raise RuntimeError(' '.join(command) + '\n' + result.stdout + result.stderr)
        return result.stdout

    with tempfile.TemporaryDirectory(prefix='kattis-rocq-') as tmp:
        build = Path(tmp)
        lib = build / 'lib'
        lib.mkdir()
        lib_flags = ['-Q', str(lib), 'Respeced']
        for name in ['Repr', 'ZBig', 'ReprFloat']:
            shutil.copy2(args.lib / (name + '.v'), lib)
            run(['rocq', 'compile', *flags, *lib_flags, name + '.v'], lib)

        if needs_cost:
            shutil.copy2(ROOT / 'lib/Cost.v', lib)
            run(['rocq', 'compile', *flags, *lib_flags, 'Cost.v'], lib)

        def check(slug):
            dest = build / slug
            generated = dest / 'generated'
            generated.mkdir(parents=True)
            spec = ROOT / slug / (slug + '.spec')
            (generated / 'Prelude.v').write_text(run(['rocq-speck', 'dump-spec', '--prelude', str(spec)], dest))
            for suffix in ['implem', 'proofs']:
                shutil.copy2(ROOT / slug / f'{slug}_{suffix}.v', dest)
            namespace = ['-Q', str(dest), 'Cold'] if slug == 'cold' else []
            command = ['rocq', 'compile', *flags, *lib_flags, *namespace, '-Q', str(generated), 'Speck']
            for file in [generated / 'Prelude.v', dest / f'{slug}_implem.v', dest / f'{slug}_proofs.v']:
                run([*command, str(file)], dest)
            return slug

        failures = []
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            pending = {pool.submit(check, slug): slug for slug in slugs}
            for job in as_completed(pending):
                slug = pending[job]
                try:
                    job.result()
                    print(f'{slug}: OK', flush=True)
                except Exception as error:
                    failures.append(slug)
                    print(f'{slug}: FAILED\n{error}', flush=True)
        print(f'{len(slugs) - len(failures)}/{len(slugs)} problems compiled successfully.')
        return bool(failures)


if __name__ == '__main__':
    raise SystemExit(main())
