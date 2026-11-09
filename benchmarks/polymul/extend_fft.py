#!/usr/bin/env python3
"""Extend FFT measurements to the Kattis bound, stopping at the first failed size."""
from pathlib import Path
import csv,datetime,hashlib,json,shutil,subprocess,tempfile,statistics
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
sizes=[24576,32768,49152,65536,98304,131072]
metadata=json.loads((HERE/'metadata.json').read_text())
sources=[ROOT/'polymul2/extraction/ocaml/marray.ml', ROOT/'polymul2/extraction/ocaml/polymul2_extracted_marray.ml']
for src in sources:
    key=str(src.relative_to(ROOT))
    if src.name=='marray.ml':key='polymul1/extraction/ocaml/marray.ml'
    assert hashlib.sha256(src.read_bytes()).hexdigest()==metadata['sources_sha256'][key], 'Extraction changed since baseline'
report={'date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'max_coefficients_per_input':131072,
        'max_degree_per_input':131071,'timeout_seconds_per_size':120,'sizes':[],
        'harness_sha256':hashlib.sha256((HERE/'bench_fft_large.ml').read_bytes()).hexdigest(),
        'validation':'Each trial checks 35 coefficient positions by exact convolution, four modular polynomial identities over two primes, all coefficient magnitudes, result length, and input immutability.'}
with tempfile.TemporaryDirectory(prefix='polymul-fft-large-') as tmp:
    build=Path(tmp)
    for p in [*sources,HERE/'bench_fft_large.ml']:shutil.copy2(p,build/p.name)
    subprocess.run(['ocamlfind','ocamlopt','-O3','-package','rocq-runtime.kernel,unix','-linkpkg',
                    'marray.ml',sources[1].name,'bench_fft_large.ml','-o','fft-benchmark'],cwd=build,check=True)
    with (HERE/'fft-large.csv').open('w') as out:
        out.write('coefficients_per_input,total_coefficients,degree_per_input,trial,algorithm,repetitions,seconds_per_call\n')
        for n in sizes:
            partial=build/'trial.csv'
            try:
                subprocess.run([str(build/'fft-benchmark'),str(n),str(partial)],check=True,capture_output=True,text=True,timeout=120)
                rows=list(csv.reader(partial.open()))
                assert len(rows)==7
            except (subprocess.TimeoutExpired,subprocess.CalledProcessError,AssertionError) as exc:
                reason='120-second per-size timeout' if isinstance(exc,subprocess.TimeoutExpired) else (getattr(exc,'stderr','') or str(exc))
                report['sizes'].append({'coefficients_per_input':n,'status':'stopped','reason':reason})
                print(f'Stopped at {n}: {reason}',flush=True)
                break
            out.write(partial.read_text());out.flush()
            med=statistics.median(float(x[6]) for x in rows)
            report['sizes'].append({'coefficients_per_input':n,'degree':n-1,'status':'measured','median_seconds':med})
            (HERE/'fft-extension.json').write_text(json.dumps(report,indent=2)+'\n')
            print(f'{n:,} coefficients per input (degree {n-1:,}): {med:.4f} seconds; 7 trials validated',flush=True)
(HERE/'fft-extension.json').write_text(json.dumps(report,indent=2)+'\n')
