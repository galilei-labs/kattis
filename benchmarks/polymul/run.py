#!/usr/bin/env python3
"""Build unchanged extractions and benchmark locally; invoke inside the Rocq opam switch."""
from pathlib import Path
import datetime, hashlib, json, platform, shutil, subprocess, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
def output(*args):
    return subprocess.check_output(args, text=True).strip()
sources = [ROOT/'polymul1/extraction/ocaml/marray.ml',
           ROOT/'polymul1/extraction/ocaml/polymul1_extracted_marray.ml',
           ROOT/'polymul2/extraction/ocaml/polymul2_extracted_marray.ml']
assert sources[0].read_bytes() == (ROOT/'polymul2/extraction/ocaml/marray.ml').read_bytes()
metadata = {
    'date_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'machine': output('sysctl', '-n', 'machdep.cpu.brand_string'),
    'memory_bytes': int(output('sysctl', '-n', 'hw.memsize')),
    'os': platform.platform(), 'ocaml_version': output('ocamlopt','-version'),
    'ocaml_config': output('ocamlopt','-config'),
    'runtime_package': output('ocamlfind','query','rocq-runtime.kernel'),
    'compiler_flags': ['-O3'], 'seed': 20261109, 'trials_per_size': 7,
    'coefficients': 'Uniform integers in [-3,3]; zero leading coefficients replaced by 1',
    'timing': 'Wall time per call; adaptive batches targeting >=30 ms (capped at 4096 calls); full major GC before each batch; alternate algorithm order',
    'included': 'Function evaluation, result allocation, FFT planning/twiddles, and GC during the batch',
    'excluded': 'Input generation, correctness checks, calibration, GC before the batch, compilation, and I/O',
    'validation': 'Every trial compares all output coefficients; sizes <=256 also checked against independent integer convolution; input immutability checked',
    'harness_sha256': hashlib.sha256((HERE/'bench.ml').read_bytes()).hexdigest(),
    'backend': 'Upstream mutable-array Marray extraction; this backend is not a verified extraction',
    'scope': 'Sizes >256 coefficients per input exceed polymul1 specification bounds; timings there are empirical extrapolation',
    'sources_sha256': {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
}
with tempfile.TemporaryDirectory(prefix='polymul-bench-') as tmp:
    build = Path(tmp)
    for p in [*sources, HERE/'bench.ml']: shutil.copy2(p, build/p.name)
    subprocess.run(['ocamlfind','ocamlopt','-O3','-package','rocq-runtime.kernel,unix','-linkpkg',
                    'marray.ml',sources[1].name,sources[2].name,'bench.ml','-o','benchmark'], cwd=build,check=True)
    subprocess.run([str(build/'benchmark'),str(HERE/'raw.csv')],check=True)
(HERE/'metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
