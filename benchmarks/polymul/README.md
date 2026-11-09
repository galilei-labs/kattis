# Extracted OCaml polynomial multiplication benchmark

Compares the unchanged `polymul1` schoolbook extraction and `polymul2` split-coefficient FFT extraction using their identical upstream `Marray` runtime.

## Reproduce

From the Kattis repository, on macOS with the `rocq-9.2` opam switch:

```sh
opam exec --switch=rocq-9.2 -- python3 benchmarks/polymul/run.py
uv run --with matplotlib python benchmarks/polymul/plot.py
```

`run.py` builds a native OCaml executable in a temporary directory. It does not modify the extracted sources. `metadata.json` records the compiler configuration, machine, source hashes, seed, and measurement method. `plot.py` records the plotting version.

## Method

- Equal-size polynomial inputs, from 16 to 16,384 coefficients **per input**. The chart's horizontal axis is the **total** coefficient count `n`, twice this number. Each input polynomial has degree `n/2 - 1`.
- Seven deterministic random input pairs per size. Coefficients are integers in `[-3, 3]`; zero leading coefficients are replaced by one. Products fit within signed 32-bit integers throughout this experiment.
- Each trial compares every output coefficient between both algorithms and checks that neither input was modified. At sizes up to 256 coefficients per input, outputs are also checked against an independent integer convolution. All 126 pairs matched.
- Native compilation with `ocamlopt -O3`, using the same runtime and compiler flags for both algorithms. No changes to the extracted functions.
- Adaptive batches target at least 30 ms, with a cap of 4,096 calls. The smallest schoolbook batches hit that cap and are shorter. Trials alternate algorithm order and run a full major collection before the timed batch.
- Wall time includes allocation, FFT twiddle-table construction, computation, and garbage collection during execution. It excludes input generation, validation, compilation, calibration, and the collection before each batch. Returned results are retained through `Sys.opaque_identity` to prevent elimination.
- Curves are measured medians; shading is the interquartile range of seven trial averages, not a confidence interval. FFT stair steps reflect power-of-two padding.

## Scope

Polymul1's specification allows at most 256 coefficients per input; measurements beyond this size exceed this bound and is an empirical extrapolation of the same executable. All tested FFT sizes are within polymul2's input-length bound. No specification bounds were modified for the benchmark.

These are the upstream **mutable-array extractions**, whose backend is not verified. Agreement on test inputs does not establish extraction correctness. The measurements describe these binaries, this machine, and balanced inputs with the recorded coefficient distribution.

## Files

- `polymul-benchmark.png`, `.svg`, `.pdf`: the graph, including its methodology notes.
- `raw.csv`: every trial's timing and batch size.
- `summary.csv`: medians, quartiles, and speedups.
- `metadata.json`: hardware, compiler, hashes, and provenance.
- `bench.ml`, `run.py`, `plot.py`: benchmark and plotting sources.

## FFT extension to the Kattis maximum

```sh
opam exec --switch=rocq-9.2 -- python3 benchmarks/polymul/extend_fft.py
uv run --with matplotlib python benchmarks/polymul/plot.py
```

The extension preserves the original paired measurements and adds a separate run
at 24,576, 32,768, 49,152, 65,536, 98,304, and 131,072 coefficients per input.
The maximum degree is therefore 131,071, and the maximum total input coefficient
count on the chart is 262,144. All six sizes completed seven trials successfully;
no FFT extrapolation is present in the resulting graph.

Each extended trial times one FFT call after warmup and a full major collection.
Validation is outside the timed region: 35 coefficient positions are checked by
exact integer convolution, four polynomial evaluation identities are checked
modulo two primes, and output length, coefficient magnitude bounds and input
immutability are checked. This is not a complete coefficient-by-coefficient
comparison against schoolbook at these larger sizes.

`fft-large.csv` stores the additional 42 measurements. `fft-extension.json`
records the source harness hash, date, outcomes and the 120-second timeout per
size. The extension stops at the first failed or timed-out size. If a future run
stops before the Kattis limit, the graph shows a separately labelled dotted
estimate scaled from the last measured FFT time using padded transform length
multiplied by its base-two logarithm. Estimates are saved separately in
`fft-extrapolation.csv`, never mixed into measured CSV rows.

## Schoolbook extension and extrapolation

Two further measured sizes completed: 24,576 and 32,768 coefficients per input,
seven trials each, using `bench_large.ml` and `extend_schoolbook.py`. Validation
uses the same independent checks as the large FFT extension. Further runs were
cancelled at the user's request, not because the machine failed.

The dotted schoolbook curve is a quadratic estimate anchored at the last measured
median: `T(N) = T(N0) * (N/N0)^2`, with `N0 = 65,536` total input coefficients.
The estimate at 262,144 total coefficients is about 65 seconds. These estimates
are in `schoolbook-extrapolation.csv`; measured trials remain separately in
`schoolbook-large.csv`. Both vertical specification-limit markers were removed
from the graph at the user's request.
