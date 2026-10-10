# Optional configuration-pairing proof tools

This separate source component provides a checked finite mathematical oracle and
an optional offline certificate for a captured graph. It adds no sampler, changes
no package version or scientific authorization, and does not alter published
v0.5.0 assets. The source and proof engineering were AI-assisted. The underlying
configuration-pairing mathematics is established; no new algorithm, priority,
speedup or practical reliability is claimed.

## What is proved

For retained simple edges `F` and original labeled degrees `d`, the ideal-oracle
root `ConfigurationPairing.ideal_flat_graph_oracle_contract` assumes a feasible
target graph and a bijective enumeration of distinct vertex/slot stubs. Under a
finite independent product of ideal uniform permutations, the decoder uses
adjacent positions `2*i` and `2*i+1` and inspects whole candidates up to a count
cap. For the complete target family `H`, matching family `M`, residual degrees
`s(v) = d(v) - degree_F(v)`, and
`rho = 1 - |H| * product_v factorial(s(v)) / |M|`, it proves

```text
0 <= rho < 1
P(all cap candidates rejected) = rho^cap
P(return g) = (1 - rho^cap) / |H|  for every g in H
```

For positive caps, successful outputs therefore have the ideal uniform law.
Cap zero has no successful event. The equal graph fibers, uniform matching law
and literal adjacent-position join are proved. A closed formula `2^m * m!` is
not proved or needed for this root.

The separate root `ConfigurationPairing.ownerCertificateCheck_sound` takes an
explicit Boolean acceptance check. It checks that occurrence labels cover each
distinct stub exactly once, owners agree, pairs have no loops, duplicates or
retained-edge collisions, the captured graph is exactly the union of retained
edges and owner pairs, and its complete labeled degrees are `d`. A successful
Lean check proves a deterministic property of that finite output and joins it
to the mathematical decoder. Three captured finite examples discharge the
Boolean premise using kernel reduction with `by decide`.

**A graph certificate does not prove random uniformity, IID draws, power,
scientific reliability, or correctness of every Python execution.** A canonical
occurrence-label lift is not a uniform random distinct-stub permutation. The
ideal-law theorem and per-output certificate have different premises.

## Source and trust boundary

`PROVENANCE.json` lists the exact raw-byte source closure and build order.
Independent component reviews 051, 054, 055 and 056 establish the recorded
accepted roots. Their private original receipts and failed attempts are retained
separately; public summaries and digests are not cryptographic attestations.
Only accepted modules enter the build order. Historical proof sources and
release inventories are untouched, including historical line endings.

Lean is pinned to 4.34.1 and mathlib to
`d13f23b723b8a846827a245b89c10fc7d3f11612`; the package manifest pins its
dependencies. The Lean binary and cached dependency objects are trusted.
Replaying these authored modules is not a transitive rebuild of the toolchain
or mathlib. Printed accepted roots use `propext`, `Classical.choice` and
`Quot.sound`; no `sorryAx` is accepted by the replay wrapper.

The complete repeated-owner Python wrapper, NumPy/Philox uniformity and IID,
NetworKit/native kernels, compiler/FFI correspondence, counter/refusal behavior
and wall-clock/resource censoring remain outside this proof. An arbitrary
time-dependent stopping rule is not covered by the count-cap law. Existing
empirical results remain descriptive and their failed/censored history remains
intact. The simplex dimension-13 volume optimum supplies no graph sampling or
runtime guarantee.

## Reproduce the authored source replay

From this directory, first run the checks requiring only Python:

```text
python build.py --verify-only
python -B -m unittest test_build -v
```

Use a separate Lean environment and the pinned `lean-toolchain` and
`lake-manifest.json`. Obtain the pinned dependency checkout/cache with the
official [mathlib cache workflow](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency).
Then use [Lake's environment](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)
to supply its cached search paths:

```text
lake exe cache get
lake env python build.py --lean-binary lean --lake-environment --output-dir build
```

The wrapper performs no downloads or dependency rebuilds. Alternatively provide
the Lean executable path and repeat `--dependency-dir` for each existing cached
dependency library directory. It rejects a dependency directory that shadows an
authored module. Output must be a new directory; prior results are not removed
or overwritten.

Run one proof build at a time. The Windows/Linux wrapper uses one compiler
thread, a 600-second aggregate limit including setup, stable observations and
cleanup, a 120-second module limit, at least 6 GiB physical headroom, 6 GiB
initial commit headroom, 2 GiB ongoing commit headroom, and a polled 1.5 GiB
compiler resident-memory limit. Sixty seconds of stable initial headroom is
included in the aggregate budget. Memory
queries fail closed; an interrupted child is killed and reaped. Polling is not
an OS hard memory limit. Other platforms fail closed until their memory guard
is implemented and reviewed. On Linux, an overcommitted system without the
required remaining commit allowance is refused. Frozen source snapshots and
pre/post source, manifest, binary and direct-cache bindings detect mutation.
Local logs, resolved cache paths, object hashes, timings, cleanup errors and failures
are retained in the chosen output directory. No seeded sampling or inference
runs as part of this replay.

## Optional captured-output workflow

Use the [offline certificate workflow](CAPTURE-WORKFLOW.md) to validate or emit
bounded captured JSON and then kernel-check the generated finite certificate
against a successful local core replay. Validation and source emission alone
do not assert kernel acceptance. The tool supports 1-8 labeled vertices and
at most 16 owner occurrences, including isolates and zero residual stubs.
The input's source hashes are provenance assertions, not execution authentication.

The measured [core replay](CORE-REPLAY.json) compiled all 20 authored modules
in 225.45 seconds including the 60-second stable start, with 164.65 seconds
of compiler wall time and a 1.04 GiB polled resident peak. All children were
terminal and the two main roots printed only the standard axioms listed above.
These are one-machine Windows observations with trusted cached dependencies,
not a performance or whole-stack verification result.

This component follows the repository [license](../../LICENSE). mathlib and its
dependencies retain their own licenses; their binaries are not distributed here.
