# Offline captured-output certificates

This optional workflow checks deterministic properties of provided finite data.
It runs no decoder, sampler or RNG. A kernel-checked certificate does not prove
execution authenticity, uniform random inputs, IID draws, power or reliability.
The ideal count-cap oracle has separate ideal-randomness premises.

The three examples are literal exports of the independently accepted finite
captures: a retained edge, repeated owners forming a triangle, and zero residual
stubs with an isolate. Private paths and worker metadata are excluded.

## Validate or emit

The UTF-8 JSON schema has exactly `schema_version` (1), `n`, `target_degrees`,
`fixed_edges`, `owners`, `returned_adjacency`, and `source_binding`. Limits are
64 KiB, 1-8 vertices and at most 16 owner occurrences. The source binding has
exactly `reference_sha256`, `function_source_sha256`, and `function_ast_sha256`.
Those hashes are assertions of provenance; the tool does not authenticate a
runtime capture. Other syntactically valid hashes are permitted because graph
properties do not depend on the asserted origin.

```text
python -X utf8 capture_to_lean.py examples/retained_edge.json
python -X utf8 capture_to_lean.py examples/retained_edge.json --output-dir emitted-retained
```

The first command validates only. The second emits finite literal data and
`by decide` proofs against `ConfigurationPairing.ownerCertificateCheck_sound`
into a new directory whose parent exists. Neither command runs Lean. An emitted
source file alone is not a kernel-checked certificate. Only bounded integers
enter Lean declarations; user strings never become Lean code.

The validator rejects duplicate JSON keys, non-integer booleans, bounds/schema
errors, odd owner lists, wrong residual multiplicities, loops, duplicate edges,
retained-edge collisions, asymmetric or incomplete adjacency, wrong labeled
degrees, and an output differing from the exact retained-plus-paired edge union.
Each occurrence receives a deterministic `(owner, occurrence index)` label;
that canonical lift is not a uniform permutation.

## Check with Lean

First complete the [pinned core replay](README.md#reproduce-the-authored-source-replay).
Its build directory contains the local receipt and all authored objects. Then,
from this directory, run one certificate check at a time:

```text
python -X utf8 check_capture.py examples/retained_edge.json --core-build build --output-dir checked-retained
```

Both directories are local; `checked-retained` must be new. This command validates
and freezes the input, emits a fresh source, and invokes the compiler recorded
by the successful core replay. It checks the source manifest, authored source
snapshots and objects, compiler and direct cached import bindings before and
after compilation. Existing directories and failed/incomplete core replays are
refused. Treat a certificate as checked only after the command terminates with
exit code zero and `CERTIFICATE-RECEIPT.json` reports `passed_kernel_certificate`
and `kernel_checked: true`.

The checker uses one thread, a 180-second aggregate limit including the
60-second stable start, setup, version query and cleanup, a 120-second compiler
limit, a polled 1.5 GiB resident limit, 6 GiB physical/start-commit headroom and
2 GiB live commit headroom. It inherits the Windows/Linux fail-closed guard;
polling is not an OS hard allocation limit. Source/object mutation, unknown
child cleanup, failures and deadline overruns withhold acceptance. Receipts and
raw logs stay local, including failed attempts. Compiler/toolchain and transitive
caches are trusted inputs; this is not a rebuild of that dependency closure.

Python reification and tooling have bounded controls and independent source
review, rather than a universal formal proof of the Python program. Lean checks
the encoded finite values. Metadata is not an execution certificate, and
count-capped ideal rejection does not cover arbitrary time/resource censoring.
No existing scientific/runtime/RNG/native authorization is promoted.

## Controls and evidence

```text
python -B -m unittest test_build test_capture_to_lean test_check_capture -v
```

These controls use mocked compiler objects and never launch Lean, sampling or
RNG. The supplied groups cover malformed/corrupt data, occurrence labels,
schema and injection strings, overwrite refusal, failed/incomplete core input,
source/object tampering, unknown cleanup and terminal receipt-write deadlines.
The capture tests retain local `test-artifacts`, which Git excludes.

The actual source replay and three generated fixture results are recorded in
`CORE-REPLAY.json` and `CERTIFICATE-REPLAY.json`. Timing is one-machine evidence,
not a speed guarantee. All failed preparation/control/proof attempts and
independent review receipts are preserved privately. Source and proof engineering
are AI-assisted; no new configuration-model algorithm or priority is claimed.
