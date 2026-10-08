# Local reference installation candidate

The exact optimized proof transfer is accepted. The native candidate is hash-bound for local installation; final release review remains pending.
Keep scientific flags false. The Python wheel contains no executable.
Source-only installation preparation does not supply a final package or prove
that a release asset was reviewed or downloaded from an authentic publisher.

Use an isolated Python environment and obtain the eventual native asset from
the reviewed new GitHub release, over ordinary authenticated HTTPS. Verify its
published SHA256SUMS against the release's reviewed inventory. Do not execute
an arbitrary downloaded file because it accompanies a matching self-generated
manifest. The existing v0.1.0 release and archive stay unchanged.

The draft `tools/install_reference_manifest.py` accepts a local runtime
directory containing the required selected six sources, executable and named
provenance files. Its approval profile pins their expected hashes and the
installed Python launcher. It creates a fresh local manifest without network,
subprocess, PATH changes, registry/configuration changes, credentials, billing
or automatic execution. It refuses hash mismatches, symlinks, an existing
output, absolute/traversing approval paths, and scientific flags other than
false. The generated manifest uses local absolute paths for the launcher;
that local manifest is private and is never a release asset.

```text
python tools/verify_release_tree.py
python tools/install_reference_manifest.py --profile optimized --runtime-dir LOCAL_RUNTIME --output NEW_LOCAL_INSTALL
curveball-reference --request examples/native-sampling-six-vertex.request --installation NEW_LOCAL_INSTALL/installation.json --installation-sha256 PRINTED_HASH --entropy-file LOCAL_DETERMINISTIC_TAPE --evidence-dir PRIVATE_RUNS
```

The installer permits only the exact accepted optimized candidate and refuses missing proof/build/Python provenance. Frozen fallback remains held. Pass `--python-package-dir` pointing to the actual installed curveball_budget directory; the executing launcher separately checks its own origin/hash against those pins. A complete
source manifest is not enough to unblock it. There is no refresh/fresh-tape
retry or resume path. OS entropy is allocated once only after preflight;
provided deterministic tapes support execution controls only. Preserve failures
and do not select completed graphs by result.

The optimized owner transfer is accepted. Candidate validation builds the
Python wheel and source distribution, binds the installed Python source pins,
and exercises isolated installation/CLI/blocked/refusal controls. The separate
Windows AMD64 native asset and these exact package bytes still require final
main review GO. Checksums, local hashes
and compiler fidelity have distinct roles; the scientific contract additionally
depends on the stated independent uniform bytes, labeled-degree null and
trusted physical I/O.


Optimized acceptance: `CurveballVerified.native_prefix_request_type_I` and `CurveballNativeSamplingPrefix.mainOptimized_eq_frozen`, standard axioms, exact six sources/19 generated artifacts/binary5ec539cf...; see prefix-proof-ledger.json. Installed flags remain held pending main review GO. Explicit --predeclared --fixed-degree-null --trust-uniform-bytes acknowledges external scientific/entropy premises; provided deterministic tapes remain unassured. Multiple-testing/selection control is separate.


Conditional eligibility requires completed OS-byte mode and explicit --predeclared, --fixed-degree-null, --trust-uniform-bytes declarations, all under the stated external trust. Provided tapes and undeclared runs remain unassured. Main review GO is an additional gate for scientific authorization; a rank flag alone never enables it. No conditional-on-completion probability claim, sample-TV certification or empirical entropy certification is emitted.
