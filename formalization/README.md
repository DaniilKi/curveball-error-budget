# Accepted Curveball proof sources and their limits

These sources support the error-budget project: a focused ordinary-kernel/gap
corollary, a separate bounded native reference result, and optional ideal pairing
models/offline certificates. Start with [the practical contribution](../docs/CONTRIBUTION.md).
The current-main [pairing tools](../proof-tools/configuration-pairing/README.md)
provide their own exact closure and replay workflow; they are outside frozen v0.5.0
release files and do not certify the fast sampler or physical random draws.

The conditional reference proof and exact v0.2.0 release artifacts were accepted
and published. The shipped scientific runtime authorization remains **false**.
Labels such as `pending_mainreview` in frozen profiles/ledgers describe retained
build-time evidence; they are not a claim that publication review is still pending.
See [the published contract](../docs/PUBLICATION_v0.2.0.md).

`proof/` contains 93 accepted project source files, preserving the 90 frozen
modules. `upstream/` contains 153 unchanged focused OpenAI/math sources and
their Apache-2.0 license. `legacy/` retains the v0.1.0 focused extraction and
provenance; `pending-prefix/` retains earlier preparation records. Historical
DRAFT/SOURCE ONLY comments were preserved, and successful receipts establish
the accepted status. No proof/runtime source bytes changed in this docs update.

## Mathematical model and finite native result

For $n\ge4$, the focused ordinary uniform unordered-pair/full-fiber kernel
corollary has nonnegative spectrum and

$$
\mathrm{gap}(K)\ge\frac{1}{\binom{n}{2}}.
$$

This is a statement about the specified mathematical resampling operator,
not a proof that a seeded backend implements its ideal random law. The
normalization is a modest corollary of the credited upstream operator result,
not a new Curveball chain or established priority claim.

Accepted roots include `CurveballVerified.native_request_type_I`, the optimized
`CurveballVerified.native_prefix_request_type_I`, and the literal rejection-event
join `CurveballVerified.native_reply_reject_admissible`. Actual
`withinLimits r = true` and `arithmeticPlan r = true` are explicit request
premises. The observed graph is uniform among labeled simple graphs with its
exact degree vector, independently of a fresh full vector of uniform bytes.
Under this finite experiment the unconditional completed rejection probability
is bounded by request alpha. Refusal contributes no rejection; no claim is
conditioned on completion. Printed statements are in
[the root log](provenance/final-root.log) and [proof ledger](provenance/frozen-proof-ledger.json).

`CurveballNativeSamplingPrefix.mainOptimized_eq_frozen` proves equality of the
complete Lean IO expressions, including parsing, bounded reads, failures and
rendering. The three transfer modules, six runtime sources and generated
artifact/binary bindings are recorded in [the prefix ledger](provenance/prefix-proof-ledger.json).
Reported axioms are `propext`, `Classical.choice` and `Quot.sound`.

Lean/compiled caches, code generation, compiler/linker/runtime/loader/hardware,
reviewed Python bindings and physical IO/entropy correspondences remain trusted.
There was no fresh full dependency rebuild, independent-kernel replay or empirical
certification of uniform independent OS bytes. The native proof does not certify
NetworKit, legacy Python, seeded RNGs, an arbitrary scientific null, successful-run
TV, completion rate or power. See [limits and selection rules](../docs/ASSUMPTIONS.md).

## Pinned reproduction

Pins: Lean 4.34.1; mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`;
OpenAI/math `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Vendor compiled caches
were trusted. The focused route is not a full upstream Comparator run. Extraction
preserved 149 credited blocks (147 whole marked blocks and two factored blocks),
with four moved declaration groups retaining exact unique owners.

Use the exact published v0.2.0 source archive and its original pinned environment
for inventory verification/replay. These commands run in that archive's
`formalization/`, **not in docs-updated main**. Frozen release manifests include
original README bytes, so intentional documentation overlays fail their exact
inventory checks without invalidating unchanged proof sources.

```text
lake update
lake exe cache get
python ../tools/verify_release_tree.py
python replay_proofs.py --print-plan
```

Compare the supplied dependency lock after setup. The replay script only prints
an ordered plan; it does not launch compilation. A fresh isolated dependency
replay was not performed by packaging or this docs update. Do not use `lake build`
as an unreviewed broad build. Actual compiler execution needs a coordinated slot,
two free-commit observations at least 60 seconds apart clearing 6 GiB, a fresh
preflight, and the retained responsive resource guard. Preserve failed/censored
receipts. Public receipts are sanitized projections, not original private logs.

For installation rather than proof replay, use the matched source/native/Python
assets and [v0.2.0 installation guide](../docs/PUBLICATION_v0.2.0.md).
Publication approval does not promote the held scientific profile; declarations
record external premises rather than proving them.
