# Focused ordinary-Curveball mathematical assurance

This directory includes153 unmodified official Lean source files from OpenAI/math commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, the exact focused compiler input, an authored normalization corollary, source/line/scope mappings, pinned dependency revisions and sanitized verification receipts. Original source files retain the upstream Apache-2.0 license in upstream/LICENSE. The combined extraction removes original import directives, selects official Mathlib imports and encloses each unchanged body in a separate outer section. It preserves public declaration names and original proof bodies; private Lean internal names use the extraction module. See provenance/exact-body-extraction-map.json for the precise transformation.

The source-owner compiler run succeeded with Lean4.34.1 in135.031seconds, two threads, using the pinned official Mathlib/dependency cache. Five printed axiom lists contain only propext, Classical.choice and Quot.sound; no sorryAx or additional axioms were reported. The packaging worker consumed the successful receipt and compiler output and independently rechecked all153 source bodies, hashes and extraction segments. A separate reviewer audited those bodies and axiom lists. Packaging did not rerun this compilation.

The compiled result is for n>=4 and every graphical labeled degree vector: the ordinary uniform unordered-pair/full-fiber Curveball kernel has Poincare gap at least1/binom(n,2). The fiber includes the original assignment and preserves the mutual edge, common neighbors and other edges. The formal statement is ordinary_curveball_gap at the end of CurveballAssurance.lean, compiled inside ExactBodyExtraction.lean. CurveballAssurance.lean retains its original upstream imports for inspection; compile the combined file for this focused replay route. Below four vertices, supported graphical inputs have unique realizations and the software's sufficient uniqueness certificate uses zero trades.

To check bytes and recorded evidence without compilation:

```sh
python verify_sources.py
```

To replay using official Lean/Lake and dependencies in a fresh checkout:

```sh
lake update
lake exe cache get
python verify_sources.py
lake env lean -j 2 -DautoImplicit=false -DmaxRecDepth=4096 -DmaxHeartbeats=1000000 -o ExactBodyExtraction.olean ExactBodyExtraction.lean
```

The supplied lake-manifest.json pins the dependency revisions used by the successful source-owner run. Compare these pins after setup. The portable Lake configuration is supplied for setup; a complete fresh-environment replay of that configuration was not performed by the packaging worker. Compilation may require several GiB beyond the sampler's memory budget. Do not run it concurrently with memory-heavy jobs on a small computer. No compiled proof/dependency bulk is distributed.

Trust scope: this was a focused extraction, not the original module-by-module build, the upstream Comparator, a full Mathlib source rebuild or an independent-kernel/Nanoda replay. The successful run trusts the official Lean compiler and pinned compiled dependency cache. It checks the mathematical resampling model and gap. It does not formally verify Python, NetworKit, the seeded PRNG, the state-count stopping arithmetic, TV conversion, joint-batch budget or rank-test implementation. Those remain separately reviewed mathematical/software steps with ideal independent randomness and complete predeclared-workflow assumptions. No new chain or spectral inequality priority is claimed: the strong pair-generator and graph/subset ingredients are upstream results, and normalization is a modest corollary.
