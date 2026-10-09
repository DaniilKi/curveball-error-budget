# 0.5.0 release candidate: read-only descriptive evidence

This candidate adds `curveball_evaluation` and `curveball-evaluation`. The existing degree-null planner/sampler and native/proof sources are unchanged apart from the package version string. New package fingerprints therefore require new environments; keep original pinned environments for historical jobs. The 0.4.0 beginner tutorial remains pinned to its tested wheel.

Build/install a local candidate wheel in a fresh environment:

```text
python -m venv .venv
.venv\Scripts\python.exe -m pip install --no-deps degree_null_research-0.5.0-py3-none-any.whl
.venv\Scripts\curveball-evaluation.exe --format json
.venv\Scripts\curveball-evaluation.exe --format markdown
```

These read saved evidence; no draws, inference, backend or compiler are invoked. Tested platform details and distribution digests belong in the accompanying validation receipt. macOS/Linux use .venv/bin paths; no new cross-platform installed smoke claim is made.

The exact [PWR-002 report](PWR-002.md), aggregate analysis and review050 receipt are preserved byte for byte. Review050 accepted descriptive evidence only. One failed job remains censored; its unknown partial output/time and 61 charged candidates are retained. All denominators, paired failures, failed advantage/cost conditions and original failed guard history remain visible. Original confirmatory status, reliable-power certification and scientific runtime authorization stay false. The interface performs no independent graph/CP/analyzer audit; authenticity of the independent review remains external to digest verification.

The public package contains no raw seeds, graphs, matrices, stub vectors or private process paths. Sanitized provenance cites NIST Harwell-Boeing BCSPWR01/02 and the official NetworKit algorithm tutorial. Full raw evidence remains privately retained. See the bundled LICENSE-SOURCE.md for attribution and scope. Existing classroom data-note and project-paper licenses remain separate.

In the extracted 0.5.0 source ZIP or sdist, check the candidate source inventory with `python tools/verify_current_release.py`. Git checkout line-ending conversion can change raw bytes; this inventory is bound to the supplied archives, not arbitrary mutable checkouts. It checks release/0.5.0/SOURCE-FILES.json, which deliberately excludes itself and documents that exclusion. It checks bytes/inventory, not proofs or runtime correctness. Historical SOURCE-MANIFEST/RELEASE-FILES and verify_release_tree.py belong to their exact approved archives/pinned environments; do not run their release-byte checks against this current overlay and interpret a docs/version mismatch as proof invalidation. No Lean/native build is performed for this release.

The older Zenodo software DOI describes version0.1.0 and the technical-note DOI describes version1.0; no new deposit is created here. Upstream PR1538 is an independently proposed draft, not adoption or seeded-backend certification. This release does not change that proposal or its licensing policy status.
