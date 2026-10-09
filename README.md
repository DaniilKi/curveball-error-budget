# Curveball Error Budget

Imagine reshuffling a network while everyone keeps the same number of
connections. Curveball is an existing algorithm for that task. This project
adds explicit error-budget planning, identity checks and reproducible reporting,
plus a separate bounded Lean reference implementation. A mathematical budget
does not establish that a scientific model is appropriate or that a seeded
sampler has the ideal random law.

**Release candidate: 0.5.0; publication awaits exact release review.**
Published planner tutorial: [0.4.0](https://github.com/DaniilKi/curveball-error-budget/releases/tag/v0.4.0).
Start with the [tested beginner tutorial](docs/QUICKSTART.md). It uses invented
data and released NetworKit 11.2.2, requires no proposed upstream API, and runs
no sampler. Power, causation, a faster algorithm and a new mixing theorem are
not established by this project.

## What the releases add

| Release | Addition | Scope |
| --- | --- | --- |
| [0.1.0](https://github.com/DaniilKi/curveball-error-budget/releases/tag/v0.1.0) | Input/label checks, conditional batch budgets, streamed jobs and reports; focused mathematical kernel/gap sources | Research wrapper around existing Curveball; fast backend and seeded RNG remain outside the proof |
| [0.2.0](https://github.com/DaniilKi/curveball-error-budget/releases/tag/v0.2.0) | Conditional finite-request Lean reference theorem and optimized/frozen IO-expression equality; separate native artifact | Restricted reference path; release approval leaves scientific runtime authorization false |
| [0.3.0](https://github.com/DaniilKi/curveball-error-budget/releases/tag/v0.3.0) | Exact degree-list planning API and `curveball-plan` CLI | Calculates a conservative count; no samples or inference |
| [0.4.0](https://github.com/DaniilKi/curveball-error-budget/releases/tag/v0.4.0) | Immutable NetworKit Graph-to-plan snapshot | Retains sorted active IDs, exact optional labels, isolates and deleted-ID holes |
| 0.5.0 candidate | Read-only accepted descriptive study evidence | Retains failed job, denominators and scientific holds; no sampling |

## Install and plan

Use a separate environment. These Windows commands assume Python 3.12 or newer
as `python`, except 3.14.1; they are checked on Python 3.14.8. The optional
`networkit` extra installs released 11.2.2 and its declared dependencies from
PyPI. This project's wheel is published on GitHub, not PyPI.

```text
python -m venv .venv
.venv\Scripts\python.exe -m pip install "degree-null-research[networkit] @ https://github.com/DaniilKi/curveball-error-budget/releases/download/v0.4.0/degree_null_research-0.4.0-py3-none-any.whl#sha256=582e48beb245d590e4e11c499d43a047306fba3dfa05198a194a60657e8f068b"
.venv\Scripts\curveball-plan.exe --degrees "[1,1,1,1,0,0]" --epsilon 1/100 --max-trades 100
```

The last command prints JSON: **150 attempted trades required**, cap 100
insufficient, exit code 3, no sampling. A cap of 150 passes only the count
comparison; it is not a runtime or memory promise. Every attempt counts,
including unchanged outcomes. Counts cannot be converted directly into successful
swaps or GlobalCurveball rounds. The exact allowance is conditional on the
ordinary operator's nonnegative spectrum/gap and independent ideal uniform draws.
See [the planner contract](docs/PLANNER.md).

For a graph, use `curveball_trade_plan_from_networkit` as shown in the tutorial.
The adapter accepts simple undirected, unweighted graphs with at most 1,000
active nodes and refuses loops, duplicate edges and invalid label coverage.
It does not compact node IDs or draw random numbers. See
[graph validation and optional installation](docs/NETWORKIT_GRAPH.md).

Download the [tutorial wheel](https://github.com/DaniilKi/curveball-error-budget/releases/download/v0.4.0/degree_null_research-0.4.0-py3-none-any.whl),
[review/source bundle](https://github.com/DaniilKi/curveball-error-budget/releases/download/v0.4.0/curveball-error-budget-v0.4.0-review.zip)
and [checksums](https://github.com/DaniilKi/curveball-error-budget/releases/download/v0.4.0/SHA256SUMS.txt).
Keep original pinned environments for older jobs; source fingerprints differ.
On macOS/Linux the environment's Python is `.venv/bin/python`; this quickstart
was not tested there.

## Which path is assured?

| Path | What is established | What remains conditional or unverified |
| --- | --- | --- |
| Planner and Graph adapter | Tested exact count arithmetic, input validation and immutable output | Operator/randomness assumptions; no execution, inference or scientific authorization |
| `curveball-reference` | Accepted Lean finite-request rejection bound and complete optimized/frozen IO-expression equality | Physical entropy, compiler/runtime/dependencies, scientific null and external correspondences; authorization remains false |
| `degree-null` fast NetworKit workflow | Reviewed research integration and bounded empirical controls | No native-proof certification of its sampler, seeded RNG or scientific inference |
| `degree-null --backend reference` | Legacy Python debugging sampler | Separate from the Lean native command; no transfer of its proof |

The native theorem bounds **unconditional completed triangle-rank rejection
mass** under a uniform labeled exact-degree null and independent uniform full
bytes, with actual limits/arithmetic checks. It does not certify successful-run
TV, physical entropy, completion rate or power. Refusal never rejects and is not
a completed negative test; do not retry until success or condition on completion.

Native limits include 4–26 vertices, 1–32 replicates, at most 1,024 attempted
trades per replicate, rejection cap at most 128 and at most 262,144 entropy
bytes, plus exact parser/arithmetic gates. One-percent rejection is impossible
at this rank resolution; at 5%, at least 20 replicates and sufficient allowance
are necessary. Predeclaration/null/randomness flags record assumptions rather
than establish them. For native reproduction use the matched **0.2.0** assets
and environment in [its installation contract](docs/PUBLICATION_v0.2.0.md),
not a mixture with the latest wheel. See [proof scope](formalization/README.md)
and [scientific/execution limits](docs/ASSUMPTIONS.md).

## What the practical evidence says

In SocioPatterns' 31-student classroom pilot, **51 of 71 second-day contact
edges also occurred on day one**. A prespecified 199-output run had no
tie-inclusive upper-tail exceedances and adjusted rank score **0.015**, conditional
on ideal kernel/randomness correspondence. This challenges that degree-only
recorded-contact baseline; it establishes no social mechanism or causation.
**The original power gate failed, so power remains unmeasured**, not measured zero.
No accuracy or runtime advantage over the heuristic comparators was established.

A separate prospective diagnostic covered all **70 observation states in 445
jobs**. Its weighted estimate was 0.0137143, with a broad simultaneous 95% interval
[0.0121146, 0.7984326]; it is not precise unconditional calibration or a seeded
backend certificate. See the published [feasibility note and diagnostic](https://github.com/DaniilKi/curveball-error-budget/releases/download/v0.3.0/FEASIBILITY-NOTE.md).
This study-derived summary follows **CC BY-NC-SA 3.0**, separately from software
and paper licenses, with SocioPatterns and Fournet/Barrat attribution in
[the source/license note](https://github.com/DaniilKi/curveball-error-budget/releases/download/v0.3.0/LICENSE-SOURCE.md).
No pupil identifiers, mappings or contact graphs are distributed here.

## Upstream work and citation

As checked on 2026-10-09, [NetworKit draft PR #1538](https://github.com/networkit/networkit/pull/1538)
is open and unmerged. Current-head main CI passed all 22 jobs; the targeted
Linux x86_64 CPython 3.15 installed-wheel API, complete notice-byte and metadata
checks passed. These test an upstream proposal, separately from our released
11.2.2 Graph adapter. Maintainer acceptance of API scope and mixed-component
licensing remains unresolved; passing CI is not adoption or sampler certification.
[Details and limitations](docs/NETWORKIT_GRAPH.md).

Use [CITATION.cff](CITATION.cff) and name the software version used. The existing
[Zenodo software DOI](https://doi.org/10.5281/zenodo.23240269) archives **0.1.0**;
it is not a deposit of 0.4.0. The unchanged [technical-note DOI](https://doi.org/10.5281/zenodo.23240350)
is note version 1.0, not peer-reviewed acceptance or a new deposit. Cite the
underlying OpenAI/math input and ordinary Curveball/heat-bath prior work
separately; see [NOTICE](NOTICE) and [paper context](paper/README.md).
No new sampler, established firstness or dimension-13 runtime/compression
consequence is claimed. Software is Apache-2.0; the paper is CC BY 4.0.
Prior release tags/assets and version-specific records are preserved.

## Read saved descriptive evidence

Release 0.5.0 adds `curveball-evaluation --format json` (or `markdown`) and the
[read-only evaluation adapter](docs/EVALUATION.md). It requires no optional
backend and runs no sampler. See [installation and release scope](docs/RELEASE_v0.5.0.md).

[PWR-002's exact accepted report](docs/PWR-002.md) retains 9,017 completed jobs
and one interrupted pairing job across the full 9,018-job schedule. Primary
null detections were 89/3000 for both pairing and Global20; the censored pairing
outcome gives sensitivity 89..90/3000. Moderate detections were 1146/1200 and
1153/1200. These are descriptive conditional calculations, not certified power.
The original confirmatory status is withdrawn; scientific/runtime holds stay false.
Pairing failed the predeclared +.05 advantage threshold, and Global605 failed
the cost-matching condition. Partial interrupted time/output count remain unknown.
The historical classroom failed power gate remains unchanged: its power was
unmeasured. PWR-002 does not restore that gate or establish real-grid fault detection.

The wheel includes aggregate analysis, exact report/review bytes and sanitized
provenance; the report's archive references mean the private raw research archive.
It contains no raw matrices, seeds, graphs, private paths or runtime binaries.
Known whole-pairing rejection is an existing algorithm under ideal randomness;
neither this evidence nor the simplex dimension-13 volume theorem establishes
a new graph algorithm, seeded-law proof or runtime improvement.
