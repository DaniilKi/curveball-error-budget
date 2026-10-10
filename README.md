# Curveball Error Budget

We make a recent OpenAI all-degree-sequence theorem usable as an explicit
sampling-error budget for ordinary Curveball. Give the planner a graph's degrees
and an error tolerance; it returns a conservative sufficient number of attempted
trades, with exact arithmetic and a clear report when your count cap is too small.
The tested tutorial runs this calculation without sampling a graph.

Curveball already reshuffled networks while preserving every vertex's degree.
Efficient implementations and rigorous results for important settings already
existed. The practical advance here is connecting the credited general undirected
operator bound to usable tolerance-to-count planning, whole-batch error accounting,
reproducible evaluation and separate, bounded proof/certificate tools.

For example, `[1,1,1,1,0,0]` with tolerance `1/100` produces **150 attempted
trades**. A cap of 100 is reported as insufficient; it does not silently shorten
the plan. This is a conditional guarantee for the specified ordinary operator and
independent ideal uniform draws. It is not a certified law for a seeded backend.

| What existed | What this project enables |
| --- | --- |
| Degree-preserving Curveball and efficient ordinary/Global implementations | A separately usable ordinary-chain planner driven by an explicit error tolerance |
| Rigorous mixing results for restricted degree families and matrix/bipartite settings | A derivative general undirected gap corollary from the pinned OpenAI operator theorem |
| Empirical diagnostics and heuristic trade counts | A conservative sufficient count and explicit batch sampling-error allowance |
| Mathematical arguments and implementation tests | Scoped Lean reference results and offline finite-output certificates, with their trust boundaries recorded |

Start with the [tested beginner tutorial](docs/QUICKSTART.md), then see
[the contribution and credited prior work](docs/CONTRIBUTION.md).
The useful guarantee is an explicit error allowance under stated premises.
No measured speed/accuracy advantage, new shuffle, worldwide priority or full
fast-stack verification is established. Negative studies remain documented below.

**Published prerelease: [0.5.0](https://github.com/DaniilKi/curveball-error-budget/releases/tag/v0.5.0).**
Published planner tutorial: [0.4.0](https://github.com/DaniilKi/curveball-error-budget/releases/tag/v0.4.0).
Start with the [tested beginner tutorial](docs/QUICKSTART.md). It uses invented
data and released NetworKit 11.2.2, requires no proposed upstream API, and runs
no sampler. Power, causation, a faster algorithm and a new mixing theorem are
not established by this project.

## When to use it

Use the planner when an explicit distributional sampling-error guarantee matters
to your prespecified simulation or comparison, the operator/randomness premises fit,
and the sufficient ordinary-trade count is affordable. Compare it with exact
pairing rejection and other proven samplers for your degree sequence. A longer
sufficient schedule buys a stated bound; a short heuristic is not thereby shown
inaccurate. Our BC39/49 study found inexpensive exact-reference sampling and did
not demonstrate an unmet need or superiority. The planner can also report that a
requested count cap is insufficient. Scientific null suitability remains separate.

For significance testing alone, existing Besag-Clifford exchangeable MCMC
tests can avoid a mixing-time requirement. Under their stationary-null and ideal
kernel premises, a reverse leg and forward spokes give valid rank tests at a
fixed length. This differs from approximating an independent uniform batch or a
global tail distribution. See [Howes, Section 3.1](https://arxiv.org/html/2310.04924v2).
This project did not first make fixed-degree significance tests valid.

## What the releases add

| Release | Addition | Scope |
| --- | --- | --- |
| [0.1.0](https://github.com/DaniilKi/curveball-error-budget/releases/tag/v0.1.0) | Input/label checks, conditional batch budgets, streamed jobs and reports; focused mathematical kernel/gap sources | Research wrapper around existing Curveball; fast backend and seeded RNG remain outside the proof |
| [0.2.0](https://github.com/DaniilKi/curveball-error-budget/releases/tag/v0.2.0) | Conditional finite-request Lean reference theorem and optimized/frozen IO-expression equality; separate native artifact | Restricted reference path; release approval leaves scientific runtime authorization false |
| [0.3.0](https://github.com/DaniilKi/curveball-error-budget/releases/tag/v0.3.0) | Exact degree-list planning API and `curveball-plan` CLI | Calculates a conservative count; no samples or inference |
| [0.4.0](https://github.com/DaniilKi/curveball-error-budget/releases/tag/v0.4.0) | Immutable NetworKit Graph-to-plan snapshot | Retains sorted active IDs, exact optional labels, isolates and deleted-ID holes |
| [0.5.0 prerelease](https://github.com/DaniilKi/curveball-error-budget/releases/tag/v0.5.0) | Read-only accepted descriptive study evidence | Retains failed job, denominators and scientific holds; no sampling |

## Optional proof tools on current main

The separate [configuration-pairing proof tools](proof-tools/configuration-pairing/README.md)
provide the accepted ideal count-cap oracle and a bounded offline certificate
workflow for captured finite outputs. A checked graph certificate proves a
deterministic property of that output; it does not establish uniform random
sampling, IID, power or scientific reliability. This source addition changes no
package version, sampler, scientific hold or published v0.5.0 artifact.

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
