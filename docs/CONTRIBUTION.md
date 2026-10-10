# Contribution and practical use

The contribution is a usable conditional error budget for existing ordinary
undirected Curveball, derived from a credited recent OpenAI theorem. It turns an
error tolerance into an explicit sufficient attempt count, then keeps that
allowance visible when planning batches and reporting Monte Carlo comparisons.

**Current practical conclusion:** the supported contribution is conditional
mathematical distribution-approximation assurance, made usable through exact
error-budget planning. Our tested examples have not demonstrated a compelling
practical advantage over the strongest applicable existing alternatives we
assessed. A sufficient schedule may require more computation; it buys a stated
error bound under assumptions, not a demonstrated speed, power or accuracy gain.
Existing valid significance tests predate this planner.

The [accepted archived bird illustration](BIRD-001.md) reached the same
.05 non-rejection with the sufficient rule and the older Besag-Clifford rank
test. It is a compatible worked example, not original-paper replication or
evidence that exact algorithms generally fail. The mathematical results and
scoped proof tools remain useful under their stated contracts.

## Before and after

Ordinary Curveball, GlobalCurveball and efficient implementations already existed.
Carstens, Berger and Strona describe the undirected algorithm and its uniform
stationary target; their discussion also includes configuration/perfect-matching
approaches. Carstens and Kleer prove bipartite Curveball/switch mixing comparisons.
Fu, Qin and Wang study binary fixed-margin matrices. Earlier rigorous sampling
theory therefore exists; these settings and operators must not be conflated.

The pinned OpenAI manuscript proves a strong inequality for its undirected
pair-resampling generator H, before comparison with the switch chain: H^2 >= H,
with constants as its kernel. For C=binom(n,2), ordinary uniform-pair Curveball
has P=I-H/C. Each pair update is an orthogonal heat-bath projection, so P has a
nonnegative spectrum. The credited ingredients give gap(P) >= 1/C for the
specified ideal operator. The normalization is a derivative corollary, not a new
mixing theorem credited to this project.

If M is the number of labeled simple graphs in the exact degree class, the usual
spectral-to-total-variation conversion gives TV <= (1/2)*sqrt(M)*exp(-t/C).
The planner uses the computable bound B=binom(C,m), exact upward-rounded binary
arithmetic and a final integer envelope check. This converts a requested tolerance
into a conservative sufficient number of attempted pair trades, including
unchanged outcomes. It does not estimate the minimum mixing time.

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

## What you can use now

- Plan before launching an expensive job, and identify insufficient count caps.
- Preserve sorted active graph IDs, labels, isolates and deleted-ID holes in an
  immutable Graph-to-plan snapshot using released NetworKit 11.2.2.
- Allocate a batch allowance eta across b outputs as eta/b per output, conditional
  on independent ideal draws and the specified ordinary kernel.
- Inspect reproducible saved studies, including negative findings and failed jobs.
- Examine a separate restricted Lean reference result, or check deterministic
  properties of supplied toy-sized finite captures with the optional proof tools.

An adjusted rank-test rule pays the batch allowance explicitly. Scientific use
still requires an appropriate labeled degree-only null, a predeclared statistic,
accounted selection/multiplicity, and the randomness/backend premises. The planner
performs no sampling or scientific test and grants no runtime authorization.

## Evidence and limitations

The [tutorial](QUICKSTART.md) demonstrates planning with invented data. The
[planner contract](PLANNER.md) states exact units, arithmetic and limits.
[PWR-002](PWR-002.md) retains one interrupted job and reports descriptive results:
the predeclared pairing advantage and cost-matching conditions failed. The earlier
classroom power gate failed, leaving its power unmeasured. Neither study proves
an empirical speed/accuracy gain from the theorem or certifies a seeded backend.
The [BIRD-001 summary](BIRD-001.md) retains the later archived-attribute
illustration, equal .070 rank conclusions and narrowly scoped pairing failure.

The [accepted native reference](../formalization/README.md) and the
[optional pairing tools](../proof-tools/configuration-pairing/README.md) have
different contracts. A finite-output certificate establishes deterministic graph
and owner-data properties; it does not prove the capture is authentic, uniformly
random or IID. Count-capped ideal oracle results do not justify conditioning on
time/resource completion. Physical randomness, compiler/runtime correspondences
and the whole fast NetworKit stack remain outside the accepted assurances.

## Upstream and archived snapshot status

The proposed [NetworKit helper](https://github.com/networkit/networkit/pull/1538)
was withdrawn and closed unmerged because practical advantage and demand had
not been established sufficiently to justify upstream maintenance. The tested
standalone planner remains available; this is not a mathematical withdrawal.
See the [verified upstream status](NETWORKIT_GRAPH.md).

The reviewed Zenodo upload kit remains frozen at commit
`ea0f86d1c508e7f2f312c161c2075d111195bc11`, before this conclusion/status update.
It has not been silently revised or deposited. A kit advertised as including
these later docs needs a refreshed source archive, exact metadata/checksums and
review. The current mathematical note and old release assets are unchanged.

## Primary sources and credit

- [OpenAI pinned manuscript and source](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Polynomial-Mixing-of-the-Switch-Chain-for-Every-Graphical-Degree-Sequence-September-25-2026): the undirected pair-generator inequality and constant kernel, especially `build/sections/mixing.tex`.
- [Carstens, Berger and Strona](https://arxiv.org/abs/1609.05137v3): existing undirected Curveball, stationary target and prior sampling methods.
- [Carstens and Kleer](https://doi.org/10.4230/LIPIcs.APPROX-RANDOM.2018.36): bipartite Curveball/switch comparisons.
- [Fu, Qin and Wang, version 2](https://arxiv.org/abs/2606.22636v2): binary fixed-margin theory, distinct from the undirected graph state space here.
- [Dyer, Greenhill and Ullrich](https://doi.org/10.1016/j.laa.2014.04.018): heat-bath structure and spectrum.
- [Global Curveball](https://arxiv.org/abs/1804.08487v2) and [NetworKit tutorial](https://networkit.github.io/dev-docs/notebooks/Randomization.html): existing efficient implementations and recommended empirical schedules.
- [SEA 2026 empirical mixing study](https://doi.org/10.4230/LIPIcs.SEA.2026.2): empirical diagnostics, distinct from a finite-error theorem.

The editable [technical note](../paper/README.md) supplies the mathematical
derivation and dated software/evidence scope. No global firstness or peer-review
acceptance is claimed. OpenAI receives source-theorem credit; existing algorithms,
heat-bath positivity, spectral conversion and rank tests retain their prior credit.
AI assistance and separate component licenses are recorded in [NOTICE](../NOTICE).
The unrelated simplex dimension-13 volume result gives no graph-runtime guarantee.
