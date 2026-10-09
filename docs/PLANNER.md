# Ordinary Curveball planner

The degree-list API/CLI was published in v0.3.0. Version0.4.0 also adds a separately documented [NetworKit graph adapter](NETWORKIT_GRAPH.md); the degree-list planner remains unchanged. The
planner calculates a sufficient attempted-trade count under explicit mathematical
and ideal-randomness assumptions. It does not run NetworKit, sample a graph, test a
scientific hypothesis or grant scientific authorization.

## API and command

```python
from degree_null import curveball_trade_plan

plan = curveball_trade_plan(
    [1, 1, 1, 1, 0, 0], "1/100",
    max_trades=100, trade_chunk_size=32,
)
assert plan.attempted_pair_trades == 150
assert plan.within_trade_limit is False
record = plan.as_dict()
```

In an environment containing this package:

```text
curveball-plan --degrees "[1,1,1,1,0,0]" --epsilon 1/100 --max-trades 100
curveball-plan --degrees-file degrees.json --epsilon 1/100 --max-trades 150
```

The command writes a JSON planning record. Exit 0 means the record was produced;
it does not mean a scientific test succeeded. Exit 3 reports a declared trade cap
is insufficient; the required count is retained. Exit 2 reports invalid input.
Input files are UTF-8 JSON degree arrays with a 16 KiB limit. The command does not
accept datasets or invoke an external service.

Degrees retain their label order and include isolates. The API accepts a finite
list or tuple of at most 1,000 exact integers and checks graphicality. Epsilon must
be strictly between zero and one half, expressed as an exact Fraction or bounded
decimal/integer-fraction string. Floating inputs and scientific-exponent strings
are refused. The immutable result records its schema, published baseline and
credited operator-source commits. Keep the external label mapping when extracting
a degree vector; the vector itself contains no labels.

`examples/plan_only.py` uses only the synthetic edge and complete vertex files
next to it, retains two isolates and produces no samples. It requires no classroom
data or NetworKit. Run it from the checkout with `python -B examples/plan_only.py`.

## Exact contract and cost

Only `kernel="ordinary_uniform_pairs"` is supported. The units are attempted
unordered vertex-pair resampling trades, including unchanged outcomes. Budgets
cannot be translated into GlobalCurveball rounds, successful edge switches,
connectivity-conditioned sampling, directed/weighted networks or binary-matrix
kernels. A supplied degree vector does not establish that a chosen backend
implements this law.

For a nontrivial degree class, let C=binom(n,2), m=sum(degrees)/2 and
B=binom(C,m). The existing exact planner uses u=ceil(log2 B),
v=ceil(log2(1/(2 epsilon))) and t=C*(ceil(u/2)+v). Its integer check verifies the
squared binary envelope B <= 4 epsilon^2 2^(2t/C). Under the credited ordinary
heat-bath operator's positivity and gap >=1/C, this is a conservative sufficient
TV budget. It is not the minimum mixing time. A sufficient isolated/universal
peeling certificate recognizes unique labeled states, which need zero trades;
zero trades do not imply inferential power or useful rejection.

The target is a uniform labeled simple undirected graph with exactly the same
per-label degrees, allowing disconnected outcomes. Pair/subset draws must be
ideal and independent. Seeded PRNG reproducibility does not establish that law.
The accepted native Lean theorem covers a separate restricted reference path;
it does not certify NetworKit, the Python fast workflow or their RNG/dependencies.
The native 26-vertex, 1,024-trade, 32-replicate and additional arithmetic/entropy
gates remain in place. This API neither lifts them nor changes failure semantics.

`max_trades` is a count comparison, not an execution limit or feasibility proof.
An unspecified cap remains unspecified; an insufficient cap never truncates the
mathematically requested count. Chunk counts and packed-pair bytes describe a
hypothetical streamed list of two uint64 endpoints per pair. They exclude
containers, graph/kernel storage, allocator effects and temporary integers.
The scalar state-bound payload is not peak memory. No sampler runtime or total
RSS prediction is provided. The inherited graphicality routine materializes a
graph; dense n=1,000 planning allocations are unmeasured. The empty n=1,000
control does not establish dense-case affordability.

The result explicitly reports no sampling, no inferential decision and false
scientific runtime authorization. Cap exceedance and an inability to reject are
not successful scientific outcomes. Scientific null suitability, batch independence,
selection, rank resolution and multiplicity require separate control.

## Existing functionality and release delta

The published project already provides `kernel.certificate`, `jobs.make_plan` and
an ordinary NetworKit 11.2.2 integration. Five existing validation/certificate
functions are factored into `planning_core.py` with unchanged function bodies;
`kernel` imports them, and the new API uses the same core. Legacy certificate
dictionaries remain unchanged. The additions are an immutable planning record,
strict public inputs, count/payload reporting, portable tests, a dedicated CLI and
synthetic documentation. There is no new sampler or mixing theorem.

Legacy jobs bind all Python source hashes. This refactor/addition changes that
fingerprint, so this package must not resume jobs made with earlier source fingerprints. Use their
original pinned environment; the existing resume guard remains intact.

Run portable planner controls with
`python -B -m unittest discover -s tests -p test_planning.py`.
They carry an unchanged licensed v0.2.0 kernel fixture and protected-file digests;
they require no sibling checkout, backend installation, random seed or data download.
They independently enumerate small graph classes and exact pair/subset laws.
These checks support the planner implementation, not the correctness of a whole
scientific library or physical entropy source.

The separate pilot failed its original full-scale power promotion gate. That gate
applies before promoting a sampler for validated scientific inference; it does not
preclude this planner engineering. The pilot's aggregate note and source-data
license are separate review materials and are not packaged with the code.

## Attribution and later upstream work

Authored code, frozen control source and synthetic examples retain Apache-2.0,
LICENSE and NOTICE. The unchanged paper retains its own CC BY 4.0 terms. No
NetworKit/TLX source, binaries, classroom identifiers, mappings, contact graphs or
derived study outputs are included in this planner contribution.

The credited conditional input is OpenAI/math family 131 at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Ordinary Curveball and heat-bath prior
work remain attributed in NOTICE, including Carstens/Berger/Strona, Carstens et al.
and Dyer/Greenhill/Ullrich. Fu/Qin/Wang's June 2026 binary-matrix work has a different
scope. API engineering, mathematical novelty, formal reference correctness,
human peer review and practical efficacy are separate claims; no worldwide-firstness
claim is made.

This is our project's API, not an accepted NetworKit contribution. A later upstream
proposal requires maintainer scope/convention agreement and licensing review; copied
Apache code must not silently be relabeled MIT. The separate source-only upstream proposal is documented in NETWORKIT_GRAPH.md; project release publication does not establish upstream acceptance or backend certification.
