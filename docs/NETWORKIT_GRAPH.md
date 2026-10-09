# NetworKit graph-to-planner adapter

Version 0.4.0 adds `degree_null.curveball_trade_plan_from_networkit` and the
frozen `NetworkitGraphTradePlan` result. Version 0.3.0 accepted a degree list;
this adapter accepts a real NetworKit Graph, validates its simple graph
structure, and retains the node-ID/optional-label correspondence in a snapshot.
It uses our existing exact planner and produces no graph samples or inference.

```python
import networkit as nk
from degree_null import curveball_trade_plan_from_networkit

graph = nk.Graph(8)
graph.addEdge(0, 1)
graph.addEdge(2, 3)
graph.removeNode(4)
graph.removeNode(6)
labels = {node: f"synthetic-{node}" for node in graph.iterNodes()}
result = curveball_trade_plan_from_networkit(
    graph, "1/100", labels=labels, max_trades=100,
)
assert result.node_ids == (0, 1, 2, 3, 5, 7)
assert result.plan.degrees == (1, 1, 1, 1, 0, 0)
assert result.plan.attempted_pair_trades == 150
assert result.plan.within_trade_limit is False
assert result.labels == tuple(labels[node] for node in result.node_ids)
record = result.as_dict()
assert record["sampling_performed"] is False
assert record["scientific_runtime_authorized"] is False
assert record["inferential_decision"] is None
```

## Validation and identity

Active node IDs are sorted numerically, retaining isolates and holes from
deleted nodes. Removed nodes are excluded; the ID bound is not the active
node count. At most 1,000 active nodes are supported, matching the project
planner. The optional `labels` mapping must cover exactly the active integer
IDs; Boolean keys, missing/extra keys, duplicate labels, empty/non-string labels
and NUL characters are refused. Labels are retained exactly, without coercion
or Unicode normalization. Missing labels remain `None`, rather than invented
external identities.

Directed/weighted graphs, self-loops and duplicate undirected edges are refused.
The adapter scans edges and checks endpoint membership, unique unordered pairs,
edge counts, each active node's degree and active node counts. NetworKit warns
that `addEdge` can insert unsupported multiedges unless checked explicitly;
the adapter therefore does not assume a Graph object is automatically simple.
See the [official Graph API](https://networkit.github.io/dev-docs/python_api/graph.html).

The returned record stores tuples and the existing frozen trade plan, retaining
no graph or caller mapping. Later caller mutations do not alter it. `as_dict`
returns fresh mutable JSON data for export. Do not concurrently mutate the
graph or label mapping while validation runs: this is a snapshot, without an
atomic lock or memory-safety guarantee. No compacting, relabeling, sampler call,
proposed upstream planner call or RNG draw occurs.

## Optional dependency and checks

Base installation and the existing planner CLI still require no NetworKit.
The new `networkit` extra pins NetworKit 11.2.2. This project is distributed
through GitHub release wheels; download the reviewed wheel, verify its checksum
and install it in an isolated environment:

```text
python -m pip install './degree_null_research-0.4.0-py3-none-any.whl[networkit]'
```

No PyPI publication is implied. The extra allows NetworKit's own
declared dependencies; it excludes this project's unrelated fast-workflow psutil
extra. The adapter imports NetworKit only when called. Absence raises an explicit
error. Released 11.2.2 does not expose the proposed `curveballTradePlan` API;
this adapter works without that proposal. The base wheel embeds no NetworKit
source/binary and keeps the authored Apache-2.0 license.

Portable graph-boundary controls use an explicit test double:
`python -B -m unittest discover -s tests -p test_networkit_graph.py`.
Real released-library synthetic controls are separate:
`python -B -m unittest discover -s tests -p test_networkit_graph_live.py`.
They skip when the optional library is absent. The real controls use one thread,
no sampler and no random seed. They validate this input boundary and immutable
planning output, not NetworKit's sampler/RNG or performance. Only selected
small synthetic cases are measured; no full-scale runtime/RSS or power claim
follows. A trade cap remains a count comparison, not an execution limit.

## Separate upstream draft proposal: source checks and pending build

On 2026-10-09 the independently reviewed proposal was opened as
[draft PR1538](https://github.com/networkit/networkit/pull/1538), head
`8035f382de0fd46ea24faa888ae8e4947ebdf4d2`, based on NetworKit commit
`ab420840dbb8a61fcb1ea0d89e5acc44fe66f2ab`. Its 12-file final patch SHA-256 is
`eb99bd9b4ed1b10e6c4d026f3c022fabbea1b65d0766ee098ad59a0a603a5cb3`.
It adds a pure-stdlib degree-list helper and frozen record with a proposed
Cython public import. Eleven helper tests and 27 project-plan comparisons
pass; Cython 3.2.9 translation passes. Translation is not C++ compile/link/runtime
verification of the public extension export or installed distribution, which
remain pending. Automatic CI is being followed for that exact head; no successful
full build or packaging result is claimed here.

The draft is not merged or adopted. It proposes MIT AND Apache-2.0 component
metadata while preserving existing MIT code and explicit Apache notices;
maintainer licensing preference/acceptance remains unresolved. No relicense or
new agreement was accepted. Five tests of an older mutable degree-list overlay
only exercised the source helper; that overlay is superseded and is not this
graph adapter. No upstream acceptance or engineering improvement is established.
None of the proposed code is required or copied into this package: our graph
adapter uses released NetworKit 11.2.2 independently.

The conditional mathematical assumptions, ordinary attempted-trade units,
per-output TV allowance and unchanged native/scientific holds are in
[PLANNER.md](PLANNER.md). The original classroom full-power gate failed and
power remains unmeasured. This additive interface grants no scientific
authorization, backend/RNG/native certification, causal or heuristic advantage,
new mathematical theorem, or dimension13 runtime/compression consequence.
Source fingerprints change in this release: retain the original pinned
environment for earlier saved jobs; do not resume them against this package.
