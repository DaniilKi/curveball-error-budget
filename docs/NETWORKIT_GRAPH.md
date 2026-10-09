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

## Separate upstream draft proposal: current validation

Checked on 2026-10-09: [draft PR #1538](https://github.com/networkit/networkit/pull/1538)
is open, unmerged, with no maintainer review/acceptance recorded. Published head
is `6c6eda3a8408f79c59a07c5e1f711fdb965dabc4`, based on
`ab420840dbb8a61fcb1ea0d89e5acc44fe66f2ab`. This proposal supplies a degree-list
helper and frozen record with a compiled public import; it is separate from our
Graph adapter using released 11.2.2. The older mutable degree-list overlay is
superseded and is not this graph/node/label/isolate validation.

[Main CI](https://github.com/networkit/networkit/actions/runs/37882567526)
completed successfully with 22 passing jobs; source-built public-export tests
passed on Linux, macOS arm64 and Windows. The
[wheel workflow](https://github.com/networkit/networkit/actions/runs/37882567527)
also succeeded (six successful job statuses plus one skip). This does not mean
six verified platform wheels: the Linux aarch64 wheel-build step was skipped on PR.

The [targeted Linux x86_64 CPython 3.15 repaired-wheel check](https://github.com/networkit/networkit/actions/runs/37882567527/job/113665356775)
actually passed archive and installed LICENSE/NOTICE byte hashes, a fresh
temporary-venv install outside the checkout, compiled/module origins, public
planner count/cap/type/immutability and component metadata. It invoked no sampler.
Independent review accepted this evidence. CI checked out merge commit
`4ff67065e45a2e238e1bf723de6cba17dc407eb3`; its tree equals the published head's
tree. This tested development wheel is not the released 11.2.2 dependency.

PR artifact uploads remain master-only: the wheel digest is recorded in CI,
without a locally preserved wheel/sdist archive or independent sdist byte audit.
Setuptools licensing deprecations and a package-discovery warning remain in logs.
One [authorized workflow-feedback request](https://github.com/networkit/networkit/pull/1538#issuecomment-6074562014)
links our tested tutorial. No maintainer response was recorded at this check;
its earlier CI-status paragraph is a dated snapshot, superseded by the terminal
results above.

The draft proposes MIT AND Apache-2.0 component metadata and explicit Apache
notices alongside unchanged MIT code. Maintainer licensing preference and API
acceptance remain unresolved; no rightsholder grant or relicense is assumed.
Passing tests is not upstream adoption, a sampler-law/PRNG certificate, scientific
authorization or a performance advantage. None of the proposed code is required
or copied into our released Graph adapter.

The conditional mathematical assumptions, ordinary attempted-trade units,
per-output TV allowance and unchanged native/scientific holds are in
[PLANNER.md](PLANNER.md). The original classroom full-power gate failed and
power remains unmeasured. This additive interface grants no scientific
authorization, backend/RNG/native certification, causal or heuristic advantage,
new mathematical theorem, or dimension13 runtime/compression consequence.
Source fingerprints change in this release: retain the original pinned
environment for earlier saved jobs; do not resume them against this package.
