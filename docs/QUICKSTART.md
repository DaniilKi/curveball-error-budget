# Plan a Curveball trade budget

Use this tutorial when you want to estimate a trade-count budget for a graph
before deciding whether to run an experiment. It uses the released 0.4.0 package
and NetworKit 11.2.2 with invented data. The planner returns a conditional
mathematical budget; it does not run a sampler or test a scientific hypothesis.

## Install in a separate environment

These commands are for Windows, with Python 3.12 or newer available as `python`
(3.14.1 is excluded by the package). They were checked on Python 3.14.8.
The wheel comes from this project's GitHub release, not a PyPI publication;
NetworKit and its dependencies are installed from PyPI. The URL pins the wheel's
SHA-256 checksum. This optional installation can download sizeable dependencies.

```text
python -m venv .venv
.venv\Scripts\python.exe -m pip install "degree-null-research[networkit] @ https://github.com/DaniilKi/curveball-error-budget/releases/download/v0.4.0/degree_null_research-0.4.0-py3-none-any.whl#sha256=582e48beb245d590e4e11c499d43a047306fba3dfa05198a194a60657e8f068b"
```

On macOS/Linux, the environment's Python is `.venv/bin/python`; those platform
commands were not tested for this tutorial. You do not need a repository checkout
or the proposed upstream NetworKit planner API.

## Make a plan

Save this as `plan_example.py` in the same folder as `.venv`. Each node represents
an invented entity; an edge represents an invented connection.

```python
import networkit as nk
from degree_null import curveball_trade_plan_from_networkit

nk.setNumberOfThreads(1)
graph = nk.Graph(8)
graph.addEdge(0, 1)
graph.addEdge(2, 3)
graph.removeNode(4)
graph.removeNode(6)
labels = {node: f"synthetic-{node}" for node in graph.iterNodes()}

result = curveball_trade_plan_from_networkit(
    graph, "1/100", labels=labels, max_trades=100,
)
print("Active node IDs:", result.node_ids)
print("Degrees:", result.plan.degrees)
print("Labels:", result.labels)
print("Required attempted trades:", result.plan.attempted_pair_trades)
print("Fits cap of 100:", result.plan.within_trade_limit)

larger_cap = curveball_trade_plan_from_networkit(
    graph, "1/100", labels=labels, max_trades=150,
)
print("Fits cap of 150:", larger_cap.plan.within_trade_limit)
record = larger_cap.as_dict()
print("Sampling performed:", record["sampling_performed"])
print("Scientific runtime authorized:", record["scientific_runtime_authorized"])
print("Inferential decision:", record["inferential_decision"])
```

Run it:

```text
.venv\Scripts\python.exe plan_example.py
```

Expected output:

```text
Active node IDs: (0, 1, 2, 3, 5, 7)
Degrees: (1, 1, 1, 1, 0, 0)
Labels: ('synthetic-0', 'synthetic-1', 'synthetic-2', 'synthetic-3', 'synthetic-5', 'synthetic-7')
Required attempted trades: 150
Fits cap of 100: False
Fits cap of 150: True
Sampling performed: False
Scientific runtime authorized: False
Inferential decision: None
```

Nodes 5 and 7 are **isolates**: they exist but have no connections. They remain
in the plan. Deleted nodes 4 and 6 are excluded, without renumbering the others.
Node IDs, degrees and labels use the same ascending active-ID order.

## Read the budget and make a decision

`"1/100"` is an exact error allowance of 0.01, often written epsilon. Under the
assumptions below, it bounds the total variation distance of one output graph
from the target distribution: the probability assigned to any event differs by
at most 0.01. It is not a p-value, confidence level or guarantee of finding a
scientific effect. Use an exact fraction or decimal string, such as `"0.01"`,
instead of a floating-point number or scientific-exponent string.

The count of 150 is a conservative sufficient budget, not the minimum mixing
time. It counts **attempted unordered vertex-pair trades**, including attempts
that leave the graph unchanged. It cannot be translated directly into successful
edge swaps or GlobalCurveball rounds.

If you can afford at most 100 attempted trades, this plan does not fit. The
planner keeps the required count of 150; it does not shorten it to 100. A useful
planning decision is to postpone execution until that budget is affordable, or
explicitly reconsider the allowance and recompute the plan. Setting the cap to
150 passes the count comparison, but establishes no runtime or memory estimate.
It still runs no trades and grants no scientific authorization.

## Check your graph and assumptions

The adapter accepts a simple undirected, unweighted NetworKit Graph with at most
1,000 active nodes. It refuses directed or weighted graphs, self-loops and
duplicate undirected edges. If supplied, labels must cover exactly the active
integer node IDs and be distinct, nonempty strings without NUL characters. If
you omit labels, they remain unspecified. The result is an immutable snapshot;
do not change the graph or labels concurrently while planning.

The target distribution is uniform over labeled simple undirected graphs with
the same degree for each label; disconnected graphs are allowed. This may be
the wrong null model if your experiment requires connected outcomes or other
constraints. The budget assumes the credited ordinary pair-resampling
operator's nonnegative spectrum and spectral-gap bound, together with
independent ideal uniform pair/subset draws.
An integer seed does not establish those assumptions. This planner does not
certify NetworKit's sampler or RNG, provide a faster algorithm, or establish
upstream adoption. The accepted native proof applies to a separate restricted
reference path, not this optional backend.

No inference or power result follows from a sufficient trade count. A valid
scientific comparison also needs an appropriate null, a specified statistic,
independence and controls for selection and multiple testing. The project's
original full-scale power gate failed; power remains unmeasured. See
[the planner contract](PLANNER.md) and [graph adapter details](NETWORKIT_GRAPH.md)
before designing an experiment.

## Tell us what would make planning useful

Researchers can [open a repository issue](https://github.com/DaniilKi/curveball-error-budget/issues/new)
to describe the intended graph and null model, approximate node/edge counts,
an affordable trade budget, and what makes installation or integration difficult.
Please use synthetic examples or aggregate descriptions; do not post private or
sensitive data. Feedback will guide possible extensions. This is an invitation
for practical feedback, not evidence of efficacy or scientific validation.
