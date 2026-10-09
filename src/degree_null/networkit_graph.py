"""Validate a NetworKit graph and snapshot its labeled ordinary trade plan.

Copyright 2026 DaniilKi contributors. SPDX-License-Identifier: Apache-2.0
No sampler or proposed upstream planner API is invoked.
"""
from collections.abc import Mapping
from dataclasses import dataclass

from .planning import CurveballTradePlan, ORDINARY_KERNEL, curveball_trade_plan


@dataclass(frozen=True, slots=True)
class NetworkitGraphTradePlan:
    """Immutable active-node/label snapshot and immutable project trade plan.

    ``node_ids``, optional ``labels`` and ``plan.degrees`` have identical order.
    No graph or caller-owned mapping is retained. ``as_dict`` returns fresh
    mutable JSON data, whose mutation cannot change this immutable record.
    """
    node_ids: tuple[int, ...]
    labels: tuple[str, ...] | None
    plan: CurveballTradePlan
    networkit_version: str

    def as_dict(self):
        record = self.plan.as_dict()
        record.update({
            "graph_adapter": "degree_null.curveball_trade_plan_from_networkit",
            "graph_backend": "networkit.Graph",
            "networkit_version": self.networkit_version,
            "node_ids": list(self.node_ids),
            "labels": None if self.labels is None else list(self.labels),
            "node_order": "ascending active NetworKit node IDs, including isolates",
            "graph_validation": "simple undirected unweighted snapshot; edge/degrees/counts agree",
            "public_integration_status": "project graph adapter; no upstream adoption or sampler certification implied",
        })
        return record


def curveball_trade_plan_from_networkit(graph, epsilon="1/10", *, labels=None,
                                      kernel=ORDINARY_KERNEL, max_trades=None,
                                      trade_chunk_size=10_000):
    """Validate a real NetworKit Graph and return a planning-only snapshot.

    NetworKit is imported only when called. The tested optional version is
    11.2.2. Active nodes, including isolates and holes left by removed nodes,
    are ordered by ascending ID. If provided, ``labels`` must map exactly those
    integer IDs to distinct nonempty strings (without NUL characters).

    Reject directed/weighted graphs, loops, duplicate edges, inconsistent
    counts/degrees, more than 1,000 active nodes and unsupported kernels. No
    graph changes, sampling, RNG draw, proposed upstream API or authorization
    occurs. Do not mutate the graph or mapping concurrently: this validation
    is a snapshot, not an atomic lock or memory-safety certification.
    """
    if kernel != ORDINARY_KERNEL:
        raise ValueError("only ordinary_uniform_pairs is supported")
    try:
        import networkit
    except ImportError as exc:
        raise RuntimeError("optional NetworKit is unavailable; install the networkit extra") from exc
    if not isinstance(graph, networkit.Graph):
        raise TypeError("graph must be a NetworKit Graph")
    if graph.isDirected() or graph.isWeighted():
        raise ValueError("graph must be undirected and unweighted")
    n = graph.numberOfNodes()
    if type(n) is not int or not 0 <= n <= 1_000:
        raise ValueError("graph must have at most 1,000 active nodes")
    upper = graph.upperNodeIdBound()
    if type(upper) is not int or upper < n:
        raise ValueError("inconsistent node ID bound")
    nodes = []
    for node in graph.iterNodes():
        if len(nodes) >= n or type(node) is not int or not 0 <= node < upper:
            raise ValueError("inconsistent active node IDs")
        if not graph.hasNode(node):
            raise ValueError("active node no longer exists")
        nodes.append(node)
    node_ids = tuple(sorted(nodes))
    if len(node_ids) != n or len(set(node_ids)) != n:
        raise ValueError("inconsistent active node IDs")
    label_values = None
    if labels is not None:
        if not isinstance(labels, Mapping):
            raise TypeError("labels must be a mapping from node IDs to strings")
        label_map = dict(labels)
        if any(type(node) is not int for node in label_map) or set(label_map) != set(node_ids):
            raise ValueError("labels must cover exactly the active integer node IDs")
        label_values = tuple(label_map[node] for node in node_ids)
        if any(type(label) is not str or not label or "\0" in label for label in label_values):
            raise ValueError("labels must be nonempty strings without NUL characters")
        if len(set(label_values)) != n:
            raise ValueError("labels must be distinct")
    m = graph.numberOfEdges()
    if type(m) is not int or not 0 <= m <= n * (n - 1) // 2:
        raise ValueError("edge count is incompatible with a simple graph")
    degrees = dict.fromkeys(node_ids, 0)
    seen = set()
    for index, edge in enumerate(graph.iterEdges()):
        if index >= m:
            raise ValueError("inconsistent edge count")
        a, b = edge
        if type(a) is not int or type(b) is not int or a not in degrees or b not in degrees:
            raise ValueError("edge endpoint is not an active integer node ID")
        if a == b:
            raise ValueError("self-loops are unsupported")
        pair = (min(a, b), max(a, b))
        if pair in seen:
            raise ValueError("parallel edges are unsupported")
        seen.add(pair)
        degrees[a] += 1
        degrees[b] += 1
    if len(seen) != m:
        raise ValueError("inconsistent edge count")
    for node in node_ids:
        if not graph.hasNode(node):
            raise ValueError("active node no longer exists")
        reported = graph.degree(node)
        if type(reported) is not int or reported != degrees[node]:
            raise ValueError("graph degree and edge snapshot disagree")
    if graph.numberOfNodes() != n or graph.numberOfEdges() != m:
        raise ValueError("graph changed during validation")
    plan = curveball_trade_plan(tuple(degrees[node] for node in node_ids), epsilon,
                               kernel=kernel, max_trades=max_trades,
                               trade_chunk_size=trade_chunk_size)
    return NetworkitGraphTradePlan(node_ids, label_values, plan,
                                  str(getattr(networkit, "__version__", "unavailable")))
