"""Portable graph-boundary controls with an explicit test double, no backend."""
from dataclasses import FrozenInstanceError
from pathlib import Path
import sys
import types
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
from degree_null.networkit_graph import curveball_trade_plan_from_networkit
from degree_null.planning import curveball_trade_plan


class GraphDouble:
    def __init__(self, nodes=(0, 1, 2, 3, 4, 5), edges=((0, 1), (2, 3)), *, directed=False, weighted=False):
        self.nodes = list(nodes)
        self.edges = list(edges)
        self.directed, self.weighted = directed, weighted
    def isDirected(self): return self.directed
    def isWeighted(self): return self.weighted
    def numberOfNodes(self): return len(self.nodes)
    def upperNodeIdBound(self): return max(self.nodes, default=-1) + 1
    def iterNodes(self): return iter(self.nodes)
    def hasNode(self, node): return node in self.nodes
    def numberOfEdges(self): return len(self.edges)
    def iterEdges(self): return iter(self.edges)
    def degree(self, node): return sum((a == node) + (b == node) for a, b in self.edges)


class GraphAdapterTests(unittest.TestCase):
    def setUp(self):
        self.backend = types.ModuleType("networkit")
        self.backend.Graph = GraphDouble
        self.backend.__version__ = "explicit-portable-test-double"
        self.guard = patch.dict(sys.modules, {"networkit": self.backend})
        self.guard.start()
        self.addCleanup(self.guard.stop)

    def test_active_ids_isolates_and_label_order(self):
        graph = GraphDouble(nodes=(7, 0, 3, 2, 1, 5), edges=((0, 1), (2, 3)))
        labels = {node: "node" + str(node) for node in graph.nodes}
        result = curveball_trade_plan_from_networkit(graph, "1/100", labels=labels, max_trades=100)
        self.assertEqual(result.node_ids, (0, 1, 2, 3, 5, 7))
        self.assertEqual(result.labels, ("node0", "node1", "node2", "node3", "node5", "node7"))
        self.assertEqual(result.plan.degrees, (1, 1, 1, 1, 0, 0))
        self.assertEqual(result.plan, curveball_trade_plan([1, 1, 1, 1, 0, 0], "1/100", max_trades=100))

    def test_immutable_snapshot_and_fresh_json(self):
        graph = GraphDouble()
        labels = {node: str(node) for node in graph.nodes}
        result = curveball_trade_plan_from_networkit(graph, labels=labels)
        graph.edges.clear(); labels[0] = "changed"
        with self.assertRaises(FrozenInstanceError): result.labels = ()
        with self.assertRaises(FrozenInstanceError): result.plan.degrees = ()
        record = result.as_dict(); record["labels"][0] = "changed"; record["degrees"][0] = 100
        self.assertEqual(result.labels[0], "0")
        self.assertEqual(result.plan.degrees[0], 1)
        self.assertEqual(result.as_dict()["degrees"][0], 1)

    def test_no_sampler_or_upstream_api_access(self):
        class Forbidden:
            def __getattr__(self, name): raise AssertionError("randomization accessed")
        self.backend.randomization = Forbidden()
        record = curveball_trade_plan_from_networkit(GraphDouble()).as_dict()
        self.assertFalse(record["sampling_performed"])
        self.assertFalse(record["scientific_runtime_authorized"])
        self.assertIsNone(record["inferential_decision"])

    def test_wrong_type_and_missing_dependency(self):
        with self.assertRaises(TypeError): curveball_trade_plan_from_networkit(object())
        with patch.dict(sys.modules, {"networkit": None}):
            with self.assertRaisesRegex(RuntimeError, "unavailable"):
                curveball_trade_plan_from_networkit(GraphDouble())

    def test_reject_directed_weighted_loops_and_parallel_edges(self):
        for graph in (GraphDouble(directed=True), GraphDouble(weighted=True),
                      GraphDouble(edges=((0, 0),)), GraphDouble(edges=((0, 1), (1, 0)))):
            with self.subTest(graph=vars(graph)), self.assertRaises(ValueError):
                curveball_trade_plan_from_networkit(graph)

    def test_exact_label_keys_and_unique_strings(self):
        base = {n: str(n) for n in range(6)}
        cases = [{}, {**base, 8: "extra"}, {**base, 0: 0}, {**base, 0: ""},
                 {**base, 0: "bad\0label"}, {**base, 0: "1"},
                 {False: "0", **{n: str(n) for n in range(1, 6)}}]
        for labels in cases:
            with self.subTest(labels=labels), self.assertRaises(ValueError):
                curveball_trade_plan_from_networkit(GraphDouble(), labels=labels)
        with self.assertRaises(TypeError):
            curveball_trade_plan_from_networkit(GraphDouble(), labels=["0"] * 6)

    def test_empty_single_unique_and_missing_ids(self):
        for graph in (GraphDouble(nodes=(), edges=()), GraphDouble(nodes=(8,), edges=()),
                      GraphDouble(nodes=(0, 2), edges=((0, 2),))):
            result = curveball_trade_plan_from_networkit(graph)
            self.assertTrue(result.plan.forced_unique)
            self.assertEqual(result.plan.attempted_pair_trades, 0)
            self.assertIsNone(result.labels)

    def test_active_node_limit_not_id_bound_limit(self):
        result = curveball_trade_plan_from_networkit(GraphDouble(nodes=(0, 1_000_000), edges=()))
        self.assertEqual(result.node_ids, (0, 1_000_000))
        self.assertEqual(len(curveball_trade_plan_from_networkit(GraphDouble(nodes=range(1_000), edges=())).node_ids), 1_000)
        with self.assertRaises(ValueError):
            curveball_trade_plan_from_networkit(GraphDouble(nodes=range(1_001), edges=()))

    def test_invalid_kernel_epsilon_and_caps(self):
        for options in ({"kernel": "GlobalCurveball"}, {"epsilon": .01},
                        {"epsilon": "1e-2"}, {"max_trades": True}, {"max_trades": -1}):
            with self.subTest(options=options), self.assertRaises((ValueError, TypeError)):
                curveball_trade_plan_from_networkit(GraphDouble(), **options)

    def test_inconsistent_degree_and_edge_counts(self):
        class WrongDegree(GraphDouble):
            def degree(self, node): return super().degree(node) + 1
        class WrongCount(GraphDouble):
            def numberOfEdges(self): return 1
        class BoolDegree(GraphDouble):
            def degree(self, node): return True
        for graph in (WrongDegree(), WrongCount(), BoolDegree()):
            with self.subTest(kind=type(graph).__name__), self.assertRaises(ValueError):
                curveball_trade_plan_from_networkit(graph)

    def test_invalid_nodes_and_endpoints(self):
        for graph in (GraphDouble(nodes=(0, 0), edges=()), GraphDouble(nodes=(False, 1), edges=()),
                      GraphDouble(edges=((0, 10),)), GraphDouble(edges=((False, 1),))):
            with self.subTest(graph=vars(graph)), self.assertRaises(ValueError):
                curveball_trade_plan_from_networkit(graph)

    def test_snapshot_does_not_modify_graph(self):
        graph = GraphDouble()
        before = (tuple(graph.nodes), tuple(graph.edges))
        curveball_trade_plan_from_networkit(graph)
        self.assertEqual(before, (tuple(graph.nodes), tuple(graph.edges)))


if __name__ == "__main__": unittest.main()
