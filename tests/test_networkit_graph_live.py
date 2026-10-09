"""Small real released NetworKit Graph controls; no randomization execution."""
from dataclasses import FrozenInstanceError
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
from degree_null import curveball_trade_plan, curveball_trade_plan_from_networkit
RAW_CASES = []
try:
    import networkit as nk
except ImportError:
    nk = None


@unittest.skipIf(nk is None, "optional NetworKit not installed")
class LiveGraphAdapterTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls): nk.setNumberOfThreads(1)

    def test_real_graph_holes_isolates_labels_and_snapshot(self):
        graph = nk.Graph(8)
        graph.addEdge(0, 1); graph.addEdge(2, 3)
        graph.removeNode(4); graph.removeNode(6)
        labels = {node: "synthetic-" + str(node) for node in graph.iterNodes()}
        before = (tuple(graph.iterNodes()), tuple(graph.iterEdges()))
        result = curveball_trade_plan_from_networkit(graph, "1/100", labels=labels, max_trades=100)
        RAW_CASES.append({"case": "holes-labels-isolates", "nodes": list(graph.iterNodes()),
                          "edges": list(graph.iterEdges()), "record": result.as_dict()})
        self.assertEqual(result.node_ids, (0, 1, 2, 3, 5, 7))
        self.assertEqual(result.plan.degrees, (1, 1, 1, 1, 0, 0))
        self.assertEqual(result.plan.attempted_pair_trades, 150)
        self.assertFalse(result.plan.within_trade_limit)
        self.assertEqual(result.networkit_version, nk.__version__)
        self.assertEqual(before, (tuple(graph.iterNodes()), tuple(graph.iterEdges())))
        graph.addEdge(5, 7); labels[0] = "changed"
        self.assertEqual(result.plan.degrees, (1, 1, 1, 1, 0, 0))
        self.assertEqual(result.labels[0], "synthetic-0")
        with self.assertRaises(FrozenInstanceError): result.node_ids = ()

    def test_current_release_without_proposed_planner(self):
        self.assertFalse(hasattr(nk.randomization, "curveballTradePlan"))
        graph = nk.Graph(6); graph.addEdge(0, 1); graph.addEdge(2, 3)
        record = curveball_trade_plan_from_networkit(graph).as_dict()
        RAW_CASES.append({"case": "released-without-proposed-api", "nodes": list(graph.iterNodes()),
                          "edges": list(graph.iterEdges()), "record": record})
        self.assertFalse(record["sampling_performed"])
        self.assertFalse(record["scientific_runtime_authorized"])
        self.assertIsNone(record["inferential_decision"])

    def test_directed_weighted_and_loop_refused(self):
        loop = nk.Graph(6); loop.addEdge(0, 0)
        for graph in (nk.Graph(6, directed=True), nk.Graph(6, weighted=True), loop):
            with self.subTest(graph=graph), self.assertRaises(ValueError):
                curveball_trade_plan_from_networkit(graph)

    def test_real_multiedges_refused(self):
        graph = nk.Graph(6); graph.addEdge(0, 1); graph.addEdge(0, 1)
        with self.assertRaises(ValueError): curveball_trade_plan_from_networkit(graph)

    def test_empty_and_deleted_all_nodes(self):
        for graph in (nk.Graph(0), nk.Graph(3)):
            if graph.numberOfNodes():
                for node in tuple(graph.iterNodes()): graph.removeNode(node)
            result = curveball_trade_plan_from_networkit(graph, labels={})
            RAW_CASES.append({"case": "empty-active-set", "id_bound": graph.upperNodeIdBound(), "record": result.as_dict()})
            self.assertEqual(result.node_ids, ())
            self.assertEqual(result.plan.attempted_pair_trades, 0)

    def test_direct_plan_agreement_on_small_synthetic_graphs(self):
        for edges in ((), ((0, 1),), ((0, 1), (1, 2), (2, 3)),
                      ((0, 1), (0, 2), (1, 2)), ((0, 5), (1, 5), (2, 5), (3, 5), (4, 5))):
            graph = nk.Graph(6)
            for a, b in edges: graph.addEdge(a, b)
            result = curveball_trade_plan_from_networkit(graph, "1/19900", max_trades=314)
            RAW_CASES.append({"case": "small-graph-agreement", "nodes": list(graph.iterNodes()),
                              "edges": list(graph.iterEdges()), "record": result.as_dict()})
            direct = curveball_trade_plan(tuple(graph.degree(n) for n in graph.iterNodes()), "1/19900", max_trades=314)
            self.assertEqual(result.plan, direct)


if __name__ == "__main__": unittest.main()
