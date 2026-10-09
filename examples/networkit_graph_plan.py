"""Synthetic released-NetworKit graph planning; no sampling or private data."""
from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
import networkit as nk
from degree_null import curveball_trade_plan_from_networkit

nk.setNumberOfThreads(1)
graph = nk.Graph(8)
graph.addEdge(0, 1)
graph.addEdge(2, 3)
graph.removeNode(4)
graph.removeNode(6)
result = curveball_trade_plan_from_networkit(
    graph, "1/100", labels={n: f"synthetic-{n}" for n in graph.iterNodes()},
    max_trades=100,
)
print(json.dumps(result.as_dict(), indent=2))
