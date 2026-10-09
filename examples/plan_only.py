"""Synthetic, distributable planning example. Does not import NetworKit or sample."""
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
from degree_null.inputs import read_network
from degree_null.planning import curveball_trade_plan

network = read_network(ROOT / "examples/synthetic-edges.csv",
                       vertices=ROOT / "examples/synthetic-vertices.json")
plan = curveball_trade_plan(network["degrees"], "1/100", max_trades=100,
                           trade_chunk_size=32)
print(json.dumps({"labels": network["labels"], "graph": network["graph"],
                  "plan": plan.as_dict(),
                  "interpretation": "Budget exceeds the declared cap; no sampling or scientific decision. Isolates and labels retained."},
                 indent=2))
