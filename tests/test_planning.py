"""Exact arithmetic, independent small-state laws and compatibility controls."""
import ast
import contextlib
from dataclasses import FrozenInstanceError
from fractions import Fraction
import itertools
import io
import json
import math
from pathlib import Path
import sys
import subprocess
import tempfile
import tomllib
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "tests/fixtures/v020-kernel.py"
sys.path.insert(0, str(ROOT / "src"))
from degree_null import kernel
from degree_null.inputs import read_network
from degree_null.planning import ORDINARY_KERNEL, curveball_trade_plan
from degree_null import planning_core
from degree_null.planning_cli import main as plan_cli


def frozen_kernel():
    # Compile text in memory: never execute a job or write baseline __pycache__.
    namespace = {"__name__": "frozen_certificate_control", "__file__": str(FIXTURE)}
    exec(compile(FIXTURE.read_text(encoding="utf-8"),
                 namespace["__file__"], "exec"), namespace)
    return namespace


def graph_classes(n):
    pairs = list(itertools.combinations(range(n), 2))
    groups = {}
    for mask in range(1 << len(pairs)):
        edges = frozenset(edge for i, edge in enumerate(pairs) if mask & (1 << i))
        degrees = tuple(sum(v in edge for edge in edges) for v in range(n))
        groups.setdefault(degrees, []).append(edges)
    return groups


def independent_matrix(n, states):
    # Enumerate every pair/subset event without calling any sampler implementation.
    index = {edges: i for i, edges in enumerate(states)}
    pairs = list(itertools.combinations(range(n), 2))
    matrix = []
    for edges in states:
        row = [Fraction(0) for _ in states]
        for a, b in pairs:
            neighbors_a = {v if u == a else u for u, v in edges if a in (u, v)}
            neighbors_b = {v if u == b else u for u, v in edges if b in (u, v)}
            left = neighbors_a - neighbors_b - {b}
            right = neighbors_b - neighbors_a - {a}
            pool = sorted(left | right)
            choices = list(itertools.combinations(pool, len(left)))
            for choice in choices:
                updated = set(edges)
                for v in left:
                    updated.remove(tuple(sorted((a, v))))
                for v in right:
                    updated.remove(tuple(sorted((b, v))))
                updated.update(tuple(sorted((a, v))) for v in choice)
                updated.update(tuple(sorted((b, v))) for v in set(pool) - set(choice))
                row[index[frozenset(updated)]] += Fraction(1, len(pairs) * len(choices))
        matrix.append(row)
    return matrix


def matmul(a, b):
    size = len(a)
    return [[sum((a[i][k] * b[k][j] for k in range(size)), Fraction(0))
             for j in range(size)] for i in range(size)]


def power(matrix, exponent):
    size = len(matrix)
    result = [[Fraction(int(i == j)) for j in range(size)] for i in range(size)]
    while exponent:
        if exponent & 1:
            result = matmul(result, matrix)
        exponent //= 2
        if exponent:
            matrix = matmul(matrix, matrix)
    return result


class PlanningTests(unittest.TestCase):
    def test_portable_frozen_fixture_binding(self):
        import hashlib
        self.assertEqual(hashlib.sha256(FIXTURE.read_bytes()).hexdigest(),
                         "a0c200d7676560fcac2832503beb40eb3cca52b70304f05a938a55b948c5fe5f")

    def test_one_shared_core(self):
        self.assertIs(kernel.certificate, planning_core.certificate)
        self.assertIs(kernel.realize_degrees, planning_core.realize_degrees)
        original = ast.parse(FIXTURE.read_text(encoding="utf-8"))
        factored = ast.parse((ROOT / "src/degree_null/planning_core.py").read_text(encoding="utf-8"))
        old = {n.name: ast.dump(n) for n in original.body if isinstance(n, ast.FunctionDef)}
        new = {n.name: ast.dump(n) for n in factored.body if isinstance(n, ast.FunctionDef)}
        self.assertEqual(set(new), {"validate_graph", "realize_degrees", "forced_unique", "parse_epsilon", "certificate"})
        for name in new:
            self.assertEqual(old[name], new[name])

    def test_frozen_certificate_all_small_graphical_vectors(self):
        frozen = frozen_kernel()["certificate"]
        for n in range(6):
            for degrees in graph_classes(n):
                for epsilon in ("1/10", "1/100", Fraction(1, 32)):
                    with self.subTest(n=n, degrees=degrees, epsilon=epsilon):
                        self.assertEqual(kernel.certificate(list(degrees), epsilon), frozen(list(degrees), epsilon))

    def test_graphicality_independent_all_vectors_through_four(self):
        for n in range(5):
            valid = graph_classes(n)
            for degrees in itertools.product(range(n), repeat=n):
                if degrees in valid:
                    self.assertEqual(curveball_trade_plan(degrees).degrees, degrees)
                else:
                    with self.assertRaises(ValueError):
                        curveball_trade_plan(degrees)

    def test_peeling_never_claims_false_unique_through_five(self):
        for n in range(6):
            for degrees, states in graph_classes(n).items():
                plan = curveball_trade_plan(degrees)
                if plan.forced_unique:
                    self.assertEqual(len(states), 1)
                    self.assertEqual(plan.attempted_pair_trades, 0)

    def test_independent_exact_binary_inequality(self):
        for n, degrees in ((4, [1] * 4), (5, [2] * 5), (26, [2] * 26), (52, [26] * 52), (104, [52] * 104)):
            for epsilon in (Fraction(1, 10), Fraction(1, 1000), Fraction(1, 2**128)):
                plan = curveball_trade_plan(degrees, epsilon)
                bound = math.comb(n * (n - 1) // 2, sum(degrees) // 2)
                # No floating logarithms: independently verify the squared TV envelope.
                self.assertLessEqual(Fraction(bound, 4 * 2**(2 * plan.binary_blocks)), epsilon**2)
                self.assertEqual(plan.attempted_pair_trades, n * (n - 1) // 2 * plan.binary_blocks)

    def test_dyadic_rounding_boundaries(self):
        for exponent in range(1, 25):
            pivot = Fraction(1, 2**(exponent + 1))
            step = Fraction(1, 2**(exponent + 20))
            below = curveball_trade_plan([1] * 4, pivot - step)
            at = curveball_trade_plan([1] * 4, pivot)
            above = curveball_trade_plan([1] * 4, pivot + step)
            self.assertEqual(below.binary_blocks, at.binary_blocks + 1)
            self.assertEqual(at.binary_blocks, above.binary_blocks)

    def test_error_monotonicity(self):
        counts = [curveball_trade_plan([2] * 26, epsilon).attempted_pair_trades
                  for epsilon in ("0.49", "1/10", "1/100", "1/1000")]
        self.assertEqual(counts, sorted(counts))

    def test_exact_decimal_and_fraction_agree(self):
        self.assertEqual(curveball_trade_plan([1] * 4, "0.01"), curveball_trade_plan([1] * 4, Fraction(1, 100)))

    def test_epsilon_refusals(self):
        for value in (True, False, 0.1, float("nan"), None, object()):
            with self.assertRaises(TypeError):
                curveball_trade_plan([1] * 4, value)
        for value in ("0", "1/2", "1", "-1/100", "nan", "1e-1000000000", "1/0", "1" * 402, " 0.1 "):
            with self.assertRaises((ValueError, ZeroDivisionError)):
                curveball_trade_plan([1] * 4, value)

    def test_degree_refusals(self):
        for vector in ([True, 1], [1.0, 1], [-1, 1], [2, 0], [1, 0], [3, 3, 0, 0], [0] * 1001):
            with self.assertRaises(ValueError):
                curveball_trade_plan(vector)
        for vector in (None, "1111", iter([1, 1, 1, 1])):
            with self.assertRaises(TypeError):
                curveball_trade_plan(vector)

    def test_unsupported_kernel_units_refused(self):
        for name in ("global", "GlobalCurveball", "successful_swaps", "edge_switches", "connected_only", "directed", "weighted", "binary_matrix", None):
            with self.assertRaises(ValueError):
                curveball_trade_plan([1] * 4, kernel=name)
        self.assertEqual(curveball_trade_plan([1] * 4, kernel=ORDINARY_KERNEL).as_dict()["kernel"], ORDINARY_KERNEL)

    def test_resource_policy_validation(self):
        for cap in (-1, True, 1.2, "100"):
            with self.assertRaises(ValueError):
                curveball_trade_plan([1] * 4, max_trades=cap)
        for chunk in (0, -1, True, 1.2, "10"):
            with self.assertRaises(ValueError):
                curveball_trade_plan([1] * 4, trade_chunk_size=chunk)

    def test_trade_cap_does_not_truncate_plan(self):
        requested = curveball_trade_plan([1] * 4)
        for cap, fits in ((0, False), (requested.attempted_pair_trades - 1, False),
                          (requested.attempted_pair_trades, True), (10**30, True)):
            plan = curveball_trade_plan([1] * 4, max_trades=cap)
            self.assertIs(plan.within_trade_limit, fits)
            self.assertEqual(plan.attempted_pair_trades, requested.attempted_pair_trades)
            self.assertIsNone(plan.as_dict()["inferential_decision"])
            self.assertFalse(plan.as_dict()["sampling_performed"])
        self.assertIsNone(requested.within_trade_limit)

    def test_unique_and_empty_are_not_inferential_success(self):
        for vector in ([], [0], [1, 1], [3, 1, 1, 1], [0] * 1000):
            plan = curveball_trade_plan(vector, max_trades=0)
            self.assertTrue(plan.forced_unique)
            self.assertEqual(plan.schedule_chunks, 0)
            self.assertEqual(plan.packed_pair_payload_bytes_per_chunk, 0)
            self.assertIsNone(plan.as_dict()["inferential_decision"])
            self.assertFalse(plan.as_dict()["scientific_runtime_authorized"])

    def test_immutable_snapshot_preserves_degree_order(self):
        degrees = [1, 1, 0, 1, 1]
        plan = curveball_trade_plan(degrees)
        degrees[0] = 0
        self.assertEqual(plan.degrees, (1, 1, 0, 1, 1))
        with self.assertRaises(FrozenInstanceError):
            plan.max_trades = 100
        self.assertIsInstance(json.loads(json.dumps(plan.as_dict()))["degrees"], list)

    def test_chunk_payload_accounting(self):
        plan = curveball_trade_plan([1] * 4, trade_chunk_size=7)
        self.assertEqual(plan.schedule_chunks, (plan.attempted_pair_trades + 6) // 7)
        self.assertEqual(plan.packed_pair_payload_bytes_per_chunk, 112)
        bound = math.comb(6, 2)
        self.assertGreaterEqual(plan.as_dict()["state_bound_integer_payload_bytes_upper"], (bound.bit_length() + 7) // 8)

    def test_planner_does_not_call_backends(self):
        with patch.object(kernel, "get_networkit", side_effect=AssertionError("must not import backend")), \
             patch.object(kernel, "reference_run", side_effect=AssertionError("must not sample")):
            curveball_trade_plan([1] * 4)

    def test_synthetic_labels_and_isolates(self):
        network = read_network(ROOT / "examples/synthetic-edges.csv", vertices=ROOT / "examples/synthetic-vertices.json")
        self.assertEqual(network["labels"], ["node-001", "node-002", "node-003", "node-004", "isolated-A", "isolated-B"])
        self.assertEqual(network["degrees"], [1, 1, 1, 1, 0, 0])
        plan = curveball_trade_plan(network["degrees"], "1/100", max_trades=100)
        self.assertFalse(plan.within_trade_limit)

    def test_native_gates_and_sources_unchanged(self):
        import hashlib
        protected = json.loads((ROOT / "tests/fixtures/v020-protected-sha256.json").read_text(encoding="utf-8"))
        self.assertEqual(protected["baseline_commit"], "9319b8289617a6a08aeb528000bddff4da7ca121")
        for name, expected in protected["files"].items():
            self.assertEqual(hashlib.sha256((ROOT / name).read_bytes()).hexdigest(), expected, name)

    def test_standalone_record_provenance(self):
        record = curveball_trade_plan([1] * 4).as_dict()
        self.assertEqual(record["schema_version"], 1)
        self.assertEqual(record["planner_baseline_commit"], "9319b8289617a6a08aeb528000bddff4da7ca121")
        self.assertEqual(record["operator_input_commit"], planning_core.SOURCE_COMMIT)
        self.assertIn("Apache-2.0", record["code_license"])

    def test_optional_dependencies_not_imported_in_fresh_process(self):
        code = '''import builtins, json, sys
sys.path.insert(0, sys.argv[1])
blocked = {"networkit", "numpy", "scipy", "psutil", "networkx", "tabulate"}
original = builtins.__import__
def guard(name, *args, **kwargs):
    if name.split(".")[0] in blocked:
        raise AssertionError("optional dependency import attempted: " + name)
    return original(name, *args, **kwargs)
builtins.__import__ = guard
from degree_null.planning import curveball_trade_plan
plan = curveball_trade_plan([1,1,1,1,0,0], "1/100", max_trades=100)
print(json.dumps({"loaded_optional": sorted(blocked & set(sys.modules)),
                  "trades": plan.attempted_pair_trades,
                  "authorized": plan.as_dict()["scientific_runtime_authorized"]}))
'''
        completed = subprocess.run([sys.executable, "-B", "-c", code, str(ROOT / "src")],
                                   capture_output=True, text=True, timeout=10)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        record = json.loads(completed.stdout)
        self.assertEqual(record["loaded_optional"], [])
        self.assertEqual(record["trades"], 150)
        self.assertFalse(record["authorized"])

    def test_independent_small_state_transition_and_budget_laws(self):
        for n, degrees in ((4, (1,) * 4), (4, (2,) * 4), (5, (1, 1, 1, 1, 0)), (5, (2,) * 5)):
            states = graph_classes(n)[degrees]
            matrix = independent_matrix(n, states)
            for i, row in enumerate(matrix):
                self.assertEqual(sum(row), 1)
                self.assertGreater(row[i], 0)  # unchanged trades must count
                for j in range(len(states)):
                    self.assertEqual(matrix[i][j], matrix[j][i])
            plan = curveball_trade_plan(degrees, "1/100")
            evolved = power(matrix, plan.attempted_pair_trades)
            stationary = Fraction(1, len(states))
            for row in evolved:
                self.assertLessEqual(sum(abs(x - stationary) for x in row) / 2, plan.epsilon)

    def test_public_api_and_registered_entry_point(self):
        import degree_null
        self.assertIs(degree_null.curveball_trade_plan, curveball_trade_plan)
        metadata = tomllib.loads((ROOT / "pyproject.toml").read_text(encoding="utf-8"))
        self.assertEqual(metadata["project"]["scripts"]["curveball-plan"], "degree_null.planning_cli:main")
        self.assertEqual(metadata["project"]["version"], degree_null.__version__)
        self.assertEqual(degree_null.__version__, "0.4.0")

    def test_cli_exceeded_cap_is_distinct_from_success(self):
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            code = plan_cli(["--degrees", "[1,1,1,1,0,0]", "--epsilon", "1/100", "--max-trades", "100"])
        self.assertEqual(code, 3)
        record = json.loads(stdout.getvalue())
        self.assertEqual(record["attempted_pair_trades"], 150)
        self.assertEqual(record["status"], "planned_exceeds_trade_limit")
        self.assertIsNone(record["inferential_decision"])
        self.assertFalse(record["scientific_runtime_authorized"])

    def test_cli_file_and_within_cap(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "degrees.json"
            path.write_text("[1,1,1,1,0,0]", encoding="utf-8")
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                code = plan_cli(["--degrees-file", str(path), "--epsilon", "1/100", "--max-trades", "150"])
            self.assertEqual(code, 0)
            record = json.loads(stdout.getvalue())
            self.assertEqual(record["degrees"], [1, 1, 1, 1, 0, 0])
            self.assertTrue(record["within_trade_limit"])
            self.assertFalse(record["sampling_performed"])

    def test_cli_invalid_inputs_and_models(self):
        for args in (["--degrees", "not-json"], ["--degrees", "{}"],
                     ["--degrees", "[1,1,1,1]", "--kernel", "GlobalCurveball"],
                     ["--degrees", "[1,1,1,1]", "--epsilon", "1e-1000000000"],
                     ["--degrees", "[1,1,1,1]", "--max-trades", "-1"],
                     ["--degrees", "[1,1,1,1]", "--trade-chunk-size", "0"]):
            stderr = io.StringIO()
            with contextlib.redirect_stderr(stderr):
                self.assertEqual(plan_cli(args), 2)
            record = json.loads(stderr.getvalue())
            self.assertEqual(record["status"], "planning_error")
            self.assertFalse(record["sampling_performed"])
            self.assertIsNone(record["inferential_decision"])

    def test_cli_input_byte_and_encoding_limits(self):
        for raw in (b" " * 16385, b"\xff"):
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "bad.json"
                path.write_bytes(raw)
                stderr = io.StringIO()
                with contextlib.redirect_stderr(stderr):
                    self.assertEqual(plan_cli(["--degrees-file", str(path)]), 2)
                self.assertFalse(json.loads(stderr.getvalue())["sampling_performed"])

    def test_cli_zero_trade_plan_makes_no_decision(self):
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            self.assertEqual(plan_cli(["--degrees", "[]", "--max-trades", "0"]), 0)
        record = json.loads(stdout.getvalue())
        self.assertEqual(record["attempted_pair_trades"], 0)
        self.assertIsNone(record["inferential_decision"])
        self.assertFalse(record["scientific_runtime_authorized"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
