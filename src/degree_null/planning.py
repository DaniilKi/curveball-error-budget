"""Ordinary Curveball planning only; never executes or authorizes sampling.

Copyright 2026 DaniilKi contributors. SPDX-License-Identifier: Apache-2.0
The arithmetic is shared with the existing v0.2.0 certificate, not a new
mixing result. See docs/PLANNER.md for assumptions, attribution and limits.
"""
from dataclasses import dataclass
from fractions import Fraction
import re

from .planning_core import SOURCE_COMMIT, certificate, parse_epsilon

ORDINARY_KERNEL = "ordinary_uniform_pairs"
_EXACT_TEXT = re.compile(r"(?:[0-9]{1,200}(?:/[0-9]{1,200})?|[0-9]{0,200}\.[0-9]{1,200})")


def _exact_epsilon(value):
    # Do not accept binary floating values or unbounded scientific exponents.
    if type(value) is str:
        if len(value) > 401 or _EXACT_TEXT.fullmatch(value) is None:
            raise ValueError("epsilon must be a bounded decimal or integer fraction")
    elif type(value) not in (int, Fraction):
        raise TypeError("epsilon must be an exact Fraction, integer or decimal/fraction string")
    return parse_epsilon(value)


@dataclass(frozen=True)
class CurveballTradePlan:
    """Immutable cost/assumption record for one idealized ordinary chain.

    `within_trade_limit` compares an explicit user count cap only. It is
    neither a runtime/memory prediction nor scientific authorization.
    Packed-pair bytes assume two uint64 endpoints; Python/container overhead
    and graph/kernel working storage are excluded. No backend is imported.
    """

    degrees: tuple[int, ...]
    epsilon: Fraction
    attempted_pair_trades: int
    binary_blocks: int
    state_count_upper_formula: str
    state_count_log2_ceiling: int
    forced_unique: bool
    max_trades: int | None
    trade_chunk_size: int

    @property
    def within_trade_limit(self):
        return None if self.max_trades is None else self.attempted_pair_trades <= self.max_trades

    @property
    def schedule_chunks(self):
        return (self.attempted_pair_trades + self.trade_chunk_size - 1) // self.trade_chunk_size

    @property
    def packed_pair_payload_bytes_per_chunk(self):
        return 16 * min(self.trade_chunk_size, self.attempted_pair_trades)

    def as_dict(self):
        """Return JSON-compatible planning data, with no inferential decision."""
        return {
            "schema_version": 1,
            "status": "planned_within_trade_limit" if self.within_trade_limit is True else
                      "planned_exceeds_trade_limit" if self.within_trade_limit is False else
                      "planned_limit_unspecified",
            "kernel": ORDINARY_KERNEL,
            "planner_baseline_commit": "9319b8289617a6a08aeb528000bddff4da7ca121",
            "operator_input_commit": SOURCE_COMMIT,
            "code_license": "Apache-2.0; retain project attribution and NOTICE",
            "degrees": list(self.degrees),
            "n": len(self.degrees),
            "edges": sum(self.degrees) // 2,
            "epsilon": str(self.epsilon),
            "attempted_pair_trades": self.attempted_pair_trades,
            "trade_units": "attempted unordered vertex-pair resampling trades, including null trades",
            "binary_blocks": self.binary_blocks,
            "state_count_upper_formula": self.state_count_upper_formula,
            "state_count_log2_ceiling": self.state_count_log2_ceiling,
            "state_bound_integer_payload_bytes_upper": (self.state_count_log2_ceiling + 8) // 8,
            "forced_unique": self.forced_unique,
            "max_trades": self.max_trades,
            "within_trade_limit": self.within_trade_limit,
            "schedule_chunks": self.schedule_chunks,
            "trade_chunk_size": self.trade_chunk_size,
            "packed_pair_payload_bytes_per_chunk": self.packed_pair_payload_bytes_per_chunk,
            "cost_scope": "count cap only; payload estimates exclude containers, graph, kernel and integer temporaries; no runtime/RSS promise",
            "model": "uniform labeled simple undirected graphs with exact per-label degrees; disconnected graphs included",
            "assumptions": [
                "for a nontrivial state space, ordinary uniform vertex-pair heat-bath operator has the credited spectral gap at least 1/binom(n,2)",
                "independent ideal uniform pair and fixed-size subset draws",
                "fixed trade count includes every unchanged outcome",
            ],
            "assurance": "conditional mathematical plan; fast backend/PRNG not covered by native Lean proof",
            "scientific_runtime_authorized": False,
            "native_profile": "pending_mainreview; unchanged",
            "sampling_performed": False,
            "inferential_decision": None,
            "public_integration_status": "local planner candidate; public integration not approved",
        }


def curveball_trade_plan(degrees, epsilon="1/10", *, kernel=ORDINARY_KERNEL,
                        max_trades=None, trade_chunk_size=10_000):
    """Plan sufficient attempted ordinary trades under explicit ideal premises.

    Parameters
    ----------
    degrees : list[int] or tuple[int, ...]
        Exact labeled degree vector, including isolates, at most 1,000 entries.
        Entries retain their order. Graphicality is checked by the shared core.
    epsilon : Fraction or exact decimal/fraction string
        Per-output TV allowance strictly between zero and one half. Floating
        inputs are refused rather than interpreted as their binary value.
    kernel : str
        Only ``ordinary_uniform_pairs`` is accepted. Global rounds, successful
        switches, directed/weighted/connected-only/matrix kernels are refused.
    max_trades : int or None
        Optional nonnegative attempted-trade cap; an insufficient cap is
        reported without truncating the mathematically requested count.
    trade_chunk_size : int
        Positive size for a hypothetical streaming trade list cost estimate.

    Returns
    -------
    CurveballTradePlan
        Counts, explicit premises and limited resource comparisons. No graph
        samples or significance verdict are produced. A unique state needs
        zero trades but does not imply a useful significance test.
    """
    if kernel != ORDINARY_KERNEL:
        raise ValueError("only ordinary_uniform_pairs is supported; no global/swap/other-null budget transfer")
    if not isinstance(degrees, (list, tuple)):
        raise TypeError("degrees must be a finite list or tuple, including isolates")
    if max_trades is not None and (type(max_trades) is not int or max_trades < 0):
        raise ValueError("max_trades must be a nonnegative integer or None")
    if type(trade_chunk_size) is not int or trade_chunk_size < 1:
        raise ValueError("trade_chunk_size must be a positive integer")
    exact = _exact_epsilon(epsilon)
    cert = certificate(list(degrees), exact)
    n = len(degrees)
    pairs = n * (n - 1) // 2
    blocks = cert["attempted_pair_trades"] // pairs if pairs else 0
    return CurveballTradePlan(tuple(degrees), exact, cert["attempted_pair_trades"],
                             blocks, cert["state_count_upper_formula"],
                             cert["state_count_log2_ceiling"], cert["forced_unique"],
                             max_trades, trade_chunk_size)
