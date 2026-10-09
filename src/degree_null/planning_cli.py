"""Dedicated planning-only entry point; no sampler execution or authorization.

Copyright 2026 DaniilKi contributors. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import json
from pathlib import Path
import sys

from .planning import ORDINARY_KERNEL, curveball_trade_plan

DEGREE_INPUT_BYTES = 16_384


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Plan ordinary Curveball attempted trades under explicit ideal assumptions; never samples or grants scientific authorization.")
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--degrees", help="JSON degree array in label order, including isolates")
    source.add_argument("--degrees-file", type=Path, help="UTF-8 JSON degree array, at most 16 KiB")
    parser.add_argument("--epsilon", default="1/10", help="exact per-output TV allowance, e.g. 1/100")
    parser.add_argument("--kernel", default=ORDINARY_KERNEL,
                        help="only ordinary_uniform_pairs; no global/swap/other-null budget transfer")
    parser.add_argument("--max-trades", type=int, help="optional attempted-trade count cap; no runtime or memory promise")
    parser.add_argument("--trade-chunk-size", type=int, default=10_000,
                        help="hypothetical streaming chunk size for payload estimates")
    args = parser.parse_args(argv)
    try:
        if args.degrees_file is not None:
            if args.degrees_file.stat().st_size > DEGREE_INPUT_BYTES:
                raise ValueError("degree input exceeds 16 KiB limit")
            raw = args.degrees_file.read_bytes()
        else:
            raw = args.degrees.encode("utf-8")
        if len(raw) > DEGREE_INPUT_BYTES:
            raise ValueError("degree input exceeds 16 KiB limit")
        degrees = json.loads(raw.decode("utf-8"))
        plan = curveball_trade_plan(degrees, args.epsilon, kernel=args.kernel,
                                   max_trades=args.max_trades,
                                   trade_chunk_size=args.trade_chunk_size)
        print(json.dumps(plan.as_dict(), indent=2))
        # Exit 0 means a planning record was produced, not scientific success.
        return 3 if plan.within_trade_limit is False else 0
    except (OSError, UnicodeError, ValueError, TypeError, ZeroDivisionError) as error:
        print(json.dumps({"status": "planning_error", "error_type": type(error).__name__,
                          "error": str(error), "sampling_performed": False,
                          "scientific_runtime_authorized": False,
                          "inferential_decision": None}), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
