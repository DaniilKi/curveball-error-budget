# Retained bounded-prefix pilot

The outer reserved-decoder check formerly traversed the full remaining bit-list.
It now structurally tests only the reserved prefix. Lean accepted equality of
the entire decoder Option result, including failure, returned value and exact
unused suffix, against the frozen decoder body.

The six-vertex request had 32 replicates, 390 attempted trades each and a
174720-byte deterministic tape. All replicas ended in labeled cycle
01,04,12,23,35,45, with zero triangles; the observation had two triangles.
The arithmetic budget/rank flags were true. Scientific rejection remained false:
the deterministic tape did not have the theorem's independent uniform law.

| Retained run | Seconds | Result |
|---|---:|---|
| Original reviewer frozen control | 20-second budget | Censored; concurrent owner compilation could affect timing |
| Prefix pilot | 2.189836 | Completed, exit 0 |
| Same-budget frozen control | 20.022976 | Wall-time censored; owned process cleaned up |
| Predeclared longer frozen control | 27.595212 | Completed, exact stdout/stderr/exit match |

The completed comparison gives a single ordered ratio of 12.601499. Launch,
cache warmth, scheduling and other workload contention were uncontrolled; this
is not a stable distributional benchmark. Seven small paired fixtures matched
exact outputs, including expected cap refusals. Four had slower prefix timings;
the two largest reversals were 0.254898 versus 0.047151 seconds and 0.147159
versus 0.037905 seconds. Negative and censored results are preserved privately.

If the n6 batch completes, calculated outer-check cons visits fall from
17444643840 to 1397760, ratio 87363/7. This excludes all other decoder, graph,
I/O, allocation/GC and process work; it is not a whole-program speed ratio.
The frozen fallback is slower on this pilot. No universal deadline, complexity
improvement for every component, throughput guarantee or dimension-13 runtime
consequence is claimed. The production launcher's 60-second maximum is separate
from the explicit 120-second longer research control.
