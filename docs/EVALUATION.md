# Research evaluation and saved descriptive evidence

The 0.5.0 candidate includes the exact accepted descriptive PWR-002 evidence
and a read-only CLI. Final independent release review remains separate.
The additive `curveball_evaluation` package consumes the maintained empirical
owner's frozen schedule and `analysis.py` output. It does not replace that
producer, draw graphs, calculate another interval, invoke NetworKit or run Lean.
The adapter lives outside `degree_null`. Existing planner and sampler bodies
remain unchanged; the package version string changes in 0.5.0, so job source
fingerprints differ. Preserve original pinned environments for historical jobs.

`FrozenStudy.from_json` checks the original observation/job file digests and
freezes all IDs, groups and seeds. It rejects duplicate seeds and incomplete
output schedules. Original job and observation counts remain the denominators,
including failed or unstarted work. New draws or seed replacement require a new
prospective protocol; they cannot be described as resuming the old experiment.
The maintained PWR-002 schedule uses canonical decimal strings for uint64 seeds;
the adapter accepts those and integer seeds, normalizes their values for duplicate
checks and preserves the exact original JSON digests. Signs, leading zeros,
non-ASCII digits, floating seeds and out-of-range values are rejected.

`StudyHistory` records planned, running, completed, censored, interrupted,
resumed and failed administrative states against retained receipt hashes. A
resumed transition requires a separately reviewed protocol-policy digest.
This records continuation provenance, not permission to replay a failed tape or
an implementation of sampling resume. Completed and failed histories are
terminal. A repair can be recorded as interruption/continuation only when the
reviewed protocol permits it, preserving the old interrupted attempt and cost.

`build_report` binds the existing analyzer's exact bytes, source digest, grouping,
counts, calibrated/power endpoints, history, retained prior evidence and resource
receipts. It currently adapts the PWR-002 analyzer's fixed ten-slot, one-sided
0.005 contract; a different schema or interval family needs an explicit adapter
and review. It validates rates against frozen denominators and copies reviewed
Clopper-Pearson endpoints from that analyzer. It does not verify their numerical
calculation or the graph/oracle law; independent producer/analysis review does.
`rate_bounds` combines lower and upper one-sided endpoints, each at the stated
tail level; do not label that pair as an unadjusted 95% two-sided interval.

Without a review binding matching all report inputs, output is descriptive only.
Even with such a binding, complete reviewed scope additionally requires the
complete scheduled census, completed terminal history, fully audited analysis
and successful terminal guard with known units. Digest matching does not
authenticate a reviewer; the release workflow must obtain the real independent
review before passing that object. Changed analysis, seeds, history, resources
or prior-evidence identities invalidate the binding.
Missing/orphan observations/jobs, truncation, audit errors, primary row formal
holds, paired precision holds, cleanup/measurement notes, unknown-ledger flags
and earlier retained failed execution receipts override a reviewed label. A
successful continuation does not restore the failed original experiment's
confirmatory status. Nonprimary comparison rows retain descriptive scope.

The report preserves cumulative resource snapshots separately rather than
double-counting overlapping all-phase reservations. Keep raw failed receipts and
explicitly missing CPU components; this adapter supplies no independent resource
monitor or hard quota. An administrative non-rejection is not completed evidence
of zero power, a valid hypothesis-test non-rejection or a conditional-on-completion
guarantee. Binomial interval claims retain the protocol's IID operational-job
assumptions; deterministic finite PRNG seeds do not establish those assumptions.
Each group also shows the exact range from assigning all missing outcomes first
non-detection, then detection: `[detections/N, (detections+missing)/N]`. This is an
outcome-sensitivity range, not a confidence interval. Paired/gain diagnostics,
analyzer errors, audit coverage and original hold signals remain visible in both
the machine report and human summary; copied diagnostic gate values cannot
override those holds or authorize inference.

`render_markdown` gives a summary alongside the machine-readable report.
It lists the original negative classroom pilot and failed PWR-002 evidence when
provided as retained identities. The full immutable originals remain outside the
new candidate. No raw input data is copied into this package. Publication needs
separate content, licensing and privacy review of exact accepted artifacts.

All reports hold runtime authorization, TV, ideal-randomness and whole-binary
refinement claims false. Existing planner, legacy research sampler, native proof
assets and reference gates remain unchanged. Historical release versions, assets
and archived published docs remain preserved; current package metadata and
navigation docs change for this candidate.
The generic pairing-law proof and empirical exact-pairing measurements cannot
certify the complete NetworKit/Python/Philox stack.

Lightweight verification from this checkout:

```text
python -I -B -m unittest discover -s tests -p test_evaluation_report.py -v
```

The adapter tests use synthetic JSON; separate study-evidence tests read saved
accepted aggregates. There are no native calls, random draws, NetworKit imports
or compiler work. Verified descriptive outputs and the CLI are integrated in
this 0.5.0 candidate; exact final distribution/publication review remains pending.

## Bundled PWR-002 evidence in 0.5.0

`curveball-evaluation --format json` reads digest-bound accepted review050
analysis/report/receipt and sanitized provenance; it runs no sampling or analysis
pipeline. `load_pwr002()` returns fresh objects. Exact report bytes are preserved;
its archive references describe the private empirical archive, not the wheel.
All 9,018 jobs remain in denominators: 9,017 complete, one failed/censored.
The failed job's 61 candidate charges stay recorded; partial output count/time
are unknown. Administrative seconds=0 is not a runtime measurement.
Missing-outcome fractions are sensitivity ranges, not confidence intervals.
Successful continuation never removes the original failed guard or restores
confirmatory status. Actual process receipt hashes and the derived composite
receipt are distinguished; cumulative resources are not summed twice.
The review receipt's publication_authorized=false describes review050's empirical
scope, not an independent packaging/publication approval. All scientific holds
remain false. Exact final packaging review is separate.
