# Operational limits and safe resume

Inputs: at most1,000nodes,1,000outputs and20MiB per file. Numeric TV/alpha arguments accept bounded decimals or integer fractions; scientific notation is rejected before constructing potentially enormous denominators.

Default limits:10million attempted trades,60seconds per invocation,256MiB current RSS,128MiB committed output allocation. Hard caps:50million trades and512MiB output allocation. Plans print a rough rate-based runtime estimate before sampling; it is not a runtime promise. Time/current RSS checks occur at chunks of at most10,000compiled trades or1,000reference trades. Package imports, input parsing, planning and final reporting are outside these chunk checks. This is a bounded research guard, not an OS quota.

Each completed graph is saved atomically to its own file, so the batch is not retained in memory. Actual committed-byte checks precede graph saves and reserve8MiB for reports/checkpoints. Atomic staging temporarily adds one graph's bytes. The report's process memory may include an earlier lifetime peak within the same Python process.

Use Ctrl-C, a STOP file or --stop-after to pause. Remove STOP before resume. Never keep/discard completed outputs based on their scientific values. No partial graph is certified or given credit for past trades. Resume verifies source hashes, exact environment versions, immutable plan fingerprint, external label map, contiguous output indices, seed, per-output certificate, graph hash and degrees. The unfinished output is fully replayed from the original graph and original index seed.

Hashes detect changes but are not tamper-proof attestations of execution. Files must stay in the trusted local job directory. Locks prevent two processes writing one job; explicit stale-lock recovery never overrides a live process. NetworKit's RNG is process-global: use separate processes rather than simultaneous Python sampling threads.

Partial jobs receive no complete batch contract or inference. Whole-batch inference requires all original requested outputs and the original frozen statistic/error configuration. Optional stopping, adaptive output selection, selected successful jobs and changing the statistic after seeing results are not covered.

Graph JSON files use integer IDs and labels.json retains exact external labels and isolates. CSV export verifies the stored plan/mapping first, rejects existing target files, and streams label-preserving edge rows. The CSV alone cannot represent isolated nodes.

Local reports intentionally include the user's local input provenance. Do not publish generated jobs or reports without reviewing those paths and the underlying network data for privacy. The release's included example inputs are synthetic.
