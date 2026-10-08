# Curveball Error Budget

**Degree-preserving Network Comparisons — research prototype v0.1.**

Imagine a friendship network. This tool creates comparison networks in which everyone keeps the same number of friends, but who is connected changes. You can compare a pattern with what happens under that particular reshuffling model. Named nodes and declared isolated nodes are preserved.

The Curveball sampler already exists. This tool adds a conservative, theorem-derived stopping rule, a whole-batch approximation-error budget, checks and reproducible reports. The mathematical contract is **conditional on the source manuscript's undirected operator inequality and ideal independent random draws**. It is not a new sampler, speed breakthrough, established first, or independently machine-verified end-to-end theorem.

## Three commands

Use Python 3.11 or later in your own virtual environment. From a source checkout:

```text
python -m pip install --only-binary=:all: -r requirements-lock.txt
python run.py plan --input examples/friendships.csv --vertices examples/people.txt --samples 99 --tv 1/100
python run.py run --input examples/friendships.csv --vertices examples/people.txt --samples 99 --tv 1/100 --statistic triangles --predeclared --output my-comparison
```

Open `my-comparison/report.html` locally, or read `report.txt`. No web service, account or internet is needed after installation. The synthetic example has two groups of three friends and an isolated person. It is not personal data.

Install the package with `python -m pip install .`, or install its release wheel. The installed `degree-null` command has the same subcommands as `python run.py`. The first release targets GitHub source/wheel installation; there is no PyPI publication or credential requirement. Tested platform: Windows AMD64, Python 3.14.8, NetworKit 11.2.2. Other supported Python versions and operating systems require validation.

## What the example reports

The example produced 99 comparison networks, all retaining six degree-two nodes and one isolate. The observed network has two triangles. In the frozen example run, 13 randomized networks had at least that many, giving raw rank score 0.14 and conservative decision score 0.15. At overall alpha target 0.05, the tool **does not reject**. This illustrates the calculation; it does not prove a social pattern meaningful or a null model correct.

## Inputs and outputs

CSV must have exactly `source,target` and two fields per record. UTF-8 labels, spaces and leading zeros are retained. Use `--format edgelist` for two whitespace-separated labels per line. Inputs are explicitly declared simple, undirected and unweighted. Two columns alone cannot reveal direction.

Supply `--vertices` to retain isolates: one label per line, or a JSON array of strings declaring the complete vertex universe. Every edge endpoint must be in it. Without it, only edge endpoints are known, and the report says so. Self-loops, repeated or reversed duplicate edges, extra/weight columns, duplicate vertex labels, `--weighted` and `--directed` are rejected. Nothing is silently converted.

Graphs are saved one per JSON file. `labels.json` supplies the exact external label mapping, including isolates. Other files record input hashes, frozen configuration, seeds, package versions, source pin, timing, memory and invariant checks.

```text
python run.py export --job my-comparison --index 0 --output comparison.csv
python run.py resume --job my-comparison
```

An edge CSV alone cannot describe isolates; retain the mapping. Resume validates the plan, mapping and finished graph files. Interrupted graphs are replayed from the original input, original seed and full schedule. Partial jobs have **no whole-batch certificate or inferential result**.

## Interpreting the error budget

`--tv 1/100` is the **total batch** approximation budget, divided across outputs. Under the stated theorem and randomness assumptions it bounds event-probability differences from ideal independent uniform fixed-degree graphs. It does not mean 1% of edges change, eliminate Monte Carlo uncertainty, validate scientific assumptions or prove causation.

For the optional predeclared upper-tail triangle test, `--alpha 1/20` means an overall target of 0.05. With batch TV 0.01, the raw rank cutoff is 0.04. The reported conservative decision score is `min(1, raw rank score + TV)`. This is not an exact p-value from a perfect sampler, nor a 95% confidence interval. The observed graph must itself follow the fixed-degree null, and the statistic must have been selected before inspecting it or choosing results. Multiple tests and selected seeds/batches need separate treatment.

The declaration flag records your claim; software cannot verify predeclaration. Disconnected comparison graphs are legitimate. Small batches may be too coarse to reject at the requested target; the plan warns.

## Bounded research jobs

The plan prints trade counts and a rough runtime estimate before sampling. Defaults: 10 million total trades, 60 seconds per invocation, 256 MiB current RSS and 128 MiB output allocation. Limits are checked at chunk boundaries, not enforced as OS quotas. Input parsing, imports and report generation are outside the internal sampler timer. Hard prototype bounds and exact cancellation/resume behavior are in [the operational guide](docs/OPERATIONS.md).

Ctrl-C, a `STOP` file or `--stop-after 2` can pause a job. Remove `STOP` before resuming. Never choose which completed outputs to keep based on their values. A stale lock requires explicit `--recover-stale-lock`; live locks are not overridden.

## Theory, evidence and attribution

See [the conditional derivation](docs/THEORY.md), [validation scope](docs/VALIDATION.md), [provenance and AI assistance](docs/PROVENANCE.md), and [dependency licensing](docs/THIRD_PARTY.md). Run `python tests/test_tool.py` for bounded tests.

The addition is a short ordinary-undirected Curveball corollary and careful software integration. [Fu–Qin–Wang](https://arxiv.org/html/2606.22636v2) already provide a related universal row-pair binary-matrix/bipartite gap. Ordinary graph Curveball and efficient implementations are prior [2016/2018 work](https://arxiv.org/abs/1609.05137v3) and [ESA2018](https://arxiv.org/html/1804.08487v2). No equally general practical undirected epsilon wrapper surfaced in the bounded search; global priority remains unestablished.

Authored source and synthetic examples: **Apache-2.0**. Dependencies retain their own licenses and are installed separately. No third-party binaries, private logs, personal networks or credentials are included.
