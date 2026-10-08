# Conditional ordinary-Curveball error contract

The mathematical input is the undirected pair-resampling inequality in OpenAI/math family131 at commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Its mixing section proves the operator inequality and a switch-chain comparison. The ordinary-Curveball corollary below is extracted for this software; it is not explicitly stated there as an implementation API.

Let Ω be the labeled simple undirected graphs with a fixed graphical degree vector, M=|Ω|, and C=binom(n,2). For each vertex pair a, let E_a be uniform conditional resampling of its exclusive neighbors, holding other edges, common neighbors and the mutual edge fixed. Each E_a is an orthogonal projection. Set H=Σ_a(I−E_a). **Assume** the source's H²≥H and that the nullspace is the constants.

Ordinary uniform-pair Curveball is K=C⁻¹Σ_a E_a=I−H/C. K is positive semidefinite and its nonconstant spectral gap is at least 1/C. Thus

`TV(K^t(x,·), uniform) ≤ (1/2) sqrt(M−1) (1−1/C)^t.`

Use the conservative state-count upper bound M≤B=binom(C,m), where m is the number of edges. For nontrivial spaces, C≥2. Define u=ceil(log₂B), v=ceil(log₂(1/(2ε))) and t=C(ceil(u/2)+v). Since (1−1/C)^C≤1/2, this schedule ensures the displayed bound is at most ε. The implementation computes these integers without floating-point logs and checks the exact squared binary inequality.

A sufficient unique-realization test recursively removes isolated or universal vertices. Certified unique spaces use zero trades, including empty and single-node inputs. The test is sufficient; it does not classify every unique degree sequence.

Steps mean **attempted uniform vertex-pair trades**, including identity/no-change trades. The supported kernel is NetworKit11.2.2 ordinary Curveball with uniform pair generation and uniform fixed-size exclusive-subset selection. This formula is not automatically a contract for GlobalCurveball, forced-success variants, directed or weighted graphs, connected-only spaces, or different switch proposals.

For a fixed requested batch of b outputs, each original-input restart receives ε=δ/b. Under independent ideal random draws, product coupling gives batch TV≤Σ ε=δ. Uniformity in the starting observed graph also controls the joint law needed for the rank test.

For a predeclared upper-tail statistic, the ideal conservative rank score is p=(k+1)/(b+1). Under the uniform fixed-degree observed-graph null, its rejection probability at threshold a is at most a, including ties. A batch TV error δ adds at most δ to any event probability. For an overall alpha target α>δ, this tool uses raw threshold α−δ and reports min(1,p+δ), yielding type-I error≤α **under all those assumptions**.

This is not a claim conditional on an arbitrary fixed observed graph, an exact seeded-PRNG theorem, a model-validity guarantee or a multiplicity correction. Optional stopping, adaptive batch/seed/statistic selection and conditioning on selected successful jobs are outside the stated contract. Resume preserves verified finished constituents and replays unfinished ones from the original fixed workflow; it grants no credit to partial chains.

No independent end-to-end formal compilation of this ordinary-Curveball software contract is claimed. Source theorem assurance and formal replay are a separate review gate. The derivation is a modest spectral corollary and implementation integration, not a new chain or new mixing theorem.

Related theory: [Fu–Qin–Wang2026](https://arxiv.org/html/2606.22636v2) provide the universal row-pair gap for binary fixed-margin matrices/bipartite graphs. [Dyer–Greenhill–Ullrich](https://arxiv.org/abs/1301.4055) establish nonnegative heat-bath spectrum. These are prior ingredients/settings, not claims of this project.
