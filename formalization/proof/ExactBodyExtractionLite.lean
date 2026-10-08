import AnalyticUnorderedBudget


/- BEGIN private normalization wrapper (unverified until successful compilation) -/

/- Private extraction and normalization of existing OpenAI proof ingredients.
   No new spectral estimate or priority claim is made. Upstream source is pinned
   to fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and remains unmodified. -/

namespace CurveballAssurance

noncomputable section
open OAI.Problem315
open OAI.Problem315.PairResampling
open scoped BigOperators RealInnerProductSpace
attribute [local instance] Classical.propDecidable

/-- The manuscript's strong pair-generator estimate, with its critical local
    hypotheses discharged by actual graph-resampling proofs. -/
theorem generator_square_unconditional {n : ℕ} {d : Fin n → ℕ}
    (hn : 4 ≤ n) (f : StateSpace n d) :
    ⟪f, generator n d f⟫ ≤ ⟪generator n d f, generator n d f⟫ := by
  apply generator_square_of_local (by omega) f (fun T hT => tripleGenerator_square f T hT)
  exact disjoint_sum_nonneg_of_named_interaction_budget f
    (fun i j k l h => OAI.Problem315.PairEquality.actual_named_interaction i j k l h f)
    (fun a _ => OAI.Problem315.PairEquality.pair_projection_budget a f)

/-- H ≥ I on the centered subspace, not merely the weaker switch-chain gap. -/
theorem generator_centered_poincare_unconditional {n : ℕ} {d : Fin n → ℕ}
    (hn : 4 ≤ n) (f : StateSpace n d) (hf : ∑ G : GraphState n d, f G = 0) :
    ‖f‖ ^ 2 ≤ ⟪f, generator n d f⟫ :=
  generator_centered_poincare (generator_square_unconditional hn) f hf

/-- Ordinary pair heat bath: uniform unordered pair; uniform full graph fiber,
    including the original assignment. There is no extra laziness or rejection
    of unchanged trades in this definition. -/
def curveballApply (n : ℕ) (d : Fin n → ℕ)
    (f : GraphState n d → ℝ) (G : GraphState n d) : ℝ :=
  (∑ a ∈ pairs n, expectation n d a (WithLp.toLp 2 f) G) /
    (Nat.choose n 2 : ℝ)

def curveballDirichlet (n : ℕ) (d : Fin n → ℕ) (f : GraphState n d → ℝ) : ℝ :=
  uniformInner n d f (fun G => f G - curveballApply n d f G)

theorem curveballApply_eq_fiber_average {n : ℕ} {d : Fin n → ℕ}
    (f : GraphState n d → ℝ) (G : GraphState n d) :
    curveballApply n d f G =
      (∑ a ∈ pairs n, (∑ H ∈ fiberStates a G, f H) / (fiberStates a G).card) /
        (Nat.choose n 2 : ℝ) := by
  unfold curveballApply
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  exact expectation_eq_average a (WithLp.toLp 2 f) G

/-- Explicit link to selecting a uniformly random fixed-size subset of exclusive
    neighbors; the existing graph-fiber equivalence is used, not assumed. -/
theorem pair_expectation_eq_subset_average {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (f : StateSpace n d) :
    expectation n d {i,j} f G =
      (∑ T : OAI.Problem315.PairFiber.Assignment G.val i j,
        f ((OAI.Problem315.PairFiber.stateFiberEquiv G i j hij).symm T).val) /
        (Nat.choose (OAI.Problem315.PairFiber.singletonSet G.val i j).card
          (OAI.Problem315.PairFiber.leftSet G.val i j).card : ℝ) :=
  OAI.Problem315.PairFiber.expectation_eq_assignment_average G i j hij f

theorem generator_apply_eq_scaled_curveball {n : ℕ} {d : Fin n → ℕ}
    (hn : 4 ≤ n) (f : GraphState n d → ℝ) (G : GraphState n d) :
    generator n d (WithLp.toLp 2 f) G =
      (Nat.choose n 2 : ℝ) * (f G - curveballApply n d f G) := by
  have hc : (0 : ℝ) < (Nat.choose n 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos (show 2 ≤ n by omega)
  have hcard : (pairs n).card = Nat.choose n 2 := by
    simp [pairs, Finset.card_powersetCard]
  rw [generator_apply]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, fluctuation_eq_sub, PiLp.sub_apply]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, hcard]
  unfold curveballApply
  field_simp [ne_of_gt hc]

theorem generator_energy_eq_scaled_curveball {n : ℕ} {d : Fin n → ℕ}
    (hn : 4 ≤ n) (f : GraphState n d → ℝ) :
    ⟪WithLp.toLp 2 f, generator n d (WithLp.toLp 2 f)⟫ / (stateCount n d : ℝ) =
      (Nat.choose n 2 : ℝ) * curveballDirichlet n d f := by
  rw [state_inner]
  simp_rw [generator_apply_eq_scaled_curveball hn]
  unfold curveballDirichlet uniformInner uniformAverage allGraphStates
  have hsum : (∑ G : GraphState n d,
      f G * ((Nat.choose n 2 : ℝ) * (f G - curveballApply n d f G))) =
      (Nat.choose n 2 : ℝ) * ∑ G : GraphState n d,
        f G * (f G - curveballApply n d f G) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro G hG
    ring
  rw [hsum]
  ring

/-- Poincaré definition of ordinary Curveball's gap, for every graphical degree
    sequence, without substituting the weak-switch kernel or assuming H ≥ I. -/
theorem ordinary_curveball_gap {n : ℕ} {d : Fin n → ℕ}
    (hn : 4 ≤ n) (hgraph : Graphical n d) (f : GraphState n d → ℝ) :
    (1 : ℝ) / (Nat.choose n 2 : ℝ) * uniformVariance n d f ≤
      curveballDirichlet n d f := by
  have hc : (0 : ℝ) < (Nat.choose n 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos (show 2 ≤ n by omega)
  have h := uniformVariance_le_generator hgraph (generator_square_unconditional hn) f
  rw [generator_energy_eq_scaled_curveball hn] at h
  rw [one_div, ← div_eq_inv_mul]
  apply (div_le_iff₀ hc).mpr
  simpa only [mul_comm] using h

#print axioms generator_square_unconditional
#print axioms generator_centered_poincare_unconditional
#print axioms curveballApply_eq_fiber_average
#print axioms pair_expectation_eq_subset_average
#print axioms ordinary_curveball_gap
#check generator_square_unconditional
#check generator_centered_poincare_unconditional
#check curveballApply_eq_fiber_average
#check pair_expectation_eq_subset_average
#check ordinary_curveball_gap

end
end CurveballAssurance
