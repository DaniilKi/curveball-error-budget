import GenericTVLite
import CurveballTransitionCore

namespace CurveballVerified
noncomputable section
open OAI.Problem315 OAI.Problem315.PairResampling CurveballAssurance
open scoped BigOperators RealInnerProductSpace
attribute [local instance] Classical.propDecidable

theorem fiberStates_eq {n : Nat} {d : Fin n → Nat} {a : Finset (Fin n)}
    {G H : GraphState n d} (h : SameFiber a G.val H.val) :
    fiberStates a G = fiberStates a H := by
  ext K
  simp only [mem_fiberStates]
  exact ⟨fun hGK => h.symm.trans hGK, fun hHK => h.trans hHK⟩

theorem pairKernel_symmetric {n : Nat} {d : Fin n → Nat}
    (a : Finset (Fin n)) (G H : GraphState n d) :
    pairKernel a G H = pairKernel a H G := by
  by_cases h : SameFiber a G.val H.val
  · simp only [pairKernel, h, h.symm, ite_true, fiberStates_eq h]
  · have h' : ¬ SameFiber a H.val G.val := fun hh => h hh.symm
    simp [pairKernel, h, h']

theorem pairKernel_apply {n : Nat} {d : Fin n → Nat}
    (a : Finset (Fin n)) (f : GraphState n d → ℝ) (G : GraphState n d) :
    (∑ H, pairKernel a G H * f H) =
      expectation n d a (WithLp.toLp 2 f) G := by
  rw [expectation_eq_average]
  change (∑ H, pairKernel a G H * f H) =
    (∑ H ∈ fiberStates a G, f H) / (fiberStates a G).card
  rw [Finset.sum_div]
  unfold fiberStates
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro H _
  by_cases h : SameFiber a G.val H.val <;>
    simp [pairKernel, fiberStates, h, div_eq_mul_inv, mul_comm]

theorem transition_apply {n : Nat} {d : Fin n → Nat}
    (f : GraphState n d → ℝ) (G : GraphState n d) :
    (∑ H, transition n d G H * f H) = curveballApply n d f G := by
  unfold transition curveballApply
  simp_rw [div_mul_eq_mul_div, Finset.sum_mul]
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  simp_rw [pairKernel_apply]

theorem transition_symmetric (n : Nat) (d : Fin n → Nat) :
    (transition n d).IsSymm := by
  apply Matrix.IsSymm.ext
  intro G H
  unfold transition
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact pairKernel_symmetric a H G

theorem transition_rows {n : Nat} {d : Fin n → Nat} (hn : 2 ≤ n)
    (G : GraphState n d) : ∑ H, transition n d G H = 1 := by
  have hc : (0 : ℝ) < n.choose 2 := by exact_mod_cast Nat.choose_pos hn
  have he (a : Finset (Fin n)) :
      expectation n d a (WithLp.toLp 2 (fun _ : GraphState n d => (1 : ℝ))) =
        WithLp.toLp 2 (fun _ : GraphState n d => (1 : ℝ)) :=
    (expectation_eq_self_iff a _).mpr (constant_mem a 1)
  have h := transition_apply (fun _ : GraphState n d => (1 : ℝ)) G
  simpa [curveballApply, he, pairs, Finset.card_powersetCard, ne_of_gt hc] using h

theorem expectation_positive {n : Nat} {d : Fin n → Nat}
    (a : Finset (Fin n)) (f : StateSpace n d) :
    0 ≤ ⟪f, expectation n d a f⟫ := by
  have h := expectation_isSymmetric a f (expectation n d a f)
  change ⟪expectation n d a f, expectation n d a f⟫ =
    ⟪f, expectation n d a (expectation n d a f)⟫ at h
  rw [expectation_idempotent] at h
  rw [← h, real_inner_self_eq_norm_sq]
  exact sq_nonneg _

theorem transition_positive {n : Nat} {d : Fin n → Nat}
    (f : GraphState n d → ℝ) :
    0 ≤ ∑ G, f G * ∑ H, transition n d G H * f H := by
  simp_rw [transition_apply, curveballApply, ← mul_div_assoc, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_comm]
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro a _
  simpa only [state_inner] using expectation_positive a (WithLp.toLp 2 f)

theorem transition_gap {n : Nat} {d : Fin n → Nat} (hn : 4 ≤ n)
    (f : GraphState n d → ℝ) (hf : ∑ G, f G = 0) :
    (1 / (n.choose 2 : ℝ)) * (∑ G, (f G) ^ 2) ≤
      ∑ G, f G * (f G - ∑ H, transition n d G H * f H) := by
  have hc : (0 : ℝ) < n.choose 2 := by exact_mod_cast Nat.choose_pos (by omega : 2 ≤ n)
  have h := generator_centered_poincare_unconditional hn (WithLp.toLp 2 f) hf
  rw [OAI.Problem315.Analytic.euclidean_norm_sq_eq_sum, state_inner] at h
  simp_rw [generator_apply_eq_scaled_curveball hn] at h
  have hs : (∑ G, f G * ((n.choose 2 : ℝ) * (f G - curveballApply n d f G))) =
      (n.choose 2 : ℝ) * ∑ G, f G * (f G - curveballApply n d f G) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro G _
    ring
  rw [hs] at h
  simp_rw [transition_apply]
  rw [one_div, ← div_eq_inv_mul]
  exact (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using h)

/-- TV bound for the powers of the very same full-fiber transition matrix. -/
theorem ordinary_curveball_tv {n : Nat} {d : Fin n → Nat} (hn : 4 ≤ n)
    (t : Nat) (G : GraphState n d) :
    (1 / 2 : ℝ) * (∑ H, |(transition n d ^ t) G H - 1 / (stateCount n d : ℝ)|) ≤
      Real.sqrt (stateCount n d : ℝ) / 2 *
        Real.exp (-(t : ℝ) / (n.choose 2 : ℝ)) := by
  have hc : (1 : ℝ) ≤ n.choose 2 := by exact_mod_cast Nat.choose_pos (by omega : 2 ≤ n)
  have hg : (1 : ℝ) / n.choose 2 ≤ 1 :=
    (div_le_one (lt_of_lt_of_le (by norm_num) hc)).mpr hc
  have h := OAI.Problem315.Analytic.matrix_tv_bound_of_gap (transition n d)
    (transition_symmetric n d) (transition_rows (by omega : 2 ≤ n)) hg
    transition_positive (transition_gap hn) t G
  simpa only [stateCount, allGraphStates, Finset.card_univ, neg_mul,
    div_mul_eq_mul_div, one_mul, neg_div, mul_one_div] using h

#print axioms transition_apply
#print axioms transition_symmetric
#print axioms transition_rows
#print axioms transition_positive
#print axioms transition_gap
#print axioms ordinary_curveball_tv
end
end CurveballVerified
