import FiniteProbability

namespace CurveballVerified
noncomputable section
open scoped BigOperators

/-- The observation has law p; the replicate law may depend on that observation.
    This dependence is retained instead of silently assuming joint independence. -/
def conditionalLaw {α β : Type} [Fintype α] [Fintype β]
    (p : FiniteLaw α) (q : α → FiniteLaw β) : FiniteLaw (α × β) where
  mass x := p.mass x.1 * (q x.1).mass x.2
  nonnegative x := mul_nonneg (p.nonnegative _) ((q x.1).nonnegative _)
  normalized := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, FiniteLaw.normalized, mul_one]
    exact p.normalized

theorem tv_conditional {α β : Type} [Fintype α] [Fintype β]
    (p : FiniteLaw α) (q r : α → FiniteLaw β) :
    tv (conditionalLaw p q) (conditionalLaw p r) =
      ∑ x, p.mass x * tv (q x) (r x) := by
  unfold tv
  simp only [conditionalLaw, Fintype.sum_prod_type]
  simp_rw [← mul_sub, abs_mul, abs_of_nonneg (p.nonnegative _)]
  simp_rw [← Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem tv_conditional_bound {α β : Type} [Fintype α] [Fintype β]
    (p : FiniteLaw α) (q r : α → FiniteLaw β) (ε : ℝ)
    (h : ∀ x, tv (q x) (r x) ≤ ε) :
    tv (conditionalLaw p q) (conditionalLaw p r) ≤ ε := by
  rw [tv_conditional]
  calc
    (∑ x, p.mass x * tv (q x) (r x)) ≤ ∑ x, p.mass x * ε :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (p.nonnegative x)
    _ = ε := by rw [← Finset.sum_mul, p.normalized, one_mul]

/-- Conditional independent replicates accumulate at most b times the per-run
    TV error, with the common observed graph preserved in both joint laws. -/
theorem conditional_batch_tv {α β : Type} [Fintype α] [Fintype β]
    (p : FiniteLaw α) (q r : α → Nat → FiniteLaw β) (ε : ℝ)
    (h : ∀ x j, tv (q x j) (r x j) ≤ ε) (b : Nat) :
    tv (conditionalLaw p (fun x => batchLaw (q x) b))
       (conditionalLaw p (fun x => batchLaw (r x) b)) ≤ (b : ℝ) * ε := by
  apply tv_conditional_bound
  intro x
  exact tv_batch_constant (q x) (r x) ε (h x) b

#print axioms tv_conditional
#print axioms tv_conditional_bound
#print axioms conditional_batch_tv
end
end CurveballVerified
