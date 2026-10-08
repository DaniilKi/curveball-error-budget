import CurveballTVLite
import StateCountLite
import BudgetCoreLite

namespace CurveballVerified
noncomputable section
open OAI.Problem315
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem exp_neg_nat_le_binary (k : Nat) :
    Real.exp (-(k : ℝ)) ≤ 1 / (2 : ℝ) ^ k := by
  have hlarge : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hbase : Real.exp (-1) ≤ (1 : ℝ) / 2 := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hlarge
  have h := pow_le_pow_left₀ (Real.exp_nonneg (-1)) hbase k
  simpa [← Real.exp_nat_mul, one_div_pow] using h

/-- An accepted integer certificate bounds actual powers of the existing
    ordinary mathematical kernel. This theorem contains no TV-bound hypothesis. -/
theorem checked_curveball_tv {n : Nat} {d : Fin n → Nat} (hn : 4 ≤ n)
    (G : GraphState n d) {p q k trades : Nat}
    (hcheck : budgetCheck n ((∑ v, d v) / 2) p q k trades = true) :
    (1 / 2 : ℝ) * (∑ H, |(transition n d ^ trades) G H -
      1 / (stateCount n d : ℝ)|) ≤ (p : ℝ) / q := by
  obtain ⟨_, _, _, ht, _⟩ := budgetCheck_sound hcheck
  rw [ht]
  have hc : (0 : ℝ) < n.choose 2 := by exact_mod_cast Nat.choose_pos (by omega : 2 ≤ n)
  have hexp : -((n.choose 2 * k : Nat) : ℝ) / (n.choose 2 : ℝ) = -(k : ℝ) := by
    push_cast
    field_simp
  have htv := ordinary_curveball_tv hn (n.choose 2 * k) G
  rw [hexp] at htv
  have hs : Real.sqrt (stateCount n d : ℝ) ≤
      Real.sqrt ((n.choose 2).choose ((∑ v, d v) / 2) : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast state_count_choose_bound n d)
  calc
    _ ≤ Real.sqrt (stateCount n d : ℝ) / 2 * Real.exp (-(k : ℝ)) := htv
    _ ≤ Real.sqrt ((n.choose 2).choose ((∑ v, d v) / 2) : ℝ) / 2 *
        (1 / (2 : ℝ) ^ k) := by
      exact mul_le_mul (div_le_div_of_nonneg_right hs (by norm_num))
        (exp_neg_nat_le_binary k) (Real.exp_nonneg _) (by positivity)
    _ ≤ (p : ℝ) / q := checked_budget_real_bound hcheck

#print axioms exp_neg_nat_le_binary
#print axioms checked_curveball_tv
end
end CurveballVerified
