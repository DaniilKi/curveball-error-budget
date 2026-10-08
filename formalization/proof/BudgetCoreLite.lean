import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace CurveballVerified

/-- Exact arithmetic on an untrusted plan. No uniqueness shortcut is accepted. -/
def budgetCheck (n m p q k trades : Nat) : Bool :=
  decide (0 < p ∧ 2 * p < q ∧ m ≤ n.choose 2 ∧
    trades = n.choose 2 * k ∧
    (n.choose 2).choose m * q ^ 2 ≤ 4 * p ^ 2 * 2 ^ (2 * k))

theorem budgetCheck_sound {n m p q k trades : Nat}
    (h : budgetCheck n m p q k trades = true) :
    0 < p ∧ 2 * p < q ∧ m ≤ n.choose 2 ∧
    trades = n.choose 2 * k ∧
    (n.choose 2).choose m * q ^ 2 ≤ 4 * p ^ 2 * 2 ^ (2 * k) := by
  simpa only [budgetCheck, decide_eq_true_eq] using h

/-- The real-number inequality certified by the exact integer check. -/
theorem integer_budget_bound {B p q k : Nat} (hp : 0 < p) (hq : 0 < q)
    (h : B * q ^ 2 ≤ 4 * p ^ 2 * 2 ^ (2 * k)) :
    Real.sqrt (B : ℝ) / 2 * (1 / (2 : ℝ) ^ k) ≤ (p : ℝ) / q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpow : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hi : (B : ℝ) * (q : ℝ) ^ 2 ≤
      4 * (p : ℝ) ^ 2 * ((2 : ℝ) ^ k) ^ 2 := by
    have hh : (B : ℝ) * (q : ℝ) ^ 2 ≤
        4 * (p : ℝ) ^ 2 * (2 : ℝ) ^ (2 * k) := by exact_mod_cast h
    simpa only [Nat.mul_comm 2 k, pow_mul] using hh
  have hs : Real.sqrt (B : ℝ) ≤ 2 * (p : ℝ) * (2 : ℝ) ^ k / q := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [div_pow]
      apply (le_div_iff₀ (sq_pos_of_pos hqR)).mpr
      nlinarith
  calc
    Real.sqrt (B : ℝ) / 2 * (1 / (2 : ℝ) ^ k) ≤
        (2 * (p : ℝ) * (2 : ℝ) ^ k / q) / 2 * (1 / (2 : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hs (by norm_num)) (by positivity)
    _ = (p : ℝ) / q := by field_simp

theorem checked_budget_real_bound {n m p q k trades : Nat}
    (h : budgetCheck n m p q k trades = true) :
    Real.sqrt ((n.choose 2).choose m : ℝ) / 2 * (1 / (2 : ℝ) ^ k)
      ≤ (p : ℝ) / q := by
  obtain ⟨hp, hpq, _, _, hi⟩ := budgetCheck_sound h
  exact integer_budget_bound hp (by omega) hi

/-- Exact conservative rank decision. Counts and rational parameters are untrusted. -/
def rankCheck (b exceed etaNum etaDen alphaNum alphaDen : Nat) : Bool :=
  decide (0 < b ∧ exceed ≤ b ∧ 0 < etaDen ∧ 0 < alphaDen ∧
    0 < alphaNum ∧ alphaNum < alphaDen ∧
    etaNum * alphaDen < alphaNum * etaDen ∧
    (exceed + 1) * alphaDen * etaDen + (b + 1) * etaNum * alphaDen
      ≤ alphaNum * (b + 1) * etaDen)

theorem rankCheck_sound {b exceed etaNum etaDen alphaNum alphaDen : Nat}
    (h : rankCheck b exceed etaNum etaDen alphaNum alphaDen = true) :
    (exceed + 1 : ℝ) / (b + 1) + (etaNum : ℝ) / etaDen
      ≤ (alphaNum : ℝ) / alphaDen := by
  have hh : 0 < b ∧ exceed ≤ b ∧ 0 < etaDen ∧ 0 < alphaDen ∧
      0 < alphaNum ∧ alphaNum < alphaDen ∧
      etaNum * alphaDen < alphaNum * etaDen ∧
      (exceed + 1) * alphaDen * etaDen + (b + 1) * etaNum * alphaDen
        ≤ alphaNum * (b + 1) * etaDen := by
    simpa only [rankCheck, decide_eq_true_eq] using h
  obtain ⟨_, _, he, ha, _, _, _, hi⟩ := hh
  have heR : (0 : ℝ) < etaDen := by exact_mod_cast he
  have haR : (0 : ℝ) < alphaDen := by exact_mod_cast ha
  have hbR : (0 : ℝ) < (b : ℝ) + 1 := by positivity
  have hiR : ((exceed : ℝ) + 1) * alphaDen * etaDen +
      ((b : ℝ) + 1) * etaNum * alphaDen ≤
      (alphaNum : ℝ) * ((b : ℝ) + 1) * etaDen := by exact_mod_cast hi
  rw [div_add_div _ _ (ne_of_gt hbR) (ne_of_gt heR)]
  apply (div_le_div_iff₀ (mul_pos hbR heR) haR).mpr
  nlinarith

#print axioms budgetCheck_sound
#print axioms integer_budget_bound
#print axioms checked_budget_real_bound
#print axioms rankCheck_sound
end CurveballVerified
