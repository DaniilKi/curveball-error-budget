import NativeBatchStatistics
import BudgetCoreLite

/- SOURCE-ONLY DRAFT. No compiler slot or acceptance claimed. -/
namespace CurveballVerified
noncomputable section
open CurveballNativeSampling CurveballSubsetVerified
open OAI.Problem315
open scoped BigOperators

theorem native_limits_dimensions (r : Request) (h : withinLimits r = true) :
    4 ≤ r.n ∧ r.n ≤ 26 := by
  have hh := Bool.and_eq_true_iff.mp h
  have hc := of_decide_eq_true hh.1
  exact ⟨hc.1,hc.2.1⟩

theorem native_limits_valid (r : Request) (h : withinLimits r = true) :
    CurveballNative.graphValid r.n r.edges = true :=
  (Bool.and_eq_true_iff.mp h).2

theorem native_plan_budget (r : Request) (h : arithmeticPlan r = true) :
    budgetCheck r.n r.edges.length r.p r.q r.k r.trades = true := by
  have hb := (Bool.and_eq_true_iff.mp h).1
  simpa only [CurveballNative.budgetCheck,budgetCheck,native_choose_eq] using hb

theorem native_plan_scalars (r : Request) (h : arithmeticPlan r = true) :
    0 < r.etaDen ∧ 0 < r.alphaDen ∧ 0 < r.alphaNum ∧
    r.alphaNum < r.alphaDen ∧ r.etaNum*r.alphaDen < r.alphaNum*r.etaDen ∧
    r.b*r.p*r.etaDen ≤ r.etaNum*r.q := by
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).2

theorem native_plan_joint_error (r : Request) (h : arithmeticPlan r = true) :
    (r.b : ℝ) * ((r.p : ℝ) / r.q) ≤ (r.etaNum : ℝ) / r.etaDen := by
  obtain ⟨he,_,_,_,_,hb⟩ := native_plan_scalars r h
  obtain ⟨hp,hpq,_,_,_⟩ := budgetCheck_sound (native_plan_budget r h)
  have hq : 0 < r.q := by omega
  have hqR : (0 : ℝ) < r.q := by exact_mod_cast hq
  have heR : (0 : ℝ) < r.etaDen := by exact_mod_cast he
  have hbR : (r.b : ℝ)*r.p*r.etaDen ≤ (r.etaNum : ℝ)*r.q := by
    exact_mod_cast hb
  calc
    (r.b : ℝ) * ((r.p : ℝ) / r.q) = ((r.b : ℝ)*r.p)/r.q := by ring
    _ ≤ (r.etaNum : ℝ)/r.etaDen := (div_le_div_iff₀ hqR heR).mpr hbR

/-- Only the deterministic native edge-count equality remains as a graph join;
    the integer certificate itself is the exact executed arithmeticPlan gate. -/
theorem native_plan_degree_budget (r : Request) (d : Fin r.n → Nat)
    (h : arithmeticPlan r = true) (hedges : r.edges.length = (∑ v,d v)/2) :
    budgetCheck r.n ((∑ v,d v)/2) r.p r.q r.k r.trades = true := by
  simpa only [hedges] using native_plan_budget r h

#print axioms native_limits_dimensions
#print axioms native_plan_budget
#print axioms native_plan_joint_error
#print axioms native_plan_degree_budget
end
end CurveballVerified
