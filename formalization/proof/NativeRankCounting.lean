import ProbabilityProofBundle
import NativeArithmetic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp

namespace CurveballVerified
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def exceedCount {α : Type} (b : Nat) (statistic : α → Nat)
    (x : BatchSpace α (b + 1)) : Nat :=
  (Finset.univ.filter (fun j : Fin b => statistic x.1 ≤ statistic (batchVector b x.2 j))).card

theorem rankCount_observed {α : Type} (b : Nat) (statistic : α → Nat)
    (x : BatchSpace α (b + 1)) :
    rankCount (fun j => statistic (batchVector (b + 1) x j)) 0 = exceedCount b statistic x + 1 := by
  have hr : rankCount (fun j => statistic (batchVector (b + 1) x j)) 0 =
      ∑ j, if statistic (batchVector (b + 1) x 0) ≤
        statistic (batchVector (b + 1) x j) then (1 : Nat) else 0 := by
    simp [rankCount]
  rw [hr,Fin.sum_univ_succ]
  simp [batchVector,exceedCount,add_comm]
  rw [Finset.card_filter]
  rfl

theorem eventMass_mono {α : Type} [Fintype α] (p : FiniteLaw α)
    (E F : α → Prop) [DecidablePred E] [DecidablePred F]
    (h : ∀ x, E x → F x) : eventMass p E ≤ eventMass p F := by
  unfold eventMass
  apply Finset.sum_le_sum
  intro x hx
  by_cases he : E x
  · simp [he,h x he]
  · by_cases hf : F x <;> simp [he,hf,p.nonnegative x]

theorem native_rank_implies_cutoff {α : Type} (b : Nat) (statistic : α → Nat)
    (x : BatchSpace α (b + 1)) (etaNum etaDen alphaNum alphaDen : Nat)
    (h : CurveballNative.rankCheck b (exceedCount b statistic x)
      etaNum etaDen alphaNum alphaDen = true) :
    rankCount (fun j => statistic (batchVector (b + 1) x j)) 0 * (alphaDen * etaDen) ≤
      (alphaNum * etaDen - etaNum * alphaDen) * (b + 1) := by
  have hh : 0 < b ∧ exceedCount b statistic x ≤ b ∧ 0 < etaDen ∧ 0 < alphaDen ∧
      0 < alphaNum ∧ alphaNum < alphaDen ∧
      etaNum * alphaDen < alphaNum * etaDen ∧
      (exceedCount b statistic x + 1) * alphaDen * etaDen +
        (b + 1) * etaNum * alphaDen ≤ alphaNum * (b + 1) * etaDen := by
    simpa only [CurveballNative.rankCheck,decide_eq_true_eq] using h
  obtain ⟨_,_,_,_,_,_,hcut,hi⟩ := hh
  have hc := Nat.sub_add_cancel (Nat.le_of_lt hcut)
  have hm := congrArg (fun z : Nat => z * (b + 1)) hc
  rw [rankCount_observed]
  nlinarith

theorem rational_cutoff_identity {etaNum etaDen alphaNum alphaDen : Nat}
    (he : 0 < etaDen) (ha : 0 < alphaDen)
    (hc : etaNum * alphaDen ≤ alphaNum * etaDen) :
    ((alphaNum * etaDen - etaNum * alphaDen : Nat) : ℝ) / (alphaDen * etaDen) +
      (etaNum : ℝ) / etaDen = (alphaNum : ℝ) / alphaDen := by
  rw [Nat.cast_sub hc]
  push_cast
  have heR : (etaDen : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt he
  have haR : (alphaDen : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha
  field_simp
  ring


#print axioms rankCount_observed
#print axioms native_rank_implies_cutoff
#print axioms rational_cutoff_identity
end
end CurveballVerified
