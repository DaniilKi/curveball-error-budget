import RankCounting
import Mathlib.Data.Fintype.Pi

namespace CurveballVerified
noncomputable section
open scoped BigOperators

def uniformLaw (α : Type) [Fintype α] [Nonempty α] : FiniteLaw α where
  mass _ := 1 / (Fintype.card α : ℝ)
  nonnegative _ := by positivity
  normalized := by
    have h : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [h]

def reindex {ι α : Type} (e : ι ≃ ι) : (ι → α) ≃ (ι → α) where
  toFun f j := f (e j)
  invFun f j := f (e.symm j)
  left_inv f := by funext j; simp
  right_inv f := by funext j; simp

theorem rankCount_reindex {ι : Type} [Fintype ι] (score : ι → Nat) (e : ι ≃ ι) (i : ι) :
    rankCount (fun j => score (e j)) i = rankCount score (e i) := by
  classical
  unfold rankCount
  apply Finset.card_bij (fun j _ => e j)
  · intro j hj
    simpa using hj
  · intro j hj k hk he
    exact e.injective he
  · intro j hj
    refine ⟨e.symm j, ?_, by simp⟩
    simpa using hj

/-- Uniform fixed-degree observations and independent uniform outputs form the
    uniform finite product law. This proves exchangeability for that law, rather
    than assuming its rank bound. -/
theorem iid_rank_bound {α ι : Type} [Fintype α] [Nonempty α] [Fintype ι] [DecidableEq ι]
    (statistic : α → Nat) (i0 : ι) (p q : Nat) (hq : 0 < q) :
    eventMass (uniformLaw (ι → α))
      (fun x => rankCount (fun j => statistic (x j)) i0 * q ≤ p * Fintype.card ι)
      ≤ (p : ℝ) / q := by
  classical
  apply conservative_rank_bound (uniformLaw (ι → α))
    (fun x j => statistic (x j)) i0 p q hq
  intro i
  let e := Equiv.swap i i0
  unfold eventMass
  apply Fintype.sum_equiv (reindex e)
  intro x
  have hr := rankCount_reindex (fun j => statistic (x j)) e i0
  simp only [e, Equiv.swap_apply_right] at hr
  simp only [uniformLaw, reindex, Equiv.coe_fn_mk]
  simp only [e,hr]

#print axioms rankCount_reindex
#print axioms iid_rank_bound
end
end CurveballVerified
