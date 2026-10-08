import NativeRankKernel
import NativePairFin

namespace CurveballVerified
noncomputable section
open OAI.Problem315
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Finite normalization of the literal existing transition, without the
    analytical spectral imports. Names avoid duplicating pending analytical roots. -/
theorem finite_transition_nonnegative {n : Nat} {d : Fin n → Nat}
    (G H : GraphState n d) : 0 ≤ transition n d G H := by
  unfold transition
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro a ha
  unfold pairKernel
  split_ifs <;> positivity

theorem finite_transition_normalized {n : Nat} {d : Fin n → Nat}
    (hn : 2 ≤ n) (G : GraphState n d) : ∑ H, transition n d G H = 1 := by
  have hr (a : Finset (Fin n)) : ∑ H, pairKernel a G H = 1 := by
    simp_rw [← fiberLaw_mass]
    exact (fiberLaw a G).normalized
  have hN : (n.choose 2 : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Nat.choose_pos hn)
  have hf (H : GraphState n d) : transition n d G H =
      (n.choose 2 : ℝ)⁻¹ * ∑ rank : Fin (n.choose 2),
        pairKernel {(nativePairEndpoint n rank).1,(nativePairEndpoint n rank).2} G H := by
    simpa only [div_eq_mul_inv,mul_comm] using (nativePairEndpoint_sum G H).symm
  simp_rw [hf]
  rw [← Finset.mul_sum,Finset.sum_comm]
  simp_rw [hr]
  simp [hN]

def finiteCurveballRow {n : Nat} {d : Fin n → Nat} (hn : 2 ≤ n)
    (G : GraphState n d) : FiniteLaw (GraphState n d) where
  mass := transition n d G
  nonnegative := finite_transition_nonnegative G
  normalized := finite_transition_normalized hn G

theorem finite_curveball_iterate_mass {n : Nat} {d : Fin n → Nat}
    (hn : 2 ≤ n) (G H : GraphState n d) (t : Nat) :
    (iterateKernel (finiteCurveballRow hn) G t).mass H = (transition n d ^ t) G H :=
  iterateKernel_mass (finiteCurveballRow hn) G H t

#print axioms finite_transition_normalized
#print axioms finite_curveball_iterate_mass
end
end CurveballVerified
