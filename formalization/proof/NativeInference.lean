import CurveballKernelLaw
import NativeArithmetic
import NativeRankCounting

namespace CurveballVerified
noncomputable section
open OAI.Problem315
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Exact native rank decision on internally computed exceedances, in the full
    ordinary-chain experiment. The actual capped/native graph experiment still
    needs its failure/refinement coupling to this experiment. -/
theorem native_curveball_inference_bound {n : Nat} {d : Fin n → Nat}
    [Nonempty (GraphState n d)] (hn : 4 ≤ n) {p q k trades : Nat}
    (hcheck : budgetCheck n ((∑ v, d v) / 2) p q k trades = true)
    (b etaNum etaDen alphaNum alphaDen : Nat)
    (he : 0 < etaDen) (ha : 0 < alphaDen)
    (hc : etaNum * alphaDen ≤ alphaNum * etaDen)
    (hbatch : (b : ℝ) * ((p : ℝ) / q) ≤ (etaNum : ℝ) / etaDen)
    (statistic : GraphState n d → Nat) :
    eventMass (curveballExperiment (d := d) (by omega : 2 ≤ n) trades b)
      (fun x => CurveballNative.rankCheck b (exceedCount b statistic x)
        etaNum etaDen alphaNum alphaDen = true) ≤ (alphaNum : ℝ) / alphaDen := by
  have hmono := eventMass_mono
    (curveballExperiment (d := d) (by omega : 2 ≤ n) trades b)
    (fun x => CurveballNative.rankCheck b (exceedCount b statistic x)
      etaNum etaDen alphaNum alphaDen = true)
    (fun x => rankCount (fun j => statistic (batchVector (b + 1) x j)) 0 *
      (alphaDen * etaDen) ≤ (alphaNum * etaDen - etaNum * alphaDen) * (b + 1))
    (fun x hx => native_rank_implies_cutoff b statistic x etaNum etaDen alphaNum alphaDen hx)
  have hr := checked_curveball_rank_bound hn hcheck b
    (alphaNum * etaDen - etaNum * alphaDen) (alphaDen * etaDen)
    (Nat.mul_pos ha he) statistic
  have hid := rational_cutoff_identity he ha hc
  simp only [Nat.cast_mul] at hr
  linarith

#print axioms rankCount_observed
#print axioms native_rank_implies_cutoff
#print axioms rational_cutoff_identity
#print axioms native_curveball_inference_bound
end
end CurveballVerified
