import CertifiedScheduleLite
import ProbabilityProofBundle

namespace CurveballVerified
noncomputable section
open OAI.Problem315
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def curveballRow {n : Nat} {d : Fin n → Nat} (hn : 2 ≤ n)
    (G : GraphState n d) : FiniteLaw (GraphState n d) where
  mass := transition n d G
  nonnegative H := by
    unfold transition
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro a ha
    unfold pairKernel
    split_ifs <;> positivity
  normalized := transition_rows hn G

theorem curveballRow_matrix {n : Nat} {d : Fin n → Nat} (hn : 2 ≤ n) :
    kernelMatrix (curveballRow (d := d) hn) = transition n d := rfl

theorem curveball_execution_power {n : Nat} {d : Fin n → Nat} (hn : 2 ≤ n)
    (G H : GraphState n d) (t : Nat) :
    (iterateKernel (curveballRow hn) G t).mass H = (transition n d ^ t) G H := by
  rw [iterateKernel_mass,curveballRow_matrix]

theorem checked_curveball_execution_tv {n : Nat} {d : Fin n → Nat}
    [Nonempty (GraphState n d)] (hn : 4 ≤ n) (G : GraphState n d)
    {p q k trades : Nat}
    (hcheck : budgetCheck n ((∑ v, d v) / 2) p q k trades = true) :
    tv (iterateKernel (curveballRow (d := d) (by omega : 2 ≤ n)) G trades)
       (uniformLaw (GraphState n d)) ≤ (p : ℝ) / q := by
  have h := checked_curveball_tv hn G hcheck
  simpa only [tv,curveball_execution_power,uniformLaw,stateCount,allGraphStates,
    Finset.card_univ] using h

def curveballExperiment {n : Nat} {d : Fin n → Nat}
    [Nonempty (GraphState n d)] (hn : 2 ≤ n) (trades b : Nat) :
    FiniteLaw (BatchSpace (GraphState n d) (b + 1)) :=
  conditionalLaw (uniformLaw (GraphState n d))
    (fun G => batchLaw (fun _ => iterateKernel (curveballRow hn) G trades) b)

theorem checked_curveball_experiment_tv {n : Nat} {d : Fin n → Nat}
    [Nonempty (GraphState n d)] (hn : 4 ≤ n) {p q k trades : Nat}
    (hcheck : budgetCheck n ((∑ v, d v) / 2) p q k trades = true) (b : Nat) :
    tv (curveballExperiment (d := d) (by omega : 2 ≤ n) trades b)
       (batchLaw (fun _ => uniformLaw (GraphState n d)) (b + 1)) ≤
      (b : ℝ) * ((p : ℝ) / q) := by
  exact conditional_batch_tv (uniformLaw (GraphState n d))
    (fun G _ => iterateKernel (curveballRow (d := d) (by omega : 2 ≤ n)) G trades)
    (fun _ _ => uniformLaw (GraphState n d)) ((p : ℝ) / q)
    (fun G _ => checked_curveball_execution_tv hn G hcheck) b

/-- Closed ideal-chain inference bound. This uses the checked certificate and
    proves the full observed/output experiment's comparison with ideal IID data.
    No claimed type-I bound or ideal rank bound is a hypothesis. -/
theorem checked_curveball_rank_bound {n : Nat} {d : Fin n → Nat}
    [Nonempty (GraphState n d)] (hn : 4 ≤ n) {p q k trades : Nat}
    (hcheck : budgetCheck n ((∑ v, d v) / 2) p q k trades = true)
    (b aNum aDen : Nat) (haDen : 0 < aDen) (statistic : GraphState n d → Nat) :
    eventMass (curveballExperiment (d := d) (by omega : 2 ≤ n) trades b)
      (fun x => rankCount (fun j => statistic (batchVector (b + 1) x j)) 0 * aDen ≤
        aNum * (b + 1)) ≤ (aNum : ℝ) / aDen + (b : ℝ) * ((p : ℝ) / q) := by
  have htransfer := event_transfer
    (curveballExperiment (d := d) (by omega : 2 ≤ n) trades b)
    (batchLaw (fun _ => uniformLaw (GraphState n d)) (b + 1))
    (fun x => rankCount (fun j => statistic (batchVector (b + 1) x j)) 0 * aDen ≤
      aNum * (b + 1))
  have htv := checked_curveball_experiment_tv hn hcheck b
  have hrank := iid_batch_rank_bound (b + 1) statistic 0 aNum aDen haDen
  linarith

#print axioms curveball_execution_power
#print axioms checked_curveball_execution_tv
#print axioms checked_curveball_experiment_tv
#print axioms checked_curveball_rank_bound
end
end CurveballVerified
