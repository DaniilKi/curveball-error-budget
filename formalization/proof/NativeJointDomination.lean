import NativeBatchLaw
import ConditionalProbability

namespace CurveballVerified
noncomputable section
open OAI.Problem315 CurveballNativeSampling
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def requestAt (r : Request) {d : Fin r.n → Nat} (s : NativeModel r.n d) : Request :=
  { r with edges := s.edges }

theorem sampling_capacities_requestAt (r : Request) {d : Fin r.n → Nat}
    (s : NativeModel r.n d) (hc : SamplingCapacities r) :
    SamplingCapacities (requestAt r s) :=
  ⟨hc.nTwo,hc.pairWidth,hc.pairReserve,hc.subsetWidth,hc.subsetReserve⟩

def nativeReplicateLaw (r : Request) (d : Fin r.n → Nat)
    (s : NativeModel r.n d) (b : Nat) :
    FiniteLaw (Option (BatchSpace (GraphState r.n d) b)) :=
  mapLaw (uniformLaw (Tape (((pairReserve r + subsetReserve r)*r.trades)*b)))
    (fun tape => batchProjection (requestAt r s) d b tape.val)

theorem native_replicate_mass_dominated (r : Request) (d : Fin r.n → Nat)
    (hc : SamplingCapacities r) (s : NativeModel r.n d) (b : Nat)
    (ys : BatchSpace (GraphState r.n d) b) :
    (nativeReplicateLaw r d s b).mass (some ys) ≤
      (batchLaw (fun _ => iterateKernel (finiteCurveballRow hc.nTwo) s.project r.trades) b).mass ys :=
  actual_batch_dominated (requestAt r s) d (sampling_capacities_requestAt r s hc) s rfl b ys

/-- Representation witnesses only: every raw starting graph projects to its
    stated mathematical graph. No probabilistic or exchangeability premise. -/
def nativeGraphExperiment (r : Request) (d : Fin r.n → Nat)
    [Nonempty (GraphState r.n d)]
    (models : GraphState r.n d → NativeModel r.n d) (b : Nat) :
    FiniteLaw (GraphState r.n d × Option (BatchSpace (GraphState r.n d) b)) :=
  conditionalLaw (uniformLaw (GraphState r.n d))
    (fun G => nativeReplicateLaw r d (models G) b)

def idealGraphExperiment (r : Request) (d : Fin r.n → Nat)
    [Nonempty (GraphState r.n d)] (hc : SamplingCapacities r) (b : Nat) :
    FiniteLaw (BatchSpace (GraphState r.n d) (b+1)) :=
  conditionalLaw (uniformLaw (GraphState r.n d))
    (fun G => batchLaw (fun _ => iterateKernel (finiteCurveballRow hc.nTwo) G r.trades) b)

/-- Every completed event of the actual runtime is dominated by the ordinary
    conditional graph experiment. Failures remain failures and contribute zero;
    there is no conditioning on completion or resampling after failure. The
    uniform observed null law is an explicit scientific model in both sides. -/
theorem actual_joint_event_dominated (r : Request) (d : Fin r.n → Nat)
    [Nonempty (GraphState r.n d)] (hc : SamplingCapacities r)
    (models : GraphState r.n d → NativeModel r.n d)
    (hmodels : ∀ G, (models G).project = G) (b : Nat)
    (E : BatchSpace (GraphState r.n d) (b+1) → Prop) :
    eventMass (nativeGraphExperiment r d models b)
      (fun x => match x.2 with | none => False | some ys => E (x.1,ys)) ≤
    eventMass (idealGraphExperiment r d hc b) E := by
  dsimp only [BatchSpace] at E ⊢
  unfold eventMass nativeGraphExperiment idealGraphExperiment
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro G hG
  simp only [Fintype.sum_option,conditionalLaw,if_false,zero_add]
  apply Finset.sum_le_sum
  intro ys hys
  by_cases he : E (G,ys)
  · simp only [he,if_true]
    apply mul_le_mul_of_nonneg_left _ ((uniformLaw (GraphState r.n d)).nonnegative G)
    have h := native_replicate_mass_dominated r d hc (models G) b ys
    simpa only [hmodels G] using h
  · simp [he]

#print axioms sampling_capacities_requestAt
#print axioms native_replicate_mass_dominated
#print axioms actual_joint_event_dominated
end
end CurveballVerified
