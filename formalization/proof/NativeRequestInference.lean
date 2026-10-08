import NativeRuntimeRejection
import NativeModelGraphJoins

/- SOURCE-ONLY DRAFT. Final request-restricted root; all graph and analytical
   imports still need acceptance. There is no OS/IO/compiler correctness axiom
   in this mathematical theorem. Real-executable correspondence is explicit TCB.
   The modeled observation is uniform graphical null data, not a fixed graph. -/
namespace CurveballVerified
noncomputable section
open OAI.Problem315 CurveballNativeSampling
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def nativeRequestDegrees (r : Request) (hlimits : withinLimits r = true) :
    Fin r.n → Nat :=
  graphDegree (canonicalOfNative r.n r.edges (native_limits_valid r hlimits)).toSimpleGraph

def nativeRequestModel (r : Request) (hlimits : withinLimits r = true) :
    NativeModel r.n (nativeRequestDegrees r hlimits) :=
  ⟨r.edges,native_limits_valid r hlimits,fun _ => rfl⟩

def nativeRequestNullExperiment (r : Request) (hlimits : withinLimits r = true) :
    FiniteLaw (GraphState r.n (nativeRequestDegrees r hlimits) ×
      BatchSpace (Fin 256) (entropyBytes r)) := by
  letI : Nonempty (GraphState r.n (nativeRequestDegrees r hlimits)) :=
    ⟨(nativeRequestModel r hlimits).project⟩
  exact productLaw (uniformLaw (GraphState r.n (nativeRequestDegrees r hlimits)))
    (batchLaw (fun _ => uniformLaw (Fin 256)) (entropyBytes r))

def nativeRequestReject (r : Request) (hlimits : withinLimits r = true) :
    GraphState r.n (nativeRequestDegrees r hlimits) ×
      BatchSpace (Fin 256) (entropyBytes r) → Prop :=
  fun x => nativeReplyReject
    (requestAt r (nativeModelOfGraph (native_limits_representation_bound r hlimits) x.1))
    (bytesFromBlocks (entropyBytes r) x.2)

/-- PRECISE FINAL FINITE THEOREM DRAFT. For actual requests whose exact resource
    and integer-plan checks succeed, uniform graphical null observation followed
    by independent uniform complete byte input gives probability at most alpha
    of a completed actual native output whose computed rank field is true.
    Failures never reject; no completion conditioning/retry. Every capacity,
    representation and edge-count premise is derived from actual request guards.
    Runtime caps include n≤26, trades≤1024, b≤32, entropy≤262144 bytes. They are
    implementation restrictions; the broader mathematical schedule is separate.
    No claimed error bound, mixing or exchangeability premise is assumed. -/
theorem native_request_type_I (r : Request) (hlimits : withinLimits r = true)
    (hplan : arithmeticPlan r = true) :
    eventMass (nativeRequestNullExperiment r hlimits) (nativeRequestReject r hlimits) ≤
      (r.alphaNum : ℝ)/r.alphaDen := by
  let d := nativeRequestDegrees r hlimits
  letI : Nonempty (GraphState r.n d) := ⟨(nativeRequestModel r hlimits).project⟩
  let hn := native_limits_representation_bound r hlimits
  let models : GraphState r.n d → NativeModel r.n d := nativeModelOfGraph hn
  have hmodels : ∀ G, (models G).project = G := fun G => nativeModelOfGraph_project hn G
  have hedges : r.edges.length = (∑ v,d v)/2 :=
    native_model_edge_count (nativeRequestModel r hlimits)
  exact native_raw_byte_rank_bound r d models hmodels hlimits hplan hedges

#print axioms native_request_type_I
end
end CurveballVerified
