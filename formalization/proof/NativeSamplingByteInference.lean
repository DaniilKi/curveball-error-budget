import NativeByteBatchLaw
import NativeSamplingInference

/- SOURCE-ONLY DRAFT. Analytical/byte proof receipts and guard/model joins
   required before scientific assurance. Complete proof bodies, no assumed
   desired TV/type-I bound. Runtime unchanged. -/
namespace CurveballVerified
noncomputable section
open OAI.Problem315 CurveballNativeSampling
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def nativeByteGraphExperiment (r : Request) (d : Fin r.n → Nat)
    [Nonempty (GraphState r.n d)] (models : GraphState r.n d → NativeModel r.n d) :
    FiniteLaw (GraphState r.n d × Option (BatchSpace (GraphState r.n d) r.b)) :=
  conditionalLaw (uniformLaw (GraphState r.n d)) fun G =>
    mapLaw (batchLaw (fun _ => uniformLaw (Fin 256)) (entropyBytes r))
      (fun xs => batchProjection (requestAt r (models G)) d r.b
        (bytesBits (bytesFromBlocks (entropyBytes r) xs)))

theorem native_byte_graph_experiment_eq_bits (r : Request) (d : Fin r.n → Nat)
    [Nonempty (GraphState r.n d)] (models : GraphState r.n d → NativeModel r.n d) :
    nativeByteGraphExperiment r d models = nativeGraphExperiment r d models r.b := by
  unfold nativeByteGraphExperiment nativeGraphExperiment
  congr 1
  funext G
  exact native_byte_batch_law (requestAt r (models G)) d

/-- Exact executable byte conversion, exact actual capped/native batch and
    internally computed rank statistic, transferred through the proved ordinary
    chain/IID inference bound. Uniform graphical observation and independent
    uniform complete byte vectors are the explicit scientific null/entropy
    models. No inference guarantee is assumed; no failure conditioning or retry.
    Graph capacities/representation and raw edge count remain deterministic
    joins, which must be derived from guards before the final public root. -/
theorem actual_native_byte_rank_bound (r : Request) (d : Fin r.n → Nat)
    [Nonempty (GraphState r.n d)]
    (models : GraphState r.n d → NativeModel r.n d)
    (hmodels : ∀ G, (models G).project = G)
    (hlimits : withinLimits r = true) (hplan : arithmeticPlan r = true)
    (hedges : r.edges.length = (∑ v,d v)/2) :
    eventMass (nativeByteGraphExperiment r d models) (nativeGraphReject r d) ≤
      (r.alphaNum : ℝ)/r.alphaDen := by
  rw [native_byte_graph_experiment_eq_bits]
  exact actual_native_rank_bound r d models hmodels hlimits hplan hedges

#print axioms native_byte_graph_experiment_eq_bits
#print axioms actual_native_byte_rank_bound
end
end CurveballVerified
