import NativeOneChainLaw
import NativeGenerationFraming
import PartialIndependentBatch

namespace CurveballVerified
noncomputable section
open OAI.Problem315 CurveballNativeSampling
attribute [local instance] Classical.propDecidable

def rawGraphBatch (n : Nat) (d : Fin n → Nat) :
    (b : Nat) → List CurveballNative.Edges → Option (BatchSpace (GraphState n d) b)
  | 0, [] => some ()
  | 0, _::_ => none
  | _+1, [] => none
  | b+1, es::outs => ((observeNativeModel n d es).map NativeModel.project).bind
      fun G => (rawGraphBatch n d b outs).map (fun tail => (G,tail))

def batchProjection (r : Request) (d : Fin r.n → Nat) (b : Nat) (bits : List Bool) :
    Option (BatchSpace (GraphState r.n d) b) :=
  (batch r b bits).bind fun out => rawGraphBatch r.n d b out.1

/-- DRAFT: the exact actual batch restarts each oneChain at original r.edges,
    in order and on disjoint complete chain reservations. The finite observer
    does not replace either chain execution or runtime batch recursion. -/
theorem batch_projection_eq_execute (r : Request) (d : Fin r.n → Nat)
    (hc : SamplingCapacities r) (hv : CurveballNative.graphValid r.n r.edges = true)
    (b : Nat) (bits : BatchSpace (Tape ((pairReserve r + subsetReserve r)*r.trades)) b)
    (suffix : List Bool) :
    batchProjection r d b
      ((chunksTapeEquiv ((pairReserve r + subsetReserve r)*r.trades) b bits).val ++ suffix) =
    executeIndependentBatch (fun tape : Tape ((pairReserve r + subsetReserve r)*r.trades) =>
      oneChainProjection r d tape.val) b bits := by
  induction b generalizing suffix with
  | zero => simp [batchProjection,batch,rawGraphBatch,executeIndependentBatch]
  | succ b ih =>
    have hframe := one_chain_allocated_prefix r hc hv bits.1
      ((chunksTapeEquiv ((pairReserve r + subsetReserve r)*r.trades) b bits.2).val ++ suffix)
    rw [chunksTapeEquiv_val_succ,List.append_assoc]
    unfold batchProjection
    simp only [batch]
    rw [hframe]
    cases hchain : oneChain r bits.1.val with
    | none => simp [hchain,executeIndependentBatch,oneChainProjection]
    | some out =>
      obtain ⟨first,count,rest⟩ := out
      simp only [hchain,Option.map_some]
      dsimp only [Bind.bind,Pure.pure]
      simp only [Option.bind_some]
      simp only [executeIndependentBatch]
      have hhead : oneChainProjection r d bits.1.val =
          (observeNativeModel r.n d first).map NativeModel.project := by
        simp only [oneChainProjection,hchain,Option.bind_some]
      rw [hhead,← ih bits.2 suffix]
      unfold batchProjection
      cases htail : batch r b
          ((chunksTapeEquiv ((pairReserve r + subsetReserve r)*r.trades) b bits.2).val ++ suffix) with
      | none =>
        cases hobs : observeNativeModel r.n d first <;> simp [hobs] <;> rfl
      | some tail =>
        obtain ⟨outs,total,unused⟩ := tail
        simp [htail,rawGraphBatch,Option.bind_assoc]

theorem actual_batch_law (r : Request) (d : Fin r.n → Nat) (hc : SamplingCapacities r)
    (hv : CurveballNative.graphValid r.n r.edges = true) (b : Nat) :
    mapLaw (uniformLaw (Tape (((pairReserve r + subsetReserve r)*r.trades)*b)))
      (fun tape => batchProjection r d b tape.val) =
    mapLaw (batchLaw (fun _ => uniformLaw (Tape ((pairReserve r + subsetReserve r)*r.trades))) b)
      (executeIndependentBatch
        (fun tape : Tape ((pairReserve r + subsetReserve r)*r.trades) => oneChainProjection r d tape.val) b) := by
  have he := uniform_chunks_tape_law ((pairReserve r + subsetReserve r)*r.trades) b
  rw [← he,mapLaw_comp]
  have hf : (fun bits => batchProjection r d b
      (chunksTapeEquiv ((pairReserve r + subsetReserve r)*r.trades) b bits).val) =
      executeIndependentBatch
        (fun tape : Tape ((pairReserve r + subsetReserve r)*r.trades) => oneChainProjection r d tape.val) b := by
    funext bits
    simpa only [List.append_nil] using batch_projection_eq_execute r d hc hv b bits []
  simp only [Function.comp_def]
  rw [hf]

/-- Completed actual raw-batch graph mass is dominated by ordered independent
    ordinary Curveball chains conditional on this fixed observation/start graph.
    No observed null-law, exchangeability or inference guarantee is assumed. -/
theorem actual_batch_dominated (r : Request) (d : Fin r.n → Nat) (hc : SamplingCapacities r)
    (s : NativeModel r.n d) (hs : s.edges = r.edges) (b : Nat)
    (ys : BatchSpace (GraphState r.n d) b) :
    (mapLaw (uniformLaw (Tape (((pairReserve r + subsetReserve r)*r.trades)*b)))
      (fun tape => batchProjection r d b tape.val)).mass (some ys) ≤
    (batchLaw (fun _ => iterateKernel (finiteCurveballRow hc.nTwo) s.project r.trades) b).mass ys := by
  have hv : CurveballNative.graphValid r.n r.edges = true := hs ▸ s.valid
  rw [actual_batch_law r d hc hv b]
  apply independent_batch_dominated
  intro H
  exact (actual_one_chain_dominated r d hc s hs H).trans_eq
    (finite_curveball_iterate_mass hc.nTwo s.project H r.trades).symm

#print axioms batch_projection_eq_execute
#print axioms actual_batch_law
#print axioms actual_batch_dominated
end
end CurveballVerified
