import NativeDrawAllocationPrefix

namespace CurveballVerified
noncomputable section
open OAI.Problem315 CurveballNativeSampling
attribute [local instance] Classical.propDecidable

/-- DRAFT: bijection between complete finite reservations and a single full
    uniform tape. This is proof-side entropy organization, not another sampler. -/
def chunksTapeEquiv (width : Nat) : (t : Nat) →
    BatchSpace (Tape width) t ≃ Tape (width*t)
  | 0 =>
    { toFun := fun _ => ⟨[],by simp⟩
      invFun := fun _ => ()
      left_inv := fun x => by cases x; rfl
      right_inv := fun x => by
        apply Subtype.ext
        have h : x.val.length = 0 := by simpa using x.property
        exact (List.eq_nil_of_length_eq_zero h).symm }
  | t+1 =>
    ((Equiv.refl (Tape width)).prodCongr (chunksTapeEquiv width t)).trans
      ((appendTapeEquiv width (width*t)).trans
        (tapeCongr (by simp [Nat.mul_succ,Nat.add_comm])))

theorem chunksTapeEquiv_val_succ (width t : Nat)
    (bits : BatchSpace (Tape width) (t+1)) :
    (chunksTapeEquiv width (t+1) bits).val =
      bits.1.val ++ (chunksTapeEquiv width t bits.2).val := rfl

theorem uniform_chunks_tape_law (width t : Nat) :
    mapLaw (batchLaw (fun _ => uniformLaw (Tape width)) t) (chunksTapeEquiv width t) =
      uniformLaw (Tape (width*t)) := by
  rw [batchLaw_uniform]
  exact map_uniform_bijection (chunksTapeEquiv width t)

/-- Finite observation of the ACTUAL generateTrace endpoint. Raw output validity
    and degree guards match observeNativeModel, proved redundant at every actual
    native successful trade. The draws/replay computation remains unchanged. -/
def generatedProjection (r : Request) (d : Fin r.n → Nat) (t : Nat)
    (es : CurveballNative.Edges) (bits : List Bool) : Option (GraphState r.n d) :=
  (generateTrace r t es bits).bind fun out =>
    (observeNativeModel r.n d out.2.1).map NativeModel.project

theorem generated_projection_eq_controlled (r : Request) (d : Fin r.n → Nat)
    (hc : SamplingCapacities r) (s : NativeModel r.n d) (t : Nat)
    (bits : BatchSpace (Tape (pairReserve r + subsetReserve r)) t)
    (suffix : List Bool) :
    controlledRun (nativeConcreteStep r d) NativeModel.project s t bits =
      generatedProjection r d t s.edges
        ((chunksTapeEquiv (pairReserve r + subsetReserve r) t bits).val ++ suffix) := by
  induction t generalizing s suffix with
  | zero =>
    simp [controlledRun,generatedProjection,generateTrace,observeNativeModel,
      s.valid,s.realizes,NativeModel.project]
  | succ t ih =>
    have hframe := draw_allocated_prefix r s.edges bits.1
      ((chunksTapeEquiv (pairReserve r + subsetReserve r) t bits.2).val ++ suffix)
      hc.pairReserve (hc.subsetReserve s.edges s.valid)
    rw [chunksTapeEquiv_val_succ,List.append_assoc]
    unfold generatedProjection
    simp only [generateTrace]
    rw [hframe]
    cases hd : draw r s.edges bits.1.val with
    | none => simp [controlledRun,nativeConcreteStep,hd]
    | some out =>
      obtain ⟨drawn,rest⟩ := out
      simp only [hd,Option.map_some]
      dsimp only [Bind.bind,Pure.pure]
      simp only [Option.bind_some]
      cases ht : CurveballNative.trade r.n s.edges drawn.first drawn.second drawn.chosen with
      | none => simp [controlledRun,nativeConcreteStep,hd,ht]
      | some nextEdges =>
        obtain ⟨next,he,hn⟩ := observeNativeModel_after_trade s drawn nextEdges ht
        have hstep : nativeConcreteStep r d s bits.1 = some next := by
          simp [nativeConcreteStep,hd,ht,hn]
        simp only [controlledRun,hstep,Option.bind_some]
        rw [ih next bits.2 suffix]
        cases hg : generateTrace r t nextEdges
            ((chunksTapeEquiv (pairReserve r + subsetReserve r) t bits.2).val ++ suffix) with
        | none => simp [generatedProjection,he,ht,hg]
        | some result => simp [generatedProjection,he,ht,hg]

theorem actual_generated_trace_law (r : Request) (d : Fin r.n → Nat)
    (hc : SamplingCapacities r) (s : NativeModel r.n d) (t : Nat) :
    mapLaw (uniformLaw (Tape ((pairReserve r + subsetReserve r)*t)))
      (fun tape => generatedProjection r d t s.edges tape.val) =
      controlledLaw (uniformLaw (Tape (pairReserve r + subsetReserve r)))
        (nativeConcreteStep r d) NativeModel.project s t := by
  have he := uniform_chunks_tape_law (pairReserve r + subsetReserve r) t
  rw [← he,mapLaw_comp]
  have hf : (fun bits => generatedProjection r d t s.edges
      (chunksTapeEquiv (pairReserve r + subsetReserve r) t bits).val) =
      controlledRun (nativeConcreteStep r d) NativeModel.project s t := by
    funext bits
    simpa only [List.append_nil] using
      (generated_projection_eq_controlled r d hc s t bits []).symm
  simp only [Function.comp_def]
  rw [hf]
  rfl

/-- Full finite uniform entropy through the ACTUAL generateTrace is dominated
    by the existing transition power; cap failures remain none. -/
theorem actual_generated_trace_dominated (r : Request) (d : Fin r.n → Nat)
    (hc : SamplingCapacities r) (s : NativeModel r.n d) (t : Nat)
    (H : GraphState r.n d) :
    (mapLaw (uniformLaw (Tape ((pairReserve r + subsetReserve r)*t)))
      (fun tape => generatedProjection r d t s.edges tape.val)).mass (some H) ≤
        (transition r.n d ^ t) s.project H := by
  rw [actual_generated_trace_law r d hc s t]
  exact native_concrete_execution_dominated r d hc s t H

#print axioms uniform_chunks_tape_law
#print axioms generated_projection_eq_controlled
#print axioms actual_generated_trace_law
#print axioms actual_generated_trace_dominated
end
end CurveballVerified
