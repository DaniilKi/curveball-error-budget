import NativeSubsetCapacity
import FiniteCurveballKernel
import ControlledEntropyExecution

namespace CurveballVerified
noncomputable section
open OAI.Problem315 CurveballNativeSampling
attribute [local instance] Classical.propDecidable

/-- DRAFT: uncompiled proof-side representation of the actual raw edge list.
    No native runtime definition is replaced or extended. -/
structure NativeModel (n : Nat) (d : Fin n → Nat) where
  edges : CurveballNative.Edges
  valid : CurveballNative.graphValid n edges = true
  realizes : Realizes n d (canonicalOfNative n edges valid).toSimpleGraph

def NativeModel.project {n : Nat} {d : Fin n → Nat} (s : NativeModel n d) :
    GraphState n d := ⟨(canonicalOfNative n s.edges s.valid).toSimpleGraph,s.realizes⟩

def observeNativeModel (n : Nat) (d : Fin n → Nat) (out : CurveballNative.Edges) :
    Option (NativeModel n d) :=
  if hv : CurveballNative.graphValid n out = true then
    if hd : Realizes n d (canonicalOfNative n out hv).toSimpleGraph then
      some ⟨out,hv,hd⟩ else none
  else none

def nativeConcreteStep (r : Request) (d : Fin r.n → Nat) (s : NativeModel r.n d)
    (bits : Tape (pairReserve r + subsetReserve r)) : Option (NativeModel r.n d) :=
  (draw r s.edges bits.val).bind fun out =>
    (CurveballNative.trade r.n s.edges out.1.first out.1.second out.1.chosen).bind
      (observeNativeModel r.n d)

theorem nativeConcreteStep_project (r : Request) (d : Fin r.n → Nat)
    (s : NativeModel r.n d) (bits : Tape (pairReserve r + subsetReserve r)) :
    (nativeConcreteStep r d s bits).map NativeModel.project =
      samplingStep r d s.edges bits.val := by
  unfold nativeConcreteStep samplingStep
  cases hd : draw r s.edges bits.val with
  | none => simp [hd]
  | some out =>
    simp only [hd,Option.bind_some]
    unfold nativeTradeState
    cases ht : CurveballNative.trade r.n s.edges out.1.first out.1.second out.1.chosen with
    | none => simp [ht]
    | some es =>
      simp only [ht,Option.bind_some]
      unfold observeNativeModel
      split_ifs <;> rfl

/-- All proof-side model checks are redundant after a successful actual native
    trade; no legal native success is silently removed by the concrete lift. -/
theorem observeNativeModel_after_trade {n : Nat} {d : Fin n → Nat}
    (s : NativeModel n d) (drawn : CurveballNative.Draw) (out : CurveballNative.Edges)
    (ht : CurveballNative.trade n s.edges drawn.first drawn.second drawn.chosen = some out) :
    ∃ next : NativeModel n d,
      next.edges = out ∧ observeNativeModel n d out = some next := by
  let C := canonicalOfNative n s.edges s.valid
  have href := canonicalOfNative_refines n s.edges s.valid
  obtain ⟨H,hrep,hv,hdeg⟩ := native_step_success_refines href ht
  have hcanon : (canonicalOfNative n out hv).toSimpleGraph = H.toSimpleGraph := by
    ext u v
    exact (native_adjacent_refines (canonicalOfNative_refines n out hv) u v).symm.trans
      (native_adjacent_refines hrep u v)
  have hr : Realizes n d (canonicalOfNative n out hv).toSimpleGraph := by
    intro v
    rw [hcanon,← degree_refines H,hdeg,degree_refines C]
    exact s.realizes v
  exact ⟨⟨out,hv,hr⟩,rfl,by simp [observeNativeModel,hv,hr]⟩

/-- Only arithmetic obligations for the actual fixed-reservation protocol.
    No sampler distribution, transition, independence or inference conclusion is
    a field of this record. Discharging it from withinLimits remains separate. -/
structure SamplingCapacities (r : Request) : Prop where
  nTwo : 2 ≤ r.n
  pairWidth : r.n.choose 2 ≤ 2 ^ wordWidth (r.n.choose 2)
  pairReserve : wordWidth (r.n.choose 2) * r.cap ≤ CurveballNativeSampling.pairReserve r
  subsetWidth : ∀ es : CurveballNative.Edges,
    CurveballNative.graphValid r.n es = true → ∀ rank : Fin (r.n.choose 2),
    nativeSubsetBound r es rank ≤ 2 ^ wordWidth (nativeSubsetBound r es rank)
  subsetReserve : ∀ es : CurveballNative.Edges,
    CurveballNative.graphValid r.n es = true → ∀ rank : Fin (r.n.choose 2),
    wordWidth (nativeSubsetBound r es rank) * r.cap ≤ CurveballNativeSampling.subsetReserve r

/-- Derived concrete-state native row bound, specialized from the actual draw
    proof rather than supplied as an ideal row or Markov premise. -/
theorem native_concrete_row_dominated (r : Request) (d : Fin r.n → Nat)
    (hc : SamplingCapacities r) (s : NativeModel r.n d) (H : GraphState r.n d) :
    (mapLaw (uniformLaw (Tape (pairReserve r + subsetReserve r)))
      (fun bits => (nativeConcreteStep r d s bits).map NativeModel.project)).mass (some H) ≤
        transition r.n d s.project H := by
  letI : NeZero (r.n.choose 2) := ⟨ne_of_gt (Nat.choose_pos hc.nTwo)⟩
  have hf : (fun bits => (nativeConcreteStep r d s bits).map NativeModel.project) =
      (fun bits => samplingStep r d s.edges bits.val) := by
    funext bits
    exact nativeConcreteStep_project r d s bits
  rw [hf]
  let C := canonicalOfNative r.n s.edges s.valid
  have href := canonicalOfNative_refines r.n s.edges s.valid
  exact sampling_draw_row_dominated r d s.edges C href s.valid s.project H rfl
    hc.pairWidth hc.pairReserve
    (native_all_pair_bounds_positive r s.edges C href s.project rfl)
    (hc.subsetWidth s.edges s.valid) (hc.subsetReserve s.edges s.valid)

/-- Probabilistic law of the actual native concrete steps on fresh complete
    reservations is dominated by the existing transition power. The remaining
    exact generateTrace/frame identity is explicitly not assumed here. -/
theorem native_concrete_execution_dominated (r : Request) (d : Fin r.n → Nat)
    (hc : SamplingCapacities r) (s : NativeModel r.n d) (t : Nat) (H : GraphState r.n d) :
    (controlledLaw (uniformLaw (Tape (pairReserve r + subsetReserve r)))
      (nativeConcreteStep r d) NativeModel.project s t).mass (some H) ≤
        (transition r.n d ^ t) s.project H := by
  have h := controlledLaw_dominated
    (uniformLaw (Tape (pairReserve r + subsetReserve r)))
    (nativeConcreteStep r d) NativeModel.project (finiteCurveballRow hc.nTwo)
    (native_concrete_row_dominated r d hc) s t H
  exact h.trans_eq (finite_curveball_iterate_mass hc.nTwo s.project H t)

#print axioms nativeConcreteStep_project
#print axioms observeNativeModel_after_trade
#print axioms native_concrete_row_dominated
#print axioms native_concrete_execution_dominated
end
end CurveballVerified
