import NativeSamplingByteInference
import NativeBatchObserverJoins
import NativeSamplingBoundary

/- SOURCE-ONLY DRAFT. Graph joins and analytical/inference imports are pending.
   No compiler run or final theorem acceptance claimed. Actual runtime unchanged.
   The event names literal batch outputs and builder's actual computed fields. -/
namespace CurveballVerified
noncomputable section
open OAI.Problem315 CurveballNativeSampling CurveballNativeSamplingBoundary
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def nativeReplyReject (r : Request) (bytes : ByteArray) : Prop :=
  bytes.size = entropyBytes r ∧
    ∃ outs count rest, batch r r.b (bytesBits bytes) = some (outs,count,rest) ∧
      completionGuard r outs count rest = false ∧
      (computedFields r outs count).rank = true

theorem native_reply_reject_success (r : Request) (bytes : ByteArray)
    (h : nativeReplyReject r bytes) : (tapeReply r bytes).exitCode = 0 := by
  obtain ⟨hsize,outs,count,rest,hbatch,hcomplete,hrank⟩ := h
  simp [tapeReply,hsize,hbatch,completionReply,hcomplete]

/-- No runtime success is silently lost by a proof-side observer. The actual
    native rank decision agrees with the actual graph statistic on that output. -/
theorem native_reply_reject_projected (r : Request) (d : Fin r.n → Nat)
    (s : NativeModel r.n d) (hs : s.edges = r.edges) (bytes : ByteArray)
    (h : nativeReplyReject r bytes) :
    nativeGraphReject r d (s.project,batchProjection r d r.b (bytesBits bytes)) := by
  obtain ⟨hsize,outs,count,rest,hbatch,hcomplete,hrank⟩ := h
  obtain ⟨ys,hys⟩ := batch_success_observer r d s hs hbatch
  have hproject : batchProjection r d r.b (bytesBits bytes) = some ys := by
    simp only [batchProjection,hbatch,Option.bind_some]
    exact hys
  rw [hproject]
  change CurveballNative.rankCheck r.b (exceedCount r.b graphTriangles (s.project,ys))
    r.etaNum r.etaDen r.alphaNum r.alphaDen = true
  rw [← native_completed_rank_identity r d s hs outs ys hys]
  simpa only [computedFields] using hrank

theorem conditional_map_event_mass {α β γ : Type} [Fintype α] [Fintype β]
    [Fintype γ] [DecidableEq γ] (p : FiniteLaw α) (q : FiniteLaw β)
    (f : α → β → γ) (E : α × γ → Prop) :
    eventMass (conditionalLaw p (fun a => mapLaw q (f a))) E =
      eventMass (productLaw p q) (fun x => E (x.1,f x.1 x.2)) := by
  unfold eventMass
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  have hleft :
      (∑ y, if E (a,y) then p.mass a * (mapLaw q (f a)).mass y else 0) =
      p.mass a * eventMass (mapLaw q (f a)) (fun y => E (a,y)) := by
    unfold eventMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases he : E (a,y) <;> simp [he]
  have hright :
      p.mass a * eventMass q (fun y => E (a,f a y)) =
      (∑ y, if E (a,f a y) then p.mass a * q.mass y else 0) := by
    unfold eventMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases he : E (a,f a y) <;> simp [he]
  change (∑ y, if E (a,y) then p.mass a * (mapLaw q (f a)).mass y else 0) =
    (∑ y, if E (a,f a y) then p.mass a * q.mass y else 0)
  rw [hleft,mapLaw_event]
  exact hright

/-- Literal completed native reply/field rejection event under the complete
    independent byte vectors and uniform graphical observation null model.
    Desired inference bound and sampler law are derived, never assumed. -/
theorem native_raw_byte_rank_bound (r : Request) (d : Fin r.n → Nat)
    [Nonempty (GraphState r.n d)]
    (models : GraphState r.n d → NativeModel r.n d)
    (hmodels : ∀ G, (models G).project = G)
    (hlimits : withinLimits r = true) (hplan : arithmeticPlan r = true)
    (hedges : r.edges.length = (∑ v,d v)/2) :
    eventMass (productLaw (uniformLaw (GraphState r.n d))
      (batchLaw (fun _ => uniformLaw (Fin 256)) (entropyBytes r)))
      (fun x => nativeReplyReject (requestAt r (models x.1))
        (bytesFromBlocks (entropyBytes r) x.2)) ≤ (r.alphaNum : ℝ)/r.alphaDen := by
  let f := fun G xs => batchProjection (requestAt r (models G)) d r.b
    (bytesBits (bytesFromBlocks (entropyBytes r) xs))
  have hmap := conditional_map_event_mass (uniformLaw (GraphState r.n d))
    (batchLaw (fun _ => uniformLaw (Fin 256)) (entropyBytes r)) f (nativeGraphReject r d)
  have hmono := eventMass_mono
    (productLaw (uniformLaw (GraphState r.n d))
      (batchLaw (fun _ => uniformLaw (Fin 256)) (entropyBytes r)))
    (fun x => nativeReplyReject (requestAt r (models x.1))
      (bytesFromBlocks (entropyBytes r) x.2))
    (fun x => nativeGraphReject r d (x.1,f x.1 x.2)) (by
      intro x hx
      have h := native_reply_reject_projected (requestAt r (models x.1)) d
        (models x.1) rfl (bytesFromBlocks (entropyBytes r) x.2) hx
      change nativeGraphReject (requestAt r (models x.1)) d
        ((models x.1).project, f x.1 x.2) at h
      cases hy : f x.1 x.2 with
      | none => simp only [nativeGraphReject, hy] at h
      | some ys =>
        simp only [nativeGraphReject, hy] at h ⊢
        simpa only [requestAt, hmodels x.1] using h)
  calc
    _ ≤ _ := hmono
    _ = eventMass (nativeByteGraphExperiment r d models) (nativeGraphReject r d) := hmap.symm
    _ ≤ (r.alphaNum : ℝ)/r.alphaDen :=
      actual_native_byte_rank_bound r d models hmodels hlimits hplan hedges

#print axioms native_reply_reject_success
#print axioms native_reply_reject_projected
#print axioms conditional_map_event_mass
#print axioms native_raw_byte_rank_bound
end
end CurveballVerified
