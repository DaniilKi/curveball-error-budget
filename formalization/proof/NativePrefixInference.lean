import NativeFinalAudit
import NativeRuntimePrefixTransfer

/- Final optimized finite-event transfer. SOURCE ONLY until accepted receipt.
   The source mapping and actual optimized native build seal are separate
   required correspondences; unchanged entry-point source hash alone is not used. -/
namespace CurveballVerified
noncomputable section
open OAI.Problem315 CurveballNativeSampling CurveballNativeSamplingBoundary
attribute [local instance] Classical.propDecidable

def nativePrefixReplyReject (r : Request) (bytes : ByteArray) : Prop :=
  bytes.size = entropyBytes r ∧
    ∃ outs count rest, CurveballNativeSamplingPrefix.batch r r.b (bytesBits bytes) =
      some (outs,count,rest) ∧ completionGuard r outs count rest = false ∧
      (computedFields r outs count).rank = true

theorem nativePrefixReplyReject_iff_frozen (r : Request) (bytes : ByteArray) :
    nativePrefixReplyReject r bytes ↔ nativeReplyReject r bytes := by
  simp only [nativePrefixReplyReject, nativeReplyReject,
    CurveballNativeSamplingPrefix.batch_eq_frozen]

def nativePrefixRequestReject (r : Request) (hlimits : withinLimits r = true) :
    GraphState r.n (nativeRequestDegrees r hlimits) ×
      BatchSpace (Fin 256) (entropyBytes r) → Prop :=
  fun x => nativePrefixReplyReject
    (requestAt r (nativeModelOfGraph (native_limits_representation_bound r hlimits) x.1))
    (bytesFromBlocks (entropyBytes r) x.2)

theorem nativePrefixRequestReject_eq_frozen (r : Request) (hlimits : withinLimits r = true) :
    nativePrefixRequestReject r hlimits = nativeRequestReject r hlimits := by
  funext x
  apply propext
  exact nativePrefixReplyReject_iff_frozen _ _

theorem native_prefix_request_type_I (r : Request) (hlimits : withinLimits r = true)
    (hplan : arithmeticPlan r = true) :
    eventMass (nativeRequestNullExperiment r hlimits) (nativePrefixRequestReject r hlimits) ≤
      (r.alphaNum : ℝ)/r.alphaDen := by
  rw [nativePrefixRequestReject_eq_frozen]
  exact native_request_type_I r hlimits hplan

theorem native_prefix_reject_admissible (r : Request) (bytes : ByteArray)
    (hplan : arithmeticPlan r = true) (h : nativePrefixReplyReject r bytes) :
    ∃ outs, AdmissibleRankOutput r outs
      (CurveballNativeSamplingPrefix.tapeReplyPrefix r bytes) := by
  rw [CurveballNativeSamplingPrefix.tapeReplyPrefix_eq_frozen]
  exact native_reply_reject_admissible r bytes hplan
    ((nativePrefixReplyReject_iff_frozen r bytes).mp h)

#check @native_prefix_request_type_I
#print axioms native_prefix_request_type_I
#print axioms native_prefix_reject_admissible
#print axioms CurveballNativeSamplingPrefix.mainOptimized_eq_frozen
end
end CurveballVerified
