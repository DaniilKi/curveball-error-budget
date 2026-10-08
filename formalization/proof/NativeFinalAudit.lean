import NativeRequestInference

/- Final source-level proof and theorem-statement audit for the frozen runtime.
   Physical compiler/OS byte transport and entropy provenance remain external
   correspondence assumptions; no such hypothesis substitutes for this bound. -/
namespace CurveballVerified
noncomputable section
open OAI.Problem315 CurveballNativeSampling CurveballNativeSamplingBoundary

/-- The actual rejection event supplies the exact successful rendered result
    with the literal budget and rank fields, rather than a free statistic flag. -/
theorem native_reply_reject_admissible (r : Request) (bytes : ByteArray)
    (hplan : arithmeticPlan r = true) (h : nativeReplyReject r bytes) :
    ∃ outs, AdmissibleRankOutput r outs (tapeReply r bytes) := by
  obtain ⟨hsize,outs,count,rest,hbatch,hcomplete,hrank⟩ := h
  have hv := completionGuard_valid hcomplete
  refine ⟨outs, ?_, hv.2.1, ?_, (arithmeticPlan_success hplan).1, ?_⟩
  · exact native_reply_reject_success r bytes ⟨hsize,outs,count,rest,hbatch,hcomplete,hrank⟩
  · have htext : (tapeReply r bytes).text = render r outs count := by
      simp [tapeReply, hsize, hbatch, completionReply, hcomplete]
    simpa only [hv.2.2] using htext
  · simpa only [hv.2.2] using hrank

-- Full theorem type with all explicit arguments and no omitted instance premise.
#check @native_request_type_I
set_option pp.all true in
#check @native_request_type_I
#print axioms native_request_type_I
#print axioms native_reply_reject_admissible
#print nativeRequestDegrees
#print nativeRequestNullExperiment
#print nativeRequestReject
#print nativeReplyReject
#print axioms actual_native_byte_rank_bound
#print axioms native_raw_byte_rank_bound
#print axioms CurveballNativeSamplingBoundary.main_validated_exact_fields
#print axioms CurveballAssurance.ordinary_curveball_gap
#print axioms checked_curveball_tv
#print axioms native_byte_batch_law
#print axioms batch_success_observer
end
end CurveballVerified
