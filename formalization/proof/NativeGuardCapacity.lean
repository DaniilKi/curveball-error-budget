import NativeGraphCapacity
import NativeRequestCapacity
import NativeConcreteExecution

namespace CurveballVerified
noncomputable section
open CurveballNativeSampling

theorem native_subset_bound_global (r : Request) (es : CurveballNative.Edges)
    (rank : Fin (r.n.choose 2)) :
    nativeSubsetBound r es rank ≤ (r.n-2).choose ((r.n-2)/2) := by
  unfold nativeSubsetBound
  exact native_subset_choose_le_global r.n es _ _
    (ne_of_lt (nativePairEndpoint_spec r.n rank).2)

/-- All arithmetic width/reservation premises of the actual draw/trace/batch
    laws follow from the actual executed request limits. No sampler law, Markov
    property, exchangeability or inference conclusion is a field or hypothesis. -/
theorem native_limits_sampling_capacities (r : Request) (h : withinLimits r = true) :
    SamplingCapacities r := by
  have hh := Bool.and_eq_true_iff.mp h
  have hd := of_decide_eq_true hh.1
  have hn4 : 4 ≤ r.n := hd.1
  have hn26 : r.n ≤ 26 := hd.2.1
  refine ⟨by omega,sampling_pair_bound_capacity r hn26,
    sampling_pair_reserve_capacity r,?_,?_⟩
  · intro es hv rank
    exact sampling_width_capacity _ ((native_subset_bound_global r es rank).trans
      (sampling_central_bound_capacity r.n hn26))
  · intro es hv rank
    exact sampling_subset_reserve_capacity r hn26 _ (native_subset_bound_global r es rank)

theorem native_limits_representation_bound (r : Request) (h : withinLimits r = true) :
    r.n ≤ 1000 := by
  have hh := Bool.and_eq_true_iff.mp h
  have hd := of_decide_eq_true hh.1
  exact hd.2.1.trans (by decide)

#print axioms native_subset_bound_global
#print axioms native_limits_sampling_capacities
#print axioms native_limits_representation_bound
end
end CurveballVerified
