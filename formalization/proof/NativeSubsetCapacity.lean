import NativeDrawRow

namespace CurveballVerified
noncomputable section
open OAI.Problem315 OAI.Problem315.PairFiber CurveballNativeSampling

/-- The actual decoded subset bound is positive because the original left
    assignment is present. This includes singleton fibers and null trades. -/
theorem native_subset_bound_positive {n : Nat} {es : CurveballNative.Edges}
    {C : CanonicalGraph n} (href : EdgeRefines es C)
    {d : Fin n → Nat} (G : GraphState n d) (hG : C.toSimpleGraph = G.val)
    (i j : Fin n) : 0 <
      (CurveballNative.exclusive n es i.val j.val).length.choose
        (CurveballNative.left n es i.val j.val).length := by
  let T : OAI.Problem315.PairFiber.Assignment G.val i j :=
    ⟨leftSet G.val i j,leftSet_subset_singletonSet G.val i j,rfl⟩
  let rank := (nativeSubsetEquiv href G hG i j).symm T
  exact Nat.lt_of_le_of_lt (Nat.zero_le rank.val) rank.isLt

theorem native_all_pair_bounds_positive (r : Request) (es : CurveballNative.Edges)
    (C : CanonicalGraph r.n) (href : EdgeRefines es C)
    {d : Fin r.n → Nat} (G : GraphState r.n d) (hG : C.toSimpleGraph = G.val) :
    ∀ rank : Fin (r.n.choose 2), 0 < nativeSubsetBound r es rank := by
  intro rank
  exact native_subset_bound_positive href G hG _ _

#print axioms native_subset_bound_positive
#print axioms native_all_pair_bounds_positive
end
end CurveballVerified
