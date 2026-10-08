import NativeRankKernel

namespace CurveballVerified
noncomputable section
open OAI.Problem315
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def nativeSubsetReserved (n : Nat) (d : Fin n → Nat) (es : CurveballNative.Edges)
    (i j width cap reserve : Nat) (bits : List Bool) : Option (GraphState n d) :=
  (reservedBitsOutput ((CurveballNative.exclusive n es i j).length.choose
    (CurveballNative.left n es i j).length) width cap reserve bits).bind
      (fun rank => nativeRankOutput n d es i j rank.val)

/-- Exact actual native subset unranking and graph trade after the complete
    reserved capped draw. Failure is an output, not a conditioning event. -/
theorem native_reserved_subset_law {n : Nat} {es : CurveballNative.Edges}
    {C : CanonicalGraph n} (href : EdgeRefines es C)
    (hg : CurveballNative.graphValid n es = true)
    {d : Fin n → Nat} (G : GraphState n d)
    (hG : C.toSimpleGraph = G.val) (i j : Fin n) (hij : i ≠ j)
    (width cap reserve : Nat)
    [NeZero ((CurveballNative.exclusive n es i.val j.val).length.choose
      (CurveballNative.left n es i.val j.val).length)]
    (hwidth : (CurveballNative.exclusive n es i.val j.val).length.choose
      (CurveballNative.left n es i.val j.val).length ≤ 2 ^ width)
    (hr : width * cap ≤ reserve) :
    mapLaw (uniformLaw (Tape reserve))
      (fun t => nativeSubsetReserved n d es i.val j.val width cap reserve t.val) =
    mapPartialLaw (cappedWordLaw
      ((CurveballNative.exclusive n es i.val j.val).length.choose
        (CurveballNative.left n es i.val j.val).length) (2 ^ width) cap)
      (fun rank => (nativeRankFiberEquiv href G hG i j hij rank).val) := by
  let bound := (CurveballNative.exclusive n es i.val j.val).length.choose
    (CurveballNative.left n es i.val j.val).length
  have hb : 0 < bound := Nat.pos_of_ne_zero (NeZero.ne bound)
  have hf : (fun t : Tape reserve =>
      nativeSubsetReserved n d es i.val j.val width cap reserve t.val) =
      Option.map (fun rank => (nativeRankFiberEquiv href G hG i j hij rank).val) ∘
        (fun t => reservedBitsOutput bound width cap reserve t.val) := by
    funext t
    cases hs : reservedBitsOutput bound width cap reserve t.val with
    | none => simp [nativeSubsetReserved,bound,hs]
    | some rank =>
      simp only [bound] at hs
      simp only [Function.comp_apply,nativeSubsetReserved,bound,hs,
        Option.bind_some,Option.map_some]
      exact nativeRankOutput_at href hg G hG i j hij rank
  rw [hf,← mapLaw_comp,uniform_reserved_tape_law hb width cap reserve hwidth hr]
  rfl

/-- Each successful native per-pair row mass is dominated by the exact existing
    full-fiber pair kernel, including the original assignment/null trade. -/
theorem native_reserved_subset_dominated {n : Nat} {es : CurveballNative.Edges}
    {C : CanonicalGraph n} (href : EdgeRefines es C)
    (hg : CurveballNative.graphValid n es = true)
    {d : Fin n → Nat} (G H : GraphState n d)
    (hG : C.toSimpleGraph = G.val) (i j : Fin n) (hij : i ≠ j)
    (width cap reserve : Nat)
    [NeZero ((CurveballNative.exclusive n es i.val j.val).length.choose
      (CurveballNative.left n es i.val j.val).length)]
    (hwidth : (CurveballNative.exclusive n es i.val j.val).length.choose
      (CurveballNative.left n es i.val j.val).length ≤ 2 ^ width)
    (hr : width * cap ≤ reserve) :
    (mapLaw (uniformLaw (Tape reserve))
      (fun t => nativeSubsetReserved n d es i.val j.val width cap reserve t.val)).mass
        (some H) ≤ pairKernel {i,j} G H := by
  letI : NeZero (2 ^ width) := ⟨ne_of_gt (by positivity)⟩
  rw [native_reserved_subset_law href hg G hG i j hij width cap reserve hwidth hr]
  have hd := mapPartialLaw_dominated
    (cappedWordLaw ((CurveballNative.exclusive n es i.val j.val).length.choose
      (CurveballNative.left n es i.val j.val).length) (2 ^ width) cap)
    (uniformLaw (Fin ((CurveballNative.exclusive n es i.val j.val).length.choose
      (CurveballNative.left n es i.val j.val).length)))
    (fun rank => (nativeRankFiberEquiv href G hG i j hij rank).val)
    (capped_success_dominated hwidth cap) H
  rw [native_rank_uniform_fiber href G hG i j hij,fiberLaw_mass] at hd
  exact hd

#print axioms native_reserved_subset_law
#print axioms native_reserved_subset_dominated
end
end CurveballVerified
