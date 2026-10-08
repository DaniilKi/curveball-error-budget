import NativeGraph
import NativeSuccess
import CanonicalGraphLite

namespace CurveballVerified

/-- Exact membership relation between an executable edge list and the already
    proved canonical graph. It is a refinement predicate, not a sampling axiom. -/
def EdgeRefines {n : Nat} (es : CurveballNative.Edges) (G : CanonicalGraph n) : Prop :=
  ∀ u v : Fin n, (u.val,v.val) ∈ es ↔ (u,v) ∈ G.edges

theorem native_adjacent_refines {n : Nat} {es : CurveballNative.Edges}
    {G : CanonicalGraph n} (h : EdgeRefines es G) (u v : Fin n) :
    CurveballNative.adjacent es u.val v.val = true ↔ G.toSimpleGraph.Adj u v := by
  simp only [CurveballNative.adjacent, decide_eq_true_eq,
    CanonicalGraph.toSimpleGraph, h u v, h v u]

theorem native_outside_refines {n : Nat} (i j v : Fin n) :
    CurveballNative.outside i.val j.val v.val = true ↔ outside i j v := by
  simp [CurveballNative.outside, outside, Fin.ext_iff]

theorem native_adjacent_false_refines {n : Nat} {es : CurveballNative.Edges}
    {G : CanonicalGraph n} (h : EdgeRefines es G) (u v : Fin n) :
    CurveballNative.adjacent es u.val v.val = false ↔ ¬ G.toSimpleGraph.Adj u v := by
  have hh := native_adjacent_refines h u v
  cases ha : CurveballNative.adjacent es u.val v.val <;> simp_all

theorem native_common_refines {n : Nat} {es : CurveballNative.Edges}
    {G : CanonicalGraph n} (h : EdgeRefines es G) (i j v : Fin n) :
    v.val ∈ CurveballNative.common n es i.val j.val ↔ v ∈ common G i j := by
  simp [CurveballNative.common_mem, common, v.isLt, outside, Fin.ext_iff,
    native_adjacent_refines h]

theorem native_left_refines {n : Nat} {es : CurveballNative.Edges}
    {G : CanonicalGraph n} (h : EdgeRefines es G) (i j v : Fin n) :
    v.val ∈ CurveballNative.left n es i.val j.val ↔ v ∈ left G i j := by
  simp [CurveballNative.left_mem, left, v.isLt, outside, Fin.ext_iff,
    native_adjacent_refines h,native_adjacent_false_refines h]

theorem native_exclusive_refines {n : Nat} {es : CurveballNative.Edges}
    {G : CanonicalGraph n} (h : EdgeRefines es G) (i j v : Fin n) :
    v.val ∈ CurveballNative.exclusive n es i.val j.val ↔ v ∈ exclusive G i j := by
  simp [CurveballNative.exclusive_mem, exclusive, v.isLt, outside, Fin.ext_iff,
    native_adjacent_refines h,native_adjacent_false_refines h]

theorem native_possibleEdges_mem (n u v : Nat) :
    (u,v) ∈ CurveballNative.possibleEdges n ↔ u < n ∧ v < n ∧ u < v := by
  exact CurveballNative.possibleEdges_mem n u v

def chosenSet (n : Nat) (xs : List Nat) : Finset (Fin n) :=
  Finset.univ.filter fun v => v.val ∈ xs

theorem native_tradeAdjacent_refines {n : Nat} {es : CurveballNative.Edges}
    {G : CanonicalGraph n} (h : EdgeRefines es G) (i j u v : Fin n)
    (chosen : List Nat) :
    CurveballNative.tradeAdjacent n es i.val j.val chosen u.val v.val = true ↔
      tradeRelation G i j (chosenSet n chosen) u v := by
  simp [CurveballNative.tradeAdjacent, tradeRelation, chosenSet,
    native_common_refines h, native_exclusive_refines h,
    native_adjacent_refines h, native_outside_refines, Fin.ext_iff, and_assoc, or_assoc]

#print axioms native_adjacent_refines
#print axioms native_common_refines
#print axioms native_left_refines
#print axioms native_exclusive_refines
#print axioms native_possibleEdges_mem
#print axioms native_tradeAdjacent_refines
end CurveballVerified
