import NativeCardinality

namespace CurveballVerified

/-- Each ordered i<j<k triple contributes once exactly when its three edges exist. -/
def canonicalTriangles {n : Nat} (G : CanonicalGraph n) : Nat :=
  ((List.finRange n).flatMap fun i =>
    (List.finRange n).flatMap fun j =>
      (List.finRange n).filter fun k => decide (i < j) && decide (j < k) &&
        decide (G.toSimpleGraph.Adj i j) && decide (G.toSimpleGraph.Adj i k) &&
        decide (G.toSimpleGraph.Adj j k)).length

theorem range_eq_finRange_values (n : Nat) :
    List.range n = (List.finRange n).map Fin.val := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem native_adjacent_eq_decide {n : Nat} {es : CurveballNative.Edges}
    {G : CanonicalGraph n} (h : EdgeRefines es G) (u v : Fin n) :
    CurveballNative.adjacent es u.val v.val = decide (G.toSimpleGraph.Adj u v) := by
  have hh := native_adjacent_refines h u v
  cases ha : CurveballNative.adjacent es u.val v.val <;> simp_all

theorem native_triangles_refines {n : Nat} {es : CurveballNative.Edges}
    {G : CanonicalGraph n} (h : EdgeRefines es G) :
    CurveballNative.triangles n es = canonicalTriangles G := by
  unfold CurveballNative.triangles canonicalTriangles
  simp only [range_eq_finRange_values,List.flatMap_map,List.filter_map,
    ← List.map_flatMap,List.length_map,Function.comp_def,Fin.lt_def,
    native_adjacent_eq_decide h]

#print axioms native_triangles_refines
end CurveballVerified
