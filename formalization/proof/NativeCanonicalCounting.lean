import NativeCardinality

namespace CurveballVerified
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def nativeEdgeVals {n : Nat} (e : Fin n × Fin n) : Nat × Nat := (e.1.val,e.2.val)

theorem nativeEdgeVals_injective (n : Nat) :
    Function.Injective (nativeEdgeVals (n := n)) := by
  intro a b h
  apply Prod.ext
  · exact Fin.ext (congrArg Prod.fst h)
  · exact Fin.ext (congrArg Prod.snd h)

theorem native_canonical_edges_image (n : Nat) (es : CurveballNative.Edges)
    (hv : CurveballNative.graphValid n es = true) :
    (canonicalOfNative n es hv).edges.image nativeEdgeVals = es.toFinset := by
  ext e
  constructor
  · intro he
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
    have hm : nativeEdgeVals p ∈ es := by simpa [canonicalOfNative,nativeEdgeVals] using hp
    exact List.mem_toFinset.mpr hm
  · intro he
    have hm := List.mem_toFinset.mp he
    have hb := ((native_graphValid_iff n es).mp hv).2.2 e hm
    refine Finset.mem_image.mpr
      ⟨(⟨e.1,lt_trans hb.1 hb.2⟩,⟨e.2,hb.2⟩),?_,rfl⟩
    simpa [canonicalOfNative] using hm

theorem native_length_canonical_card (n : Nat) (es : CurveballNative.Edges)
    (hv : CurveballNative.graphValid n es = true) :
    es.length = (canonicalOfNative n es hv).edges.card := by
  calc
    es.length = es.toFinset.card :=
      (List.toFinset_card_of_nodup ((native_graphValid_iff n es).mp hv).2.1).symm
    _ = ((canonicalOfNative n es hv).edges.image nativeEdgeVals).card :=
      congrArg Finset.card (native_canonical_edges_image n es hv).symm
    _ = (canonicalOfNative n es hv).edges.card :=
      Finset.card_image_of_injective _ (nativeEdgeVals_injective n)

/-- Canonical oriented storage has exactly one element per undirected edge. -/
theorem native_canonical_card_edgeFinset {n : Nat} (C : CanonicalGraph n) :
    C.edges.card = C.toSimpleGraph.edgeFinset.card := by
  classical
  apply Finset.card_bij (fun e _ => s(e.1,e.2))
  · intro e he
    rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
    exact Or.inl he
  · intro a ha b hb hab
    rcases Sym2.eq_iff.mp hab with h | h
    · exact Prod.ext h.1 h.2
    · have hforward := C.canonical a ha
      have hback : a.2 < a.1 := by
        simpa only [h.1,h.2] using C.canonical b hb
      exact False.elim ((lt_asymm hforward) hback)
  · intro e
    refine Sym2.inductionOn e ?_
    intro u v he
    have hadj : C.toSimpleGraph.Adj u v := by
      simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using he
    rcases hadj with huv | hvu
    · exact ⟨(u,v),huv,rfl⟩
    · exact ⟨(v,u),hvu,Sym2.eq_iff.mpr (Or.inr ⟨rfl,rfl⟩)⟩

theorem native_length_edgeFinset (n : Nat) (es : CurveballNative.Edges)
    (hv : CurveballNative.graphValid n es = true) :
    es.length = (canonicalOfNative n es hv).toSimpleGraph.edgeFinset.card :=
  (native_length_canonical_card n es hv).trans
    (native_canonical_card_edgeFinset (canonicalOfNative n es hv))

theorem native_canonical_eq_of_refines {n : Nat} {es : CurveballNative.Edges}
    {C D : CanonicalGraph n} (hC : EdgeRefines es C) (hD : EdgeRefines es D) :
    C.toSimpleGraph = D.toSimpleGraph := by
  ext u v
  exact (native_adjacent_refines hC u v).symm.trans (native_adjacent_refines hD u v)

#print axioms native_length_canonical_card
#print axioms native_canonical_card_edgeFinset
#print axioms native_length_edgeFinset
end
end CurveballVerified
