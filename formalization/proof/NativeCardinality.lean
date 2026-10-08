import NativeGraphProof

namespace CurveballVerified

theorem native_graphValid_iff (n : Nat) (es : CurveballNative.Edges) :
    CurveballNative.graphValid n es = true ↔
      n ≤ 1000 ∧ es.Nodup ∧ ∀ e ∈ es, e.1 < e.2 ∧ e.2 < n := by
  simp [CurveballNative.graphValid]

/-- Proof-side canonical witness, not an executed alternative implementation. -/
def canonicalOfNative (n : Nat) (es : CurveballNative.Edges)
    (hv : CurveballNative.graphValid n es = true) : CanonicalGraph n where
  edges := Finset.univ.filter fun e => (e.1.val,e.2.val) ∈ es
  canonical := by
    intro e he
    have hm := (Finset.mem_filter.mp he).2
    exact ((native_graphValid_iff n es).mp hv).2.2 _ hm |>.1

theorem canonicalOfNative_refines (n : Nat) (es : CurveballNative.Edges)
    (hv : CurveballNative.graphValid n es = true) :
    EdgeRefines es (canonicalOfNative n es hv) := by
  intro u v
  simp [canonicalOfNative]

theorem chosenSet_val_image (n : Nat) (xs : List Nat)
    (hr : ∀ v ∈ xs, v < n) :
    (chosenSet n xs).image Fin.val = xs.toFinset := by
  ext v
  constructor
  · intro hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    simpa [chosenSet] using hw
  · intro hv
    have hm : v ∈ xs := List.mem_toFinset.mp hv
    refine Finset.mem_image.mpr ⟨⟨v,hr v hm⟩,?_,rfl⟩
    simpa [chosenSet] using hm

theorem chosenSet_card (n : Nat) (xs : List Nat)
    (hn : xs.Nodup) (hr : ∀ v ∈ xs, v < n) :
    (chosenSet n xs).card = xs.length := by
  calc
    _ = ((chosenSet n xs).image Fin.val).card :=
      (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ = xs.toFinset.card := congrArg Finset.card (chosenSet_val_image n xs hr)
    _ = xs.length := List.toFinset_card_of_nodup hn

theorem native_left_set {n : Nat} {es : CurveballNative.Edges}
    {G : CanonicalGraph n} (h : EdgeRefines es G) (i j : Fin n) :
    chosenSet n (CurveballNative.left n es i.val j.val) = left G i j := by
  ext v
  simp [chosenSet,native_left_refines h]

theorem native_exclusive_set {n : Nat} {es : CurveballNative.Edges}
    {G : CanonicalGraph n} (h : EdgeRefines es G) (i j : Fin n) :
    chosenSet n (CurveballNative.exclusive n es i.val j.val) = exclusive G i j := by
  ext v
  simp [chosenSet,native_exclusive_refines h]

theorem native_left_card {n : Nat} {es : CurveballNative.Edges}
    {G : CanonicalGraph n} (h : EdgeRefines es G) (i j : Fin n) :
    (CurveballNative.left n es i.val j.val).length = (left G i j).card := by
  rw [← native_left_set h]
  symm
  apply chosenSet_card
  · exact List.nodup_range.filter _
  · intro v hv
    exact List.mem_range.mp (List.mem_filter.mp hv).1

theorem native_degree_refines {n : Nat} {es : CurveballNative.Edges}
    {G : CanonicalGraph n} (h : EdgeRefines es G) (v : Fin n) :
    CurveballNative.degree n es v.val = G.degree v := by
  let xs := (List.range n).filter (CurveballNative.adjacent es v.val)
  have hr : ∀ w ∈ xs, w < n := by
    intro w hw
    exact List.mem_range.mp (List.mem_filter.mp hw).1
  have hc := chosenSet_card n xs (List.nodup_range.filter _) hr
  have he : chosenSet n xs = Finset.univ.filter (G.toSimpleGraph.Adj v) := by
    ext w
    simp [chosenSet,xs,w.isLt,native_adjacent_refines h]
  simpa [CurveballNative.degree,CanonicalGraph.degree,xs,he] using hc.symm

#print axioms native_graphValid_iff
#print axioms canonicalOfNative_refines
#print axioms chosenSet_card
#print axioms native_left_card
#print axioms native_degree_refines
end CurveballVerified
