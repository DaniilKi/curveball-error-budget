import ProbabilityProofBundle
import NativeTradeRefinement

/- Exact authored body: NativePairRefinement -/
section
namespace CurveballSubsetVerified

theorem unrankPair_of_list {n rank i j : Nat}
    (h : CurveballNative.unrankSubset (List.range n) 2 rank = some [i,j]) :
    CurveballNative.unrankPair n rank = some (i,j) := by
  simp [CurveballNative.unrankPair,h]

/-- Every valid pair rank reaches an ascending in-range pair. -/
theorem unrankPair_complete (n : Nat) (rank : Fin (n.choose 2)) :
    ∃ i j, CurveballNative.unrankPair n rank.val = some (i,j) ∧ i < j ∧ j < n ∧
      CurveballNative.unrankSubset (List.range n) 2 rank.val = some [i,j] := by
  let r : Fin ((List.range n).length.choose 2) := ⟨rank.val,by simpa using rank.isLt⟩
  have h := unrankSubset_at (List.range n) 2 r
  have hv := unrankSubset_valid h
  obtain ⟨i,j,hij⟩ := List.length_eq_two.mp hv.2
  rw [hij] at h hv
  have hp : List.Pairwise (· < ·) [i,j] := List.pairwise_lt_range.sublist hv.1
  have hijlt : i < j := by simpa using hp
  have hj : j < n := List.mem_range.mp (hv.1.subset (by simp))
  exact ⟨i,j,unrankPair_of_list h,hijlt,hj,h⟩

/-- The native pair output determines the exact subset decoded by the rank. -/
theorem unrankPair_list {n rank i j : Nat}
    (h : CurveballNative.unrankPair n rank = some (i,j)) :
    CurveballNative.unrankSubset (List.range n) 2 rank = some [i,j] := by
  cases hs : CurveballNative.unrankSubset (List.range n) 2 rank with
  | none => simp [CurveballNative.unrankPair,hs] at h
  | some xs =>
    cases xs with
    | nil => simp [CurveballNative.unrankPair,hs] at h
    | cons a rest =>
      cases rest with
      | nil => simp [CurveballNative.unrankPair,hs] at h
      | cons b rest =>
        cases rest with
        | nil =>
          simp [CurveballNative.unrankPair,hs] at h
          obtain ⟨rfl,rfl⟩ := h
          rfl
        | cons c rest => simp [CurveballNative.unrankPair,hs] at h

theorem unrankPair_valid {n rank i j : Nat}
    (h : CurveballNative.unrankPair n rank = some (i,j)) : i < j ∧ j < n := by
  have hv := unrankSubset_valid (unrankPair_list h)
  have hp : List.Pairwise (· < ·) [i,j] := List.pairwise_lt_range.sublist hv.1
  exact ⟨by simpa using hp,List.mem_range.mp (hv.1.subset (by simp))⟩

theorem unrankPair_injective (n : Nat) (r s : Fin (n.choose 2))
    (h : CurveballNative.unrankPair n r.val = CurveballNative.unrankPair n s.val) : r = s := by
  obtain ⟨i,j,hr,_,_,hrlist⟩ := unrankPair_complete n r
  have hs : CurveballNative.unrankPair n s.val = some (i,j) := h.symm.trans hr
  have hslist := unrankPair_list hs
  let r' : Fin ((List.range n).length.choose 2) := ⟨r.val,by simpa using r.isLt⟩
  let s' : Fin ((List.range n).length.choose 2) := ⟨s.val,by simpa using s.isLt⟩
  have he : subsetAt (List.range n) 2 r' = subsetAt (List.range n) 2 s' := by
    apply Subtype.ext
    have hr' := unrankSubset_at (List.range n) 2 r'
    have hs' := unrankSubset_at (List.range n) 2 s'
    exact Option.some.inj (hr'.symm.trans (hrlist.trans hslist.symm) |>.trans hs')
  have heq := (subsetAt_bijective (xs := List.range n) List.nodup_range 2).1 he
  exact Fin.ext (congrArg (fun z : Fin ((List.range n).length.choose 2) => z.val) heq)

#print axioms unrankPair_complete
#print axioms unrankPair_list
#print axioms unrankPair_valid
#print axioms unrankPair_injective
end CurveballSubsetVerified

end

/- Exact authored body: NativeDecodedTrade -/
section
namespace CurveballVerified
open CurveballSubsetVerified

/-- The actual binomial decoder supplies all chosen-list runtime guards. No
    arbitrary legal-list or output-validity premise is substituted for decoding. -/
theorem decoded_subset_legal (n : Nat) (es : CurveballNative.Edges) (i j : Fin n)
    (rank : Fin ((CurveballNative.exclusive n es i.val j.val).length.choose
      (CurveballNative.left n es i.val j.val).length)) :
    ∃ chosen, CurveballNative.unrankSubset (CurveballNative.exclusive n es i.val j.val)
      (CurveballNative.left n es i.val j.val).length rank.val = some chosen ∧
      chosen.Nodup ∧
      (∀ v ∈ chosen, v < n ∧ v ∈ CurveballNative.exclusive n es i.val j.val) ∧
      chosen.length = (CurveballNative.left n es i.val j.val).length := by
  let xs := CurveballNative.exclusive n es i.val j.val
  let k := (CurveballNative.left n es i.val j.val).length
  let chosen := (subsetAt xs k rank).val
  have hu := unrankSubset_at xs k rank
  have hv := unrankSubset_valid hu
  have hn : xs.Nodup := by
    exact List.nodup_range.filter _
  refine ⟨chosen,hu,hn.sublist hv.1,?_,hv.2⟩
  intro v hm
  have hp := hv.1.subset hm
  refine ⟨?_,hp⟩
  exact List.mem_range.mp (List.mem_filter.mp hp).1

theorem decoded_trade_refines {n : Nat} {es : CurveballNative.Edges}
    {G : CanonicalGraph n} (href : EdgeRefines es G)
    (hg : CurveballNative.graphValid n es = true) (i j : Fin n) (hij : i ≠ j)
    (rank : Fin ((CurveballNative.exclusive n es i.val j.val).length.choose
      (CurveballNative.left n es i.val j.val).length)) :
    ∃ chosen out, CurveballNative.unrankSubset (CurveballNative.exclusive n es i.val j.val)
      (CurveballNative.left n es i.val j.val).length rank.val = some chosen ∧
      CurveballNative.trade n es i.val j.val chosen = some out ∧
      ∃ H : CanonicalGraph n, EdgeRefines out H ∧
        ∃ hT : chosenSet n chosen ⊆ OAI.Problem315.PairFiber.singletonSet G.toSimpleGraph i j,
          H.toSimpleGraph = OAI.Problem315.PairFiber.trade G.toSimpleGraph i j hij
            (chosenSet n chosen) hT ∧ ∀ v : Fin n, H.degree v = G.degree v := by
  obtain ⟨chosen,hu,hd,hr,hc⟩ := decoded_subset_legal n es i j rank
  obtain ⟨out,hout,H,href',hgraph,hdeg⟩ := native_trade_refines href hg i j hij chosen hd hr hc
  have hT : chosenSet n chosen ⊆ OAI.Problem315.PairFiber.singletonSet G.toSimpleGraph i j := by
    rw [← exclusive_refines]
    intro v hv
    exact (native_exclusive_refines href i j v).mp
      (hr v.val (by simpa [chosenSet] using hv)).2
  exact ⟨chosen,out,hu,hout,H,href',hT,hgraph,hdeg⟩

#print axioms decoded_subset_legal
#print axioms decoded_trade_refines

end CurveballVerified

end

