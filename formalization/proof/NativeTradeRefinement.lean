import NativeCardinality

namespace CurveballVerified

def nativeMaterialize (n : Nat) (es : CurveballNative.Edges) (i j : Nat)
    (chosen : List Nat) : CurveballNative.Edges :=
  (CurveballNative.possibleEdges n).filter fun e =>
    CurveballNative.tradeAdjacent n es i j chosen e.1 e.2

theorem native_possibleEdges_nodup (n : Nat) :
    (CurveballNative.possibleEdges n).Nodup := by
  unfold CurveballNative.possibleEdges
  apply List.nodup_flatMap.mpr
  constructor
  · intro i hi
    apply List.Nodup.map
    · intro a b hab
      exact congrArg Prod.snd hab
    · exact List.nodup_range.filter _
  · have hr : List.Pairwise (fun i j : Nat => i ≠ j) (List.range n) :=
      List.nodup_range
    apply hr.imp
    intro i j hij
    apply List.disjoint_left.mpr
    intro e he hf
    obtain ⟨a,ha,he⟩ := List.mem_map.mp he
    obtain ⟨b,hb,hf⟩ := List.mem_map.mp hf
    exact hij (by simpa using congrArg Prod.fst (he.trans hf.symm))

theorem nativeMaterialize_valid (n : Nat) (es : CurveballNative.Edges)
    (i j : Nat) (chosen : List Nat) (hn : n ≤ 1000) :
    CurveballNative.graphValid n (nativeMaterialize n es i j chosen) = true := by
  apply (native_graphValid_iff _ _).mpr
  refine ⟨hn,(native_possibleEdges_nodup n).filter _,?_⟩
  intro e he
  have hp := (List.mem_filter.mp he).1
  have hb := (native_possibleEdges_mem n e.1 e.2).mp hp
  exact ⟨hb.2.2,hb.2.1⟩

theorem nativeMaterialize_refines {n : Nat} {es : CurveballNative.Edges}
    {G : CanonicalGraph n} (h : EdgeRefines es G) (i j : Fin n)
    (hij : i ≠ j) (chosen : List Nat)
    (hT : chosenSet n chosen ⊆ exclusive G i j) :
    EdgeRefines (nativeMaterialize n es i.val j.val chosen)
      (executeTrade G i j hij (chosenSet n chosen) hT) := by
  intro u v
  simp [nativeMaterialize,native_possibleEdges_mem,u.isLt,v.isLt,
    native_tradeAdjacent_refines h,executeTrade,fromRelation]

theorem native_trade_valid {n : Nat} {es : CurveballNative.Edges}
    (hg : CurveballNative.graphValid n es = true) (i j : Fin n)
    (hij : i ≠ j) (chosen : List Nat) (hd : chosen.Nodup)
    (hr : ∀ v ∈ chosen, v < n ∧ v ∈ CurveballNative.exclusive n es i.val j.val)
    (hc : chosen.length = (CurveballNative.left n es i.val j.val).length) :
    CurveballNative.trade n es i.val j.val chosen =
      some (nativeMaterialize n es i.val j.val chosen) := by
  have hn := (native_graphValid_iff n es).mp hg |>.1
  have hv : i.val < n ∧ j.val < n ∧ i.val ≠ j.val ∧ chosen.Nodup ∧
      ∀ v ∈ chosen, v < n ∧ v ∈ CurveballNative.exclusive n es i.val j.val :=
    ⟨i.isLt,j.isLt,fun he => hij (Fin.ext he),hd,hr⟩
  have hout := nativeMaterialize_valid n es i.val j.val chosen hn
  dsimp only [nativeMaterialize] at hout
  simpa [CurveballNative.trade,hg,hv,hc,nativeMaterialize,hout] using hr

/-- Arbitrary valid draws refine the credited upstream full-fiber trade. -/
theorem native_trade_refines {n : Nat} {es : CurveballNative.Edges}
    {G : CanonicalGraph n} (h : EdgeRefines es G)
    (hg : CurveballNative.graphValid n es = true) (i j : Fin n)
    (hij : i ≠ j) (chosen : List Nat) (hd : chosen.Nodup)
    (hr : ∀ v ∈ chosen, v < n ∧ v ∈ CurveballNative.exclusive n es i.val j.val)
    (hc : chosen.length = (CurveballNative.left n es i.val j.val).length) :
    ∃ out, CurveballNative.trade n es i.val j.val chosen = some out ∧
      ∃ H : CanonicalGraph n, EdgeRefines out H ∧
        H.toSimpleGraph = OAI.Problem315.PairFiber.trade G.toSimpleGraph i j hij
          (chosenSet n chosen) (by
            rw [← exclusive_refines]
            intro v hv
            exact (native_exclusive_refines h i j v).mp
              (hr v.val (by simpa [chosenSet] using hv)).2) ∧
        ∀ v : Fin n, H.degree v = G.degree v := by
  have hT : chosenSet n chosen ⊆ exclusive G i j := by
    intro v hv
    exact (native_exclusive_refines h i j v).mp
      (hr v.val (by simpa [chosenSet] using hv)).2
  have hcard : (chosenSet n chosen).card = (left G i j).card := by
    rw [chosenSet_card n chosen hd (fun v hv => (hr v hv).1),hc,native_left_card h]
  refine ⟨nativeMaterialize n es i.val j.val chosen,
    native_trade_valid hg i j hij chosen hd hr hc,
    executeTrade G i j hij (chosenSet n chosen) hT,
    nativeMaterialize_refines h i j hij chosen hT,
    executeTrade_refines G i j hij (chosenSet n chosen) hT,?_⟩
  exact executeTrade_degree G i j hij (chosenSet n chosen) hT hcard

#print axioms native_possibleEdges_nodup
#print axioms nativeMaterialize_valid
#print axioms nativeMaterialize_refines
#print axioms native_trade_valid
#print axioms native_trade_refines

theorem native_trade_success_checks {n : Nat} {es out : CurveballNative.Edges}
    {a b : Nat} {chosen : List Nat}
    (ht : CurveballNative.trade n es a b chosen = some out) :
    CurveballNative.graphValid n es = true ∧
    (a < n ∧ b < n ∧ a ≠ b ∧ chosen.Nodup ∧
      ∀ v ∈ chosen, v < n ∧ v ∈ CurveballNative.exclusive n es a b) ∧
    chosen.length = (CurveballNative.left n es a b).length ∧
    out = nativeMaterialize n es a b chosen ∧
    CurveballNative.graphValid n out = true := by
  obtain ⟨hg,hv,hc⟩ := CurveballNative.trade_success_checks ht
  let i : Fin n := ⟨a,hv.1⟩
  let j : Fin n := ⟨b,hv.2.1⟩
  have hij : i ≠ j := fun he => hv.2.2.1 (congrArg Fin.val he)
  have hm := native_trade_valid hg i j hij chosen hv.2.2.2.1 hv.2.2.2.2 hc
  have he : out = nativeMaterialize n es a b chosen := Option.some.inj (ht.symm.trans hm)
  exact ⟨hg,hv,hc,he,CurveballNative.trade_success_valid ht⟩

theorem native_step_success_refines {n : Nat} {es out : CurveballNative.Edges}
    {G : CanonicalGraph n} (h : EdgeRefines es G) {a b : Nat} {chosen : List Nat}
    (ht : CurveballNative.trade n es a b chosen = some out) :
    ∃ H : CanonicalGraph n, EdgeRefines out H ∧
      CurveballNative.graphValid n out = true ∧
      ∀ v : Fin n, H.degree v = G.degree v := by
  obtain ⟨hg,⟨ha,hb,hab,hd,hr⟩,hc,he,hout⟩ := native_trade_success_checks ht
  let i : Fin n := ⟨a,ha⟩
  let j : Fin n := ⟨b,hb⟩
  have hij : i ≠ j := fun h => hab (congrArg Fin.val h)
  obtain ⟨res,hres,H,href,hgraph,hdeg⟩ :=
    native_trade_refines h hg i j hij chosen hd hr hc
  have heq : res = out := Option.some.inj (hres.symm.trans ht)
  exact ⟨H,heq ▸ href,hout,hdeg⟩

#print axioms native_trade_success_checks
#print axioms native_step_success_refines
end CurveballVerified
