import AnalyticSliceProjection

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairTradeSwitch.lean -/
section

namespace OAI

noncomputable section

namespace Problem315.PairFiber

theorem fourVertexState_key {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i u v j : Fin n) (h : FourDistinct i u v j)
    (hiu : G.val.Adj i u) (hvj : G.val.Adj v j)
    (hiv : ¬ G.val.Adj i v) (huj : ¬ G.val.Adj u j) :
    key i j (fourVertexState G i u v j h).val = key i j G.val := by
  classical
  have hl (w : Fin n) : (fourVertexState G i u v j h).val.Adj i w ↔
      (G.val.Adj i w ∧ w ≠ u) ∨ w = v :=
    proposalResult_fourVertex_adj_first G.val i u v j h hiu hvj hiv huj w
  have hr (w : Fin n) : (fourVertexState G i u v j h).val.Adj j w ↔
      (G.val.Adj j w ∧ w ≠ v) ∨ w = u := by
    simpa [fourVertexState, h.2.2.1.symm, h.2.2.2.2.1.symm, h.2.2.2.2.2.symm] using
      proposalResult_fourVertex_adj G.val i u v j h hiu hvj hiv huj j w
  apply key_eq_of
  · intro x y hx hy
    change (proposalResult G.val (fourVertexProposal i u v j h)).Adj x y ↔ _
    rw [proposalResult_fourVertex_adj G.val i u v j h hiu hvj hiv huj]
    simp [hx.1, hx.2, hy.1, hy.2]
  · rw [hl]
    simp [h.2.2.2.2.1.symm, h.2.2.2.2.2.symm]
  · intro w
    have hju : ¬ G.val.Adj j u := fun hadj => huj hadj.symm
    have hjv : G.val.Adj j v := hvj.symm
    by_cases hwu : w = u
    · subst w
      simp [edgeBit, hl, hr, hiu, hju, h.2.2.2.1]
    by_cases hwv : w = v
    · subst w
      simp [edgeBit, hl, hr, hiv, hjv, h.2.2.2.1.symm]
    simp [edgeBit, hl, hr, hwu, hwv]

theorem fourVertexState_leftSet {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i u v j : Fin n) (h : FourDistinct i u v j)
    (hiu : G.val.Adj i u) (hvj : G.val.Adj v j)
    (hiv : ¬ G.val.Adj i v) (huj : ¬ G.val.Adj u j) :
    leftSet (fourVertexState G i u v j h).val i j =
      insert v ((leftSet G.val i j).erase u) := by
  classical
  have hl (w : Fin n) : (fourVertexState G i u v j h).val.Adj i w ↔
      (G.val.Adj i w ∧ w ≠ u) ∨ w = v :=
    proposalResult_fourVertex_adj_first G.val i u v j h hiu hvj hiv huj w
  have hr (w : Fin n) : (fourVertexState G i u v j h).val.Adj j w ↔
      (G.val.Adj j w ∧ w ≠ v) ∨ w = u := by
    simpa [fourVertexState, h.2.2.1.symm, h.2.2.2.2.1.symm, h.2.2.2.2.2.symm] using
      proposalResult_fourVertex_adj G.val i u v j h hiu hvj hiv huj j w
  ext w
  simp only [mem_leftSet, Finset.mem_insert, Finset.mem_erase, hl, hr]
  by_cases hwu : w = u
  · subst w
    simp [h.2.2.2.1]
  by_cases hwv : w = v
  · subst w
    simp [Outside, h.2.1.symm, h.2.2.2.2.2, h.2.2.2.1.symm]
  simp [hwu, hwv, and_comm]

theorem exchange_leftSet_subset {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i u v j : Fin n) (h : FourDistinct i u v j)
    (hvj : G.val.Adj v j) (hiv : ¬ G.val.Adj i v) :
    insert v ((leftSet G.val i j).erase u) ⊆ singletonSet G.val i j := by
  classical
  intro w hw
  rcases Finset.mem_insert.mp hw with hw | hw
  · subst w
    exact (mem_singletonSet G.val i j v).mpr
      ⟨⟨h.2.1.symm, h.2.2.2.2.2⟩, Or.inr ⟨hvj.symm, hiv⟩⟩
  · exact leftSet_subset_singletonSet G.val i j (Finset.mem_of_mem_erase hw)

theorem trade_exchange_eq_fourVertexState {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i u v j : Fin n) (h : FourDistinct i u v j)
    (hiu : G.val.Adj i u) (hvj : G.val.Adj v j)
    (hiv : ¬ G.val.Adj i v) (huj : ¬ G.val.Adj u j) :
    trade G.val i j h.2.2.1 (insert v ((leftSet G.val i j).erase u))
      (exchange_leftSet_subset G i u v j h hvj hiv) =
        (fourVertexState G i u v j h).val := by
  apply graph_eq_of_key_leftSet_eq
  · exact (key_trade _ _ _ _ _ _).trans
      (fourVertexState_key G i u v j h hiu hvj hiv huj).symm
  · rw [leftSet_trade, fourVertexState_leftSet G i u v j h hiu hvj hiv huj]

theorem switchStep_of_trade_exchange {n : ℕ} {d : Fin n → ℕ}
    (G H : GraphState n d) (i u v j : Fin n) (h : FourDistinct i u v j)
    (hiu : G.val.Adj i u) (hvj : G.val.Adj v j)
    (hiv : ¬ G.val.Adj i v) (huj : ¬ G.val.Adj u j)
    (hH : H.val = trade G.val i j h.2.2.1
      (insert v ((leftSet G.val i j).erase u))
      (exchange_leftSet_subset G i u v j h hvj hiv)) :
    SwitchStep n d G H := by
  have heq : H = fourVertexState G i u v j h := Subtype.ext
    (hH.trans (trade_exchange_eq_fourVertexState G i u v j h hiu hvj hiv huj))
  rw [heq]
  exact switchStep_fourVertexState G i u v j h hiu hvj hiv huj

theorem switchStep_of_key_leftSet_exchange {n : ℕ} {d : Fin n → ℕ}
    (G H : GraphState n d) (i j u v : Fin n) (hij : i ≠ j)
    (hu : u ∈ leftSet G.val i j) (hv : v ∈ singletonSet G.val i j)
    (hvn : v ∉ leftSet G.val i j)
    (hkey : key i j H.val = key i j G.val)
    (hleft : leftSet H.val i j = insert v ((leftSet G.val i j).erase u)) :
    SwitchStep n d G H := by
  classical
  obtain ⟨huo, hiu, hju⟩ := (mem_leftSet G.val i j u).mp hu
  obtain ⟨hvo, hvxor⟩ := (mem_singletonSet G.val i j v).mp hv
  have hvright : G.val.Adj j v ∧ ¬ G.val.Adj i v := by
    rcases hvxor with hvleft | hvright
    · exact False.elim (hvn ((mem_leftSet G.val i j v).mpr ⟨hvo, hvleft⟩))
    · exact hvright
  have huv : u ≠ v := by
    intro heq
    exact hvn (heq ▸ hu)
  have hdist : FourDistinct i u v j :=
    ⟨huo.1.symm, hvo.1.symm, hij, huv, huo.2, hvo.2⟩
  have huj : ¬ G.val.Adj u j := fun he => hju he.symm
  have heq : H = fourVertexState G i u v j hdist := by
    apply Subtype.ext
    apply graph_eq_of_key_leftSet_eq
    · exact hkey.trans
        (fourVertexState_key G i u v j hdist hiu hvright.1.symm hvright.2 huj).symm
    · exact hleft.trans
        (fourVertexState_leftSet G i u v j hdist hiu hvright.1.symm hvright.2 huj).symm
  rw [heq]
  exact switchStep_fourVertexState G i u v j hdist hiu hvright.1.symm hvright.2 huj

theorem map_swap_eq_exchange {V : Type*} [DecidableEq V]
    (A : Finset V) (u v : V) (hu : u ∈ A) (hv : v ∉ A) :
    A.map (Equiv.swap u v).toEmbedding = insert v (A.erase u) := by
  classical
  have huv : u ≠ v := fun heq => hv (heq ▸ hu)
  ext w
  simp only [Finset.mem_map_equiv, Equiv.symm_swap,
    Finset.mem_insert, Finset.mem_erase]
  by_cases hwu : w = u
  · subst w
    simp [huv, hv]
  by_cases hwv : w = v
  · subst w
    simp [hu]
  simp [Equiv.swap_apply_of_ne_of_ne hwu hwv, hwu, hwv]

theorem map_swap_eq_self_of_mem_iff {V : Type*} [DecidableEq V]
    (A : Finset V) (u v : V) (hmem : u ∈ A ↔ v ∈ A) :
    A.map (Equiv.swap u v).toEmbedding = A := by
  classical
  ext w
  simp only [Finset.mem_map_equiv, Equiv.symm_swap]
  by_cases hwu : w = u
  · subst w
    simpa using hmem.symm
  by_cases hwv : w = v
  · subst w
    simpa using hmem
  rw [Equiv.swap_apply_of_ne_of_ne hwu hwv]

theorem eq_or_switchStep_of_key_leftSet_swap {n : ℕ} {d : Fin n → ℕ}
    (G H : GraphState n d) (i j u v : Fin n) (hij : i ≠ j)
    (hu : u ∈ singletonSet G.val i j) (hv : v ∈ singletonSet G.val i j)
    (hkey : key i j H.val = key i j G.val)
    (hleft : leftSet H.val i j =
      (leftSet G.val i j).map (Equiv.swap u v).toEmbedding) :
    G = H ∨ SwitchStep n d G H := by
  classical
  by_cases hul : u ∈ leftSet G.val i j
  · by_cases hvl : v ∈ leftSet G.val i j
    · left
      apply Subtype.ext
      apply graph_eq_of_key_leftSet_eq hkey.symm
      rw [hleft, map_swap_eq_self_of_mem_iff _ u v (by simp [hul, hvl])]
    · right
      exact switchStep_of_key_leftSet_exchange G H i j u v hij hul hv hvl hkey
        (hleft.trans (map_swap_eq_exchange _ u v hul hvl))
  · by_cases hvl : v ∈ leftSet G.val i j
    · right
      apply switchStep_of_key_leftSet_exchange G H i j v u hij hvl hu hul hkey
      rw [hleft, Equiv.swap_comm u v]
      exact map_swap_eq_exchange _ v u hvl hul
    · left
      apply Subtype.ext
      apply graph_eq_of_key_leftSet_eq hkey.symm
      rw [hleft, map_swap_eq_self_of_mem_iff _ u v (by simp [hul, hvl])]

theorem fourVertexProposal_mem_crossingPairs {n : ℕ}
    (i u v j : Fin n) (h : FourDistinct i u v j) :
    ({i, j} : Finset (Fin n)) ∈
      SwitchPairFiber.crossingPairs (fourVertexProposal i u v j h) := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
  · have hs : (fourVertexProposal i u v j h).1.val = {i, u, v, j} := by
      rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
      rfl
    rw [hs]
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
    tauto
  · simp [h.2.2.1]
  · intro x y hxy
    simp only [removedMatching_fourVertexProposal, addedMatching_fourVertexProposal] at hxy
    rcases hxy with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      simp [h.1.symm, h.2.1.symm, h.2.2.1,
        h.2.2.2.2.1, h.2.2.2.2.2]

theorem exists_crossingProposal_of_key_leftSet_exchange {n : ℕ} {d : Fin n → ℕ}
    (G H : GraphState n d) (i j u v : Fin n) (hij : i ≠ j)
    (hu : u ∈ leftSet G.val i j) (hv : v ∈ singletonSet G.val i j)
    (hvn : v ∉ leftSet G.val i j)
    (hkey : key i j H.val = key i j G.val)
    (hleft : leftSet H.val i j = insert v ((leftSet G.val i j).erase u)) :
    ∃ p : SwitchProposal n, validSwitch G.val p ∧
      ({i, j} : Finset (Fin n)) ∈ SwitchPairFiber.crossingPairs p ∧
      proposalResult G.val p = H.val := by
  classical
  obtain ⟨huo, hiu, hju⟩ := (mem_leftSet G.val i j u).mp hu
  obtain ⟨hvo, hvxor⟩ := (mem_singletonSet G.val i j v).mp hv
  have hvright : G.val.Adj j v ∧ ¬ G.val.Adj i v := by
    rcases hvxor with hvleft | hvright
    · exact False.elim (hvn ((mem_leftSet G.val i j v).mpr ⟨hvo, hvleft⟩))
    · exact hvright
  have huv : u ≠ v := fun heq => hvn (heq ▸ hu)
  have hdist : FourDistinct i u v j :=
    ⟨huo.1.symm, hvo.1.symm, hij, huv, huo.2, hvo.2⟩
  have huj : ¬ G.val.Adj u j := fun he => hju he.symm
  refine ⟨fourVertexProposal i u v j hdist,
    (validSwitch_fourVertexProposal_iff G.val i u v j hdist).mpr
      ⟨hiu, hvright.1.symm, hvright.2, huj⟩,
    fourVertexProposal_mem_crossingPairs i u v j hdist, ?_⟩
  change (fourVertexState G i u v j hdist).val = H.val
  apply graph_eq_of_key_leftSet_eq
  · exact (fourVertexState_key G i u v j hdist hiu hvright.1.symm hvright.2 huj).trans hkey.symm
  · exact (fourVertexState_leftSet G i u v j hdist hiu hvright.1.symm hvright.2 huj).trans hleft.symm

end Problem315.PairFiber

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairTradeSwitch.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairSwapInjectivity.lean -/
section

namespace OAI

noncomputable section
namespace Problem315.PairFiber

variable {V : Type*} [DecidableEq V]

theorem exchange_endpoints_unique (T : Finset V) {u v u' v' : V}
    (hu : u ∈ T) (hv : v ∉ T) (_hu' : u' ∈ T) (_hv' : v' ∉ T)
    (h : insert v (T.erase u) = insert v' (T.erase u')) :
    u = u' ∧ v = v' := by
  have hvv : v = v' := by
    have hmem : v ∈ insert v' (T.erase u') := h ▸ Finset.mem_insert_self v _
    rcases Finset.mem_insert.mp hmem with heq | hmem
    · exact heq
    · exact False.elim (hv (Finset.mem_of_mem_erase hmem))
  have huu : u = u' := by
    by_contra hne
    have huv : u ≠ v := fun heq => hv (heq ▸ hu)
    have hnot : u ∉ insert v (T.erase u) := by simp [huv]
    apply hnot
    rw [h]
    exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, hu⟩)
  exact ⟨huu, hvv⟩

theorem swap_eq_of_map_eq (T : Finset V) {u v u' v' : V}
    (hu : u ∈ T) (hv : v ∉ T) (hu' : u' ∈ T) (hv' : v' ∉ T)
    (h : T.map (Equiv.swap u v).toEmbedding =
      T.map (Equiv.swap u' v').toEmbedding) :
    Equiv.swap u v = Equiv.swap u' v' := by
  rw [map_swap_eq_exchange T u v hu hv, map_swap_eq_exchange T u' v' hu' hv'] at h
  obtain ⟨rfl, rfl⟩ := exchange_endpoints_unique T hu hv hu' hv' h
  rfl

theorem exists_oriented_swap_of_map_ne (T : Finset V) {σ : Equiv.Perm V}
    (hσ : σ.IsSwap) (hne : T.map σ.toEmbedding ≠ T) :
    ∃ u v, u ∈ T ∧ v ∉ T ∧ σ = Equiv.swap u v := by
  obtain ⟨u, v, _, rfl⟩ := hσ
  by_cases hu : u ∈ T
  · by_cases hv : v ∈ T
    · exact False.elim (hne (map_swap_eq_self_of_mem_iff T u v (by simp [hu, hv])))
    · exact ⟨u, v, hu, hv, rfl⟩
  · by_cases hv : v ∈ T
    · exact ⟨v, u, hv, hu, Equiv.swap_comm u v⟩
    · exact False.elim (hne (map_swap_eq_self_of_mem_iff T u v (by simp [hu, hv])))

theorem map_swap_injective_on_nontrivial (T : Finset V) {σ τ : Equiv.Perm V}
    (hσ : σ.IsSwap) (hτ : τ.IsSwap)
    (hneσ : T.map σ.toEmbedding ≠ T) (hneτ : T.map τ.toEmbedding ≠ T)
    (h : T.map σ.toEmbedding = T.map τ.toEmbedding) : σ = τ := by
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_oriented_swap_of_map_ne T hσ hneσ
  obtain ⟨u', v', hu', hv', rfl⟩ := exists_oriented_swap_of_map_ne T hτ hneτ
  exact swap_eq_of_map_eq T hu hv hu' hv' h

theorem map_swap_injOn (T : Finset V) :
    Set.InjOn (fun σ : Equiv.Perm V => T.map σ.toEmbedding)
      {σ | σ.IsSwap ∧ T.map σ.toEmbedding ≠ T} := by
  intro σ hσ τ hτ h
  exact map_swap_injective_on_nontrivial T hσ.1 hτ.1 hσ.2 hτ.2 h

end Problem315.PairFiber

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairSwapInjectivity.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairAssignmentMoves.lean -/
section

namespace OAI

noncomputable section
namespace Problem315.PairFiber
open SlicePermutationAction

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem assignmentRelabel_injective_on_nontrivial (G : SimpleGraph V) (i j : V)
    (T : Assignment G i j) {σ τ : Equiv.Perm (singletonSet G i j)}
    (hσ : σ.IsSwap) (hτ : τ.IsSwap)
    (hneσ : assignmentRelabel G i j σ T ≠ T)
    (hneτ : assignmentRelabel G i j τ T ≠ T)
    (h : assignmentRelabel G i j σ T = assignmentRelabel G i j τ T) : σ = τ := by
  let e := assignmentSliceEquiv G i j
  apply map_swap_injective_on_nontrivial (e T).val hσ hτ
  · intro hh
    apply hneσ
    apply e.injective
    change e (e.symm (relabel σ (e T))) = e T
    rw [e.apply_symm_apply]
    exact Subtype.ext hh
  · intro hh
    apply hneτ
    apply e.injective
    change e (e.symm (relabel τ (e T))) = e T
    rw [e.apply_symm_apply]
    exact Subtype.ext hh
  · have hh := congrArg (fun U => (e U).val) h
    simpa only [assignmentRelabel, Equiv.apply_symm_apply, e, relabel] using hh

theorem exists_crossingProposal_of_key_leftSet_swap {n : ℕ} {d : Fin n → ℕ}
    (G H : GraphState n d) (i j u v : Fin n) (hij : i ≠ j)
    (hu : u ∈ singletonSet G.val i j) (hv : v ∈ singletonSet G.val i j)
    (hkey : key i j H.val = key i j G.val)
    (hleft : leftSet H.val i j =
      (leftSet G.val i j).map (Equiv.swap u v).toEmbedding)
    (hne : H ≠ G) :
    ∃ p : SwitchProposal n, validSwitch G.val p ∧
      ({i, j} : Finset (Fin n)) ∈ SwitchPairFiber.crossingPairs p ∧
      proposalResult G.val p = H.val := by
  classical
  have hnot (hm : u ∈ leftSet G.val i j ↔ v ∈ leftSet G.val i j) : False := by
    apply hne
    apply Subtype.ext
    apply graph_eq_of_key_leftSet_eq hkey
    rw [hleft, map_swap_eq_self_of_mem_iff _ u v hm]
  by_cases hul : u ∈ leftSet G.val i j
  · by_cases hvl : v ∈ leftSet G.val i j
    · exact False.elim (hnot (by simp [hul, hvl]))
    · exact exists_crossingProposal_of_key_leftSet_exchange G H i j u v hij
        hul hv hvl hkey (hleft.trans (map_swap_eq_exchange _ u v hul hvl))
  · by_cases hvl : v ∈ leftSet G.val i j
    · apply exists_crossingProposal_of_key_leftSet_exchange G H i j v u hij
        hvl hu hul hkey
      rw [hleft, Equiv.swap_comm u v]
      exact map_swap_eq_exchange _ v u hvl hul
    · exact False.elim (hnot (by simp [hul, hvl]))

theorem assignmentRelabel_exists_crossingProposal {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (T : Assignment G.val i j) (σ : Equiv.Perm (singletonSet G.val i j))
    (hσ : σ.IsSwap) (hne : assignmentRelabel G.val i j σ T ≠ T) :
    let H := ((stateFiberEquiv G i j hij).symm T).val
    let K := ((stateFiberEquiv G i j hij).symm
      (assignmentRelabel G.val i j σ T)).val
    ∃ p : SwitchProposal n, validSwitch H.val p ∧
      ({i, j} : Finset (Fin n)) ∈ SwitchPairFiber.crossingPairs p ∧
      proposalResult H.val p = K.val := by
  classical
  obtain ⟨x, y, _, rfl⟩ := hσ
  let H := ((stateFiberEquiv G i j hij).symm T).val
  let K := ((stateFiberEquiv G i j hij).symm
    (assignmentRelabel G.val i j (Equiv.swap x y) T)).val
  have hkH : key i j H.val = key i j G.val :=
    ((stateFiberEquiv G i j hij).symm T).property
  have hkK : key i j K.val = key i j G.val :=
    ((stateFiberEquiv G i j hij).symm _).property
  have hlH : leftSet H.val i j = T.val := leftSet_trade G.val i j hij T.val T.property.1
  have hlK : leftSet K.val i j =
      T.val.map (Equiv.swap x.val y.val).toEmbedding := by
    exact (leftSet_trade G.val i j hij
      (assignmentRelabel G.val i j (Equiv.swap x y) T).val
      (assignmentRelabel G.val i j (Equiv.swap x y) T).property.1).trans
        (assignmentRelabel_swap_val G.val i j x y T)
  apply exists_crossingProposal_of_key_leftSet_swap H K i j x.val y.val hij
  · rw [singletonSet_eq_of_key_eq hkH]
    exact x.property
  · rw [singletonSet_eq_of_key_eq hkH]
    exact y.property
  · exact hkK.trans hkH.symm
  · rw [hlK, hlH]
  · intro heq
    apply hne
    apply Subtype.ext
    have hh := congrArg (fun F : GraphState n d => leftSet F.val i j) heq
    rw [hlH] at hh
    exact (leftSet_trade G.val i j hij
      (assignmentRelabel G.val i j (Equiv.swap x y) T).val
      (assignmentRelabel G.val i j (Equiv.swap x y) T).property.1).symm.trans hh

end Problem315.PairFiber

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairAssignmentMoves.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairSwapFlip.lean -/
section

namespace OAI

noncomputable section
namespace Problem315.PairFiber
attribute [local instance] Classical.propDecidable

theorem reverse_fourVertexProposal {n : ℕ} (i u v j : Fin n)
    (h : FourDistinct i u v j) (hr : FourDistinct i v u j) :
    reverseProposal (fourVertexProposal i u v j h) = fourVertexProposal i v u j hr := by
  apply SwitchProposal.ext_matchings
  · ext x y
    simp only [removedMatching_reverse, addedMatching_fourVertexProposal,
      removedMatching_fourVertexProposal]
  · ext x y
    simp only [addedMatching_reverse, removedMatching_fourVertexProposal,
      addedMatching_fourVertexProposal]

theorem valid_fourVertex_iff_left_membership {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i u v j : Fin n) (h : FourDistinct i u v j)
    (hu : u ∈ singletonSet G.val i j) (hv : v ∈ singletonSet G.val i j) :
    validSwitch G.val (fourVertexProposal i u v j h) ↔
      u ∈ leftSet G.val i j ∧ v ∉ leftSet G.val i j := by
  rw [validSwitch_fourVertexProposal_iff]
  obtain ⟨huo, huadj⟩ := (mem_singletonSet G.val i j u).mp hu
  obtain ⟨hvo, hvadj⟩ := (mem_singletonSet G.val i j v).mp hv
  simp only [mem_leftSet, huo, hvo, true_and]
  constructor
  · rintro ⟨hiu, hvj, hiv, huj⟩
    exact ⟨⟨hiu, fun hju => huj hju.symm⟩, fun hh => hiv hh.1⟩
  · rintro ⟨⟨hiu, hju⟩, hvl⟩
    have hr : G.val.Adj j v ∧ ¬ G.val.Adj i v := hvadj.resolve_left hvl
    exact ⟨hiu, hr.1.symm, hr.2, fun huj => hju huj.symm⟩

theorem state_eq_bidirectional_of_key_leftSet_swap {n : ℕ} {d : Fin n → ℕ}
    (G H : GraphState n d) (i u v j : Fin n) (h : FourDistinct i u v j)
    (hu : u ∈ singletonSet G.val i j) (hv : v ∈ singletonSet G.val i j)
    (hkey : key i j H.val = key i j G.val)
    (hleft : leftSet H.val i j = (leftSet G.val i j).map (Equiv.swap u v).toEmbedding) :
    H = if validSwitch G.val (fourVertexProposal i u v j h) then
      proposalState G (fourVertexProposal i u v j h)
    else if validSwitch G.val (reverseProposal (fourVertexProposal i u v j h)) then
      proposalState G (reverseProposal (fourVertexProposal i u v j h)) else G := by
  classical
  let hr : FourDistinct i v u j :=
    ⟨h.2.1, h.1, h.2.2.1, h.2.2.2.1.symm, h.2.2.2.2.2, h.2.2.2.2.1⟩
  rw [reverse_fourVertexProposal i u v j h hr]
  have hp := valid_fourVertex_iff_left_membership G i u v j h hu hv
  have hq := valid_fourVertex_iff_left_membership G i v u j hr hv hu
  have hforward (hvl : u ∈ leftSet G.val i j) (hvr : v ∉ leftSet G.val i j) :
      H = proposalState G (fourVertexProposal i u v j h) := by
    have hh := (validSwitch_fourVertexProposal_iff G.val i u v j h).mp
      (hp.mpr ⟨hvl, hvr⟩)
    apply Subtype.ext
    apply graph_eq_of_key_leftSet_eq
    · exact hkey.trans (fourVertexState_key G i u v j h hh.1 hh.2.1 hh.2.2.1 hh.2.2.2).symm
    · change leftSet H.val i j = leftSet (fourVertexState G i u v j h).val i j
      rw [hleft, map_swap_eq_exchange _ u v hvl hvr,
        fourVertexState_leftSet G i u v j h hh.1 hh.2.1 hh.2.2.1 hh.2.2.2]
  have hreverse (hvl : v ∈ leftSet G.val i j) (hvr : u ∉ leftSet G.val i j) :
      H = proposalState G (fourVertexProposal i v u j hr) := by
    have hh := (validSwitch_fourVertexProposal_iff G.val i v u j hr).mp
      (hq.mpr ⟨hvl, hvr⟩)
    apply Subtype.ext
    apply graph_eq_of_key_leftSet_eq
    · exact hkey.trans (fourVertexState_key G i v u j hr hh.1 hh.2.1 hh.2.2.1 hh.2.2.2).symm
    · change leftSet H.val i j = leftSet (fourVertexState G i v u j hr).val i j
      rw [hleft, Equiv.swap_comm u v, map_swap_eq_exchange _ v u hvl hvr,
        fourVertexState_leftSet G i v u j hr hh.1 hh.2.1 hh.2.2.1 hh.2.2.2]
  have hfixed (hh : u ∈ leftSet G.val i j ↔ v ∈ leftSet G.val i j) : H = G := by
    apply Subtype.ext
    apply graph_eq_of_key_leftSet_eq hkey
    rw [hleft, map_swap_eq_self_of_mem_iff _ u v hh]
  by_cases hul : u ∈ leftSet G.val i j <;> by_cases hvl : v ∈ leftSet G.val i j
  · rw [ite_eq_right (by simp only [hp, hul, hvl, not_true_eq_false, and_false, not_false_eq_true]),
      ite_eq_right (by simp only [hq, hul, hvl, not_true_eq_false, and_false, not_false_eq_true])]
    exact hfixed (by simp [hul, hvl])
  · rw [ite_eq_left (hp.mpr ⟨hul, hvl⟩)]
    exact hforward hul hvl
  · rw [ite_eq_right (by simp only [hp, hul, false_and, not_false_eq_true]),
      ite_eq_left (hq.mpr ⟨hvl, hul⟩)]
    exact hreverse hvl hul
  · rw [ite_eq_right (by simp only [hp, hul, false_and, not_false_eq_true]),
      ite_eq_right (by simp only [hq, hvl, false_and, not_false_eq_true])]
    exact hfixed (by simp [hul, hvl])

theorem assignmentRelabel_swap_eq_bidirectional {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (h : FourDistinct i x.val y.val j)
    (T : Assignment G.val i j) :
    ((stateFiberEquiv G i j hij).symm
      (assignmentRelabel G.val i j (Equiv.swap x y) T)).val =
    let H := ((stateFiberEquiv G i j hij).symm T).val
    let p := fourVertexProposal i x.val y.val j h
    if validSwitch H.val p then proposalState H p
    else if validSwitch H.val (reverseProposal p) then
      proposalState H (reverseProposal p) else H := by
  classical
  let H : GraphState n d := ((stateFiberEquiv G i j hij).symm T).val
  let K : GraphState n d := ((stateFiberEquiv G i j hij).symm
    (assignmentRelabel G.val i j (Equiv.swap x y) T)).val
  have hkH : key i j H.val = key i j G.val :=
    ((stateFiberEquiv G i j hij).symm T).property
  have hkK : key i j K.val = key i j G.val :=
    ((stateFiberEquiv G i j hij).symm _).property
  have hlH : leftSet H.val i j = T.val :=
    leftSet_trade G.val i j hij T.val T.property.1
  have hlK : leftSet K.val i j = T.val.map (Equiv.swap x.val y.val).toEmbedding := by
    exact (leftSet_trade G.val i j hij
      (assignmentRelabel G.val i j (Equiv.swap x y) T).val
      (assignmentRelabel G.val i j (Equiv.swap x y) T).property.1).trans
        (assignmentRelabel_swap_val G.val i j x y T)
  apply state_eq_bidirectional_of_key_leftSet_swap H K i x.val y.val j h
  · rw [singletonSet_eq_of_key_eq hkH]
    exact x.property
  · rw [singletonSet_eq_of_key_eq hkH]
    exact y.property
  · exact hkK.trans hkH.symm
  · rw [hlK, hlH]

theorem fourDistinct_of_singleton_labels {n : ℕ} (G : SimpleGraph (Fin n))
    (i j : Fin n) (hij : i ≠ j) (x y : singletonSet G i j) (hxy : x ≠ y) :
    FourDistinct i x.val y.val j := by
  have hx := ((mem_singletonSet G i j x.val).mp x.property).1
  have hy := ((mem_singletonSet G i j y.val).mp y.property).1
  exact ⟨hx.1.symm, hy.1.symm, hij,
    fun hval => hxy (Subtype.ext hval), hx.2, hy.2⟩

theorem singleton_labels_of_valid_fourVertex {n : ℕ} (G : SimpleGraph (Fin n))
    (i u v j : Fin n) (h : FourDistinct i u v j)
    (hp : validSwitch G (fourVertexProposal i u v j h)) :
    u ∈ singletonSet G i j ∧ v ∈ singletonSet G i j := by
  have hh := (validSwitch_fourVertexProposal_iff G i u v j h).mp hp
  constructor
  · apply (mem_singletonSet G i j u).mpr
    exact ⟨⟨h.1.symm, h.2.2.2.2.1⟩,
      Or.inl ⟨hh.1, fun huj => hh.2.2.2 huj.symm⟩⟩
  · apply (mem_singletonSet G i j v).mpr
    exact ⟨⟨h.2.1.symm, h.2.2.2.2.2⟩, Or.inr ⟨hh.2.1.symm, hh.2.2.1⟩⟩

theorem bidirectional_eq_self_of_not_singleton {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i u v j : Fin n) (h : FourDistinct i u v j)
    (hout : ¬ (u ∈ singletonSet G.val i j ∧ v ∈ singletonSet G.val i j)) :
    (if validSwitch G.val (fourVertexProposal i u v j h) then
      proposalState G (fourVertexProposal i u v j h)
    else if validSwitch G.val (reverseProposal (fourVertexProposal i u v j h)) then
      proposalState G (reverseProposal (fourVertexProposal i u v j h)) else G) = G := by
  have hp : ¬ validSwitch G.val (fourVertexProposal i u v j h) :=
    fun hv => hout (singleton_labels_of_valid_fourVertex G.val i u v j h hv)
  let hr : FourDistinct i v u j :=
    ⟨h.2.1, h.1, h.2.2.1, h.2.2.2.1.symm, h.2.2.2.2.2, h.2.2.2.2.1⟩
  have hq : ¬ validSwitch G.val (reverseProposal (fourVertexProposal i u v j h)) := by
    rw [reverse_fourVertexProposal i u v j h hr]
    intro hv
    exact hout (singleton_labels_of_valid_fourVertex G.val i v u j hr hv).symm
  simp only [ite_eq_right hp, ite_eq_right hq]

theorem fourVertexProposal_exchange_pairs {n : ℕ} (i u v j : Fin n)
    (h : FourDistinct i u v j) (hs : FourDistinct u i j v) :
    fourVertexProposal i u v j h = fourVertexProposal u i j v hs := by
  apply SwitchProposal.ext_matchings
  · ext x y
    simp only [removedMatching_fourVertexProposal]
    tauto
  · ext x y
    simp only [addedMatching_fourVertexProposal]
    tauto

end Problem315.PairFiber

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairSwapFlip.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairSwapFlipProjection.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Problem315.PairFiber
attribute [local instance] Classical.propDecidable

variable {n : ℕ} {d : Fin n → ℕ}

theorem assignmentRelabel_swap_eq_flip
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (h : FourDistinct i x.val y.val j)
    (T : Assignment G.val i j) :
    ((stateFiberEquiv G i j hij).symm
      (assignmentRelabel G.val i j (Equiv.swap x y) T)).val =
    SwitchFlip.flip (fourVertexProposal i x.val y.val j h)
      ((stateFiberEquiv G i j hij).symm T).val :=
  assignmentRelabel_swap_eq_bidirectional G i j hij x y h T

theorem flip_leftSet_eq_map_swap
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (h : FourDistinct i x.val y.val j) :
    leftSet (SwitchFlip.flip (fourVertexProposal i x.val y.val j h) G).val i j =
      (leftSet G.val i j).map (Equiv.swap x.val y.val).toEmbedding := by
  let T : Assignment G.val i j :=
    ⟨leftSet G.val i j, leftSet_subset_singletonSet G.val i j, rfl⟩
  have hG : ((stateFiberEquiv G i j hij).symm T).val = G := by
    apply Subtype.ext
    exact trade_original G.val i j hij
  have he := assignmentRelabel_swap_eq_flip G i j hij x y h T
  rw [hG] at he
  rw [← he]
  exact (leftSet_trade G.val i j hij
    (assignmentRelabel G.val i j (Equiv.swap x y) T).val
    (assignmentRelabel G.val i j (Equiv.swap x y) T).property.1).trans
      (assignmentRelabel_swap_val G.val i j x y T)

theorem projection_at_assignment
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (h : FourDistinct i x.val y.val j)
    (f : PairResampling.StateSpace n d) (T : Assignment G.val i j) :
    SwitchFlip.projection (fourVertexProposal i x.val y.val j h) f
      ((stateFiberEquiv G i j hij).symm T).val =
    (f ((stateFiberEquiv G i j hij).symm T).val -
      f ((stateFiberEquiv G i j hij).symm
        (assignmentRelabel G.val i j (Equiv.swap x y) T)).val) / 2 := by
  rw [SwitchFlip.projection_apply, assignmentRelabel_swap_eq_flip]

theorem sum_projection_sq_fiber_eq_assignment
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (h : FourDistinct i x.val y.val j)
    (f : PairResampling.StateSpace n d) :
    (∑ H ∈ PairResampling.fiberStates {i, j} G,
      (SwitchFlip.projection (fourVertexProposal i x.val y.val j h) f H) ^ 2) =
    (1 / 4 : ℝ) * ∑ T : Assignment G.val i j,
      (f ((stateFiberEquiv G i j hij).symm T).val -
        f ((stateFiberEquiv G i j hij).symm
          (assignmentRelabel G.val i j (Equiv.swap x y) T)).val) ^ 2 := by
  rw [← Finset.sum_coe_sort]
  calc
    _ = ∑ T : Assignment G.val i j,
        (SwitchFlip.projection (fourVertexProposal i x.val y.val j h) f
          ((stateFiberEquiv G i j hij).symm T).val) ^ 2 := by
      exact ((resamplingFiberEquiv G i j hij).symm.sum_comp
        (fun H => (SwitchFlip.projection (fourVertexProposal i x.val y.val j h) f H.val) ^ 2)).symm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      rw [projection_at_assignment]
      ring

theorem projection_eq_zero_of_not_singleton
    (G : GraphState n d) (i u v j : Fin n) (h : FourDistinct i u v j)
    (hout : ¬ (u ∈ singletonSet G.val i j ∧ v ∈ singletonSet G.val i j))
    (f : PairResampling.StateSpace n d) :
    SwitchFlip.projection (fourVertexProposal i u v j h) f G = 0 := by
  rw [SwitchFlip.projection_apply]
  have hf : SwitchFlip.flip (fourVertexProposal i u v j h) G = G :=
    bidirectional_eq_self_of_not_singleton G i u v j h hout
  rw [hf]
  ring

end Problem315.PairFiber

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairSwapFlipProjection.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairEqualityBudget.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

def assignmentNormalizedEquiv (G : GraphState n d) (i j : Fin n) :
    Assignment G.val i j ≃
      SliceNormalized.State (singletonSet G.val i j) (leftSet G.val i j).card :=
  (assignmentSliceEquiv G.val i j).trans (cardSliceEquivPowerset _)

theorem assignmentVector_eq_raw (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (hxy : x ≠ y) :
    assignmentVector G i j x.val y.val =
      SliceNormalized.reindexedRaw (assignmentNormalizedEquiv G i j) x y := by
  have hval : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
  have ha : active i j x.val y.val G := ⟨x.property, y.property⟩
  ext T
  let H := (stateFiberEquiv G i j hij).symm T
  have hc := centered_reconstruction G i j x.val y.val hij hval ha T
  have hr := fluctuation_eq_raw_of_fiber G i j hij x y hxy
    (observable i x.val y.val) (fun _ => rfl) H
  change centered i j x.val y.val H.val = _ at hr
  change (if active i j x.val y.val G then
    SliceMoments.centeredEqual (singletonSet G.val i j) (leftSet G.val i j).card
      x.val y.val T.val else 0) = _
  rw [ite_eq_left ha, ← hc]
  change centered i j x.val y.val H.val = _
  rw [hr]
  change SliceNormalized.raw (leftSet G.val i j).card x y
      (stateFiberNormalizedEquiv G i j hij H) =
    SliceNormalized.raw (leftSet G.val i j).card x y (assignmentNormalizedEquiv G i j T)
  have he : stateFiberNormalizedEquiv G i j hij H = assignmentNormalizedEquiv G i j T := by
    change (assignmentSliceEquiv G.val i j).trans (cardSliceEquivPowerset _)
      (stateFiberEquiv G i j hij ((stateFiberEquiv G i j hij).symm T)) = _
    rw [Equiv.apply_symm_apply]
    rfl
  rw [he]

theorem restriction_projection_energy_eq_raw (G : GraphState n d)
    (i j : Fin n) (hij : i ≠ j) (x y : singletonSet G.val i j)
    (f : StateSpace n d) :
    (if x = y then 0 else
      ‖assignmentRestriction G i j hij (projection i j x.val y.val f)‖ ^ 2) =
    ‖(ℝ ∙ SliceNormalized.reindexedRaw (assignmentNormalizedEquiv G i j) x y).starProjection
      (assignmentRestriction G i j hij f)‖ ^ 2 := by
  by_cases hxy : x = y
  · subst y
    have hz : SliceNormalized.reindexedRaw (assignmentNormalizedEquiv G i j) x x = 0 := by
      ext T
      simp
    simp [hz]
  · rw [ite_eq_right hxy, assignmentRestriction_projection G i j x.val y.val hij
      (fun h => hxy (Subtype.ext h)), assignmentVector_eq_raw G i j hij x y hxy]

theorem assignment_projection_budget (G : GraphState n d) (i j : Fin n)
    (hij : i ≠ j) (f : StateSpace n d) :
    (∑ x : singletonSet G.val i j, ∑ y : singletonSet G.val i j,
      if x = y then 0 else
        ‖assignmentRestriction G i j hij (projection i j x.val y.val f)‖ ^ 2) ≤
      (1 / 4 : ℝ) * ∑ x : singletonSet G.val i j, ∑ y : singletonSet G.val i j,
        ∑ T : Assignment G.val i j,
          (f ((stateFiberEquiv G i j hij).symm T).val -
            f ((stateFiberEquiv G i j hij).symm
              (assignmentRelabel G.val i j (Equiv.swap x y) T)).val) ^ 2 := by
  have hq : (leftSet G.val i j).card ≤ Fintype.card (singletonSet G.val i j) := by
    rw [Fintype.card_coe]
    exact Finset.card_le_card (leftSet_subset_singletonSet G.val i j)
  have h := SliceNormalized.reindexed_projection_energy_le_swap_sum
    (assignmentNormalizedEquiv G i j) hq (assignmentRestriction G i j hij f)
  have hswap (x y : singletonSet G.val i j) (T : Assignment G.val i j) :
      (assignmentNormalizedEquiv G i j).symm
        (SliceEuclideanGenerator.swapState (leftSet G.val i j).card x y
          (assignmentNormalizedEquiv G i j T)) =
        assignmentRelabel G.val i j (Equiv.swap x y) T := by
    exact SliceNormalized.conjugated_swap_cardSlice (assignmentSliceEquiv G.val i j) x y T
  simp_rw [hswap, assignmentRestriction_apply] at h
  simp_rw [restriction_projection_energy_eq_raw G i j hij]
  linarith

theorem assignmentRestriction_projection_eq_zero_of_inactive
    (G : GraphState n d) (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (ha : ¬ active i j k l G) (f : StateSpace n d) :
    assignmentRestriction G i j hij (projection i j k l f) = 0 := by
  rw [assignmentRestriction_projection G i j k l hij hkl]
  have hz : assignmentVector G i j k l = 0 := by
    ext T
    simp [assignmentVector, ha]
  simp [hz]

theorem sum_array_subtype {V : Type*} [DecidableEq V]
    (s : Finset V) (F : V → V → ℝ) :
    (∑ k : s, ∑ l : s, F k.val l.val) = ∑ k ∈ s, ∑ l ∈ s, F k l := by
  calc
    _ = ∑ k : s, ∑ l ∈ s, F k.val l := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_coe_sort s (fun l => F k.val l)
    _ = _ := Finset.sum_coe_sort s (fun k => ∑ l ∈ s, F k l)

theorem sum_array_eq_subtype {V : Type*} [Fintype V] [DecidableEq V]
    (s : Finset V) (F : V → V → ℝ)
    (hs : ∀ k l, ¬ (k ∈ s ∧ l ∈ s) → F k l = 0) :
    (∑ k, ∑ l, F k l) = ∑ k : s, ∑ l : s, F k.val l.val := by
  calc
    _ = ∑ k ∈ s, ∑ l, F k l := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro k _ hk
      apply Finset.sum_eq_zero
      intro l _
      exact hs k l (fun h => hk h.1)
    _ = ∑ k ∈ s, ∑ l ∈ s, F k l := by
      apply Finset.sum_congr rfl
      intro k hk
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro l _ hl
      exact hs k l (fun h => hl h.2)
    _ = _ := (sum_array_subtype s F).symm

theorem assignment_projection_sum_eq_singletons (G : GraphState n d)
    (i j : Fin n) (hij : i ≠ j) (f : StateSpace n d) :
    (∑ k, ∑ l, if k = l then 0 else
      ‖assignmentRestriction G i j hij (projection i j k l f)‖ ^ 2) =
    ∑ x : singletonSet G.val i j, ∑ y : singletonSet G.val i j,
      if x = y then 0 else
        ‖assignmentRestriction G i j hij (projection i j x.val y.val f)‖ ^ 2 := by
  have h := sum_array_eq_subtype (singletonSet G.val i j)
    (fun k l => if k = l then 0 else
      ‖assignmentRestriction G i j hij (projection i j k l f)‖ ^ 2) ?_
  · simpa only [Subtype.ext_iff] using h
  · intro k l ha
    by_cases hkl : k = l
    · simp [hkl]
    · rw [ite_eq_right hkl, assignmentRestriction_projection_eq_zero_of_inactive
        G i j k l hij hkl ha f]
      simp

theorem sum_assignmentRestriction_norm_sq (i j : Fin n) (hij : i ≠ j)
    (f : StateSpace n d) :
    (∑ G : GraphState n d, ‖assignmentRestriction G i j hij f‖ ^ 2 /
      (Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card : ℝ)) =
      ‖f‖ ^ 2 := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  simp only [assignmentRestriction_apply]
  have hav (G : GraphState n d) := assignment_average_eq_fiber_average G i j hij
    (fun H => (f H)^2)
  simp_rw [hav]
  exact sum_fiber_average {i,j} (fun H => (f H)^2)

theorem sum_assignmentRestriction_family_norm_sq
    {A : Type*} [Fintype A] (i j : Fin n) (hij : i ≠ j)
    (F : A → StateSpace n d) :
    (∑ G : GraphState n d, (∑ a, ‖assignmentRestriction G i j hij (F a)‖ ^ 2) /
      (Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card : ℝ)) =
      ∑ a, ‖F a‖ ^ 2 := by
  simp_rw [Finset.sum_div]
  rw [Finset.sum_comm]
  simp_rw [sum_assignmentRestriction_norm_sq i j hij]

theorem sum_norm_sq_le_of_assignment_restriction_budget
    {A B : Type*} [Fintype A] [Fintype B]
    (i j : Fin n) (hij : i ≠ j) (F : A → StateSpace n d) (H : B → StateSpace n d)
    (hl : ∀ G : GraphState n d,
      (∑ a, ‖assignmentRestriction G i j hij (F a)‖ ^ 2) ≤
        ∑ b, ‖assignmentRestriction G i j hij (H b)‖ ^ 2) :
    (∑ a, ‖F a‖ ^ 2) ≤ ∑ b, ‖H b‖ ^ 2 := by
  rw [← sum_assignmentRestriction_family_norm_sq i j hij F,
    ← sum_assignmentRestriction_family_norm_sq i j hij H]
  apply Finset.sum_le_sum
  intro G _
  exact div_le_div_of_nonneg_right (hl G) (Nat.cast_nonneg _)

def orderedGain (i j k l : Fin n) : StateSpace n d →L[ℝ] StateSpace n d :=
  if h : FourDistinct i k l j then
    SwitchFlip.projection (fourVertexProposal i k l j h) else 0

@[simp] theorem orderedGain_of_distinct (i j k l : Fin n)
    (h : FourDistinct i k l j) :
    orderedGain (d := d) i j k l =
      SwitchFlip.projection (fourVertexProposal i k l j h) := by
  simp only [orderedGain, dite_eq_left h]

theorem assignment_orderedGain_norm_sq (G : GraphState n d)
    (i j : Fin n) (hij : i ≠ j) (x y : singletonSet G.val i j)
    (f : StateSpace n d) :
    ‖assignmentRestriction G i j hij (orderedGain i j x.val y.val f)‖ ^ 2 =
      (1 / 4 : ℝ) * ∑ T : Assignment G.val i j,
        (f ((stateFiberEquiv G i j hij).symm T).val -
          f ((stateFiberEquiv G i j hij).symm
            (assignmentRelabel G.val i j (Equiv.swap x y) T)).val) ^ 2 := by
  by_cases hxy : x = y
  · subst y
    have hd : ¬ FourDistinct i x.val x.val j := fun h => h.2.2.2.1 rfl
    simp [orderedGain, hd, assignmentRelabel, SlicePermutationAction.relabel]
  · have hd := fourDistinct_of_singleton_labels G.val i j hij x y hxy
    rw [orderedGain_of_distinct i j x.val y.val hd, EuclideanSpace.real_norm_sq_eq,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T _
    rw [assignmentRestriction_apply, projection_at_assignment G i j hij x y hd]
    ring

theorem sum_array_subtype_le {V : Type*} [Fintype V] [DecidableEq V]
    (s : Finset V) (F : V → V → ℝ) (hF : ∀ k l, 0 ≤ F k l) :
    (∑ k : s, ∑ l : s, F k.val l.val) ≤ ∑ k, ∑ l, F k l := by
  rw [sum_array_subtype]
  calc
    _ ≤ ∑ k ∈ s, ∑ l, F k l := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      intro l _ _
      exact hF k l
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      intro k _ _
      exact Finset.sum_nonneg (fun l _ => hF k l)

theorem assignment_ordered_projection_budget (G : GraphState n d)
    (i j : Fin n) (hij : i ≠ j) (f : StateSpace n d) :
    (∑ k, ∑ l, if k = l then 0 else
      ‖assignmentRestriction G i j hij (projection i j k l f)‖ ^ 2) ≤
      ∑ k, ∑ l, ‖assignmentRestriction G i j hij (orderedGain i j k l f)‖ ^ 2 := by
  rw [assignment_projection_sum_eq_singletons G i j hij f]
  calc
    _ ≤ (1 / 4 : ℝ) * ∑ x : singletonSet G.val i j, ∑ y : singletonSet G.val i j,
        ∑ T : Assignment G.val i j,
          (f ((stateFiberEquiv G i j hij).symm T).val -
            f ((stateFiberEquiv G i j hij).symm
              (assignmentRelabel G.val i j (Equiv.swap x y) T)).val) ^ 2 :=
      assignment_projection_budget G i j hij f
    _ = ∑ x : singletonSet G.val i j, ∑ y : singletonSet G.val i j,
        ‖assignmentRestriction G i j hij (orderedGain i j x.val y.val f)‖ ^ 2 := by
      simp_rw [assignment_orderedGain_norm_sq G i j hij]
      simp only [Finset.mul_sum]
    _ ≤ _ := sum_array_subtype_le (singletonSet G.val i j)
      (fun k l => ‖assignmentRestriction G i j hij (orderedGain i j k l f)‖ ^ 2)
      (fun k l => sq_nonneg _)

theorem ordered_projection_budget (i j : Fin n) (hij : i ≠ j) (f : StateSpace n d) :
    (∑ k, ∑ l, if k = l then 0 else ‖projection i j k l f‖ ^ 2) ≤
      ∑ k, ∑ l, ‖orderedGain i j k l f‖ ^ 2 := by
  let F : Fin n × Fin n → StateSpace n d :=
    fun p => if p.1 = p.2 then 0 else projection i j p.1 p.2 f
  let H : Fin n × Fin n → StateSpace n d := fun p => orderedGain i j p.1 p.2 f
  have hF (G : GraphState n d) (k l : Fin n) :
      ‖assignmentRestriction G i j hij (F (k,l))‖ ^ 2 =
        if k = l then 0 else
          ‖assignmentRestriction G i j hij (projection i j k l f)‖ ^ 2 := by
    by_cases hkl : k = l <;> simp [F, hkl]
  have h := sum_norm_sq_le_of_assignment_restriction_budget i j hij F H (fun G => by
    simp only [Fintype.sum_prod_type]
    simp_rw [hF]
    exact assignment_ordered_projection_budget G i j hij f)
  have hFg (k l : Fin n) : ‖F (k,l)‖ ^ 2 =
      if k = l then 0 else ‖projection i j k l f‖ ^ 2 := by
    by_cases hkl : k = l <;> simp [F, hkl]
  simpa only [Fintype.sum_prod_type, hFg, H] using h

end Problem315.PairEquality

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairEqualityBudget.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/UnorderedPairSums.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.UnorderedPairSums

variable {V : Type*} [DecidableEq V]

theorem ordered_fiber (s : Finset V) (i j : V)
    (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    s.offDiag.filter (fun p => ({p.1,p.2} : Finset V) = {i,j}) =
      {(i,j),(j,i)} := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hp,he⟩
    have hs : ({p.1,p.2} : Set V) = {i,j} := by
      simpa only [Finset.coe_pair] using congrArg (fun t : Finset V => (t : Set V)) he
    rcases Set.pair_eq_pair_iff.mp hs with hp | hp
    · exact Or.inl (Prod.ext hp.1 hp.2)
    · exact Or.inr (Prod.ext hp.1 hp.2)
  · rintro (rfl | rfl) <;> simp [hi,hj,hij,hij.symm, Finset.pair_comm]

theorem sum_offDiag_eq_two_mul (s : Finset V) (f : Finset V → ℝ) :
    (∑ p ∈ s.offDiag, f {p.1,p.2}) = 2 * ∑ a ∈ s.powersetCard 2, f a := by
  have hmap (p : V × V) (hp : p ∈ s.offDiag) :
      ({p.1,p.2} : Finset V) ∈ s.powersetCard 2 := by
    obtain ⟨hi,hj,hij⟩ := Finset.mem_offDiag.mp hp
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hi
      · exact hj
    · simp [hij]
  rw [← Finset.sum_fiberwise_of_maps_to' hmap f, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  obtain ⟨has, hac⟩ := Finset.mem_powersetCard.mp ha
  obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hac
  have hi := has (Finset.mem_insert_self i {j})
  have hj := has (Finset.mem_insert_of_mem (Finset.mem_singleton_self j))
  rw [ordered_fiber s i j hi hj hij]
  have hp : (i,j) ≠ (j,i) := fun h => hij (congrArg Prod.fst h)
  simp [hp, two_mul]

theorem sum_ordered_eq_two_mul [Fintype V] (f : Finset V → ℝ) :
    (∑ i : V, ∑ j : V, if i ≠ j then f {i,j} else 0) =
      2 * ∑ a ∈ (Finset.univ : Finset V).powersetCard 2, f a := by
  have he : (Finset.univ : Finset V).offDiag =
      (Finset.univ ×ˢ Finset.univ).filter (fun p : V × V => p.1 ≠ p.2) := by
    ext p
    simp [Finset.mem_offDiag]
  have h := sum_offDiag_eq_two_mul (Finset.univ : Finset V) f
  rw [he, Finset.sum_filter, Finset.sum_product] at h
  exact h

end Problem315.UnorderedPairSums

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/UnorderedPairSums.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairEqualityUnorderedSum.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem projection_diag_right (i j k : Fin n) :
    projection (d := d) i j k k = 0 := by
  have hz : centered (d := d) i j k k = 0 := by
    unfold centered
    apply (fluctuation_eq_zero_iff _ _).mpr
    intro G H h
    change (if G.val.Adj i k ↔ G.val.Adj i k then (1 : ℝ) else 0) =
      if H.val.Adj i k ↔ H.val.Adj i k then 1 else 0
    simp
  have he : equalitySpace (d := d) i j k k = ⊥ := by
    apply le_antisymm
    · intro f hf
      change f = 0
      ext G
      change f G = 0
      obtain ⟨c,hc⟩ := hf G
      have h := hc G (SameFiber.refl _ _)
      simpa only [hz, PiLp.zero_apply, ite_self, mul_zero] using h
    · exact bot_le
  exact (congrArg (fun M : Submodule ℝ (StateSpace n d) => M.starProjection) he).trans
    Submodule.starProjection_bot

theorem sum_pairProjection_eq_half_ordered (i j : Fin n) (hij : i ≠ j)
    (f : StateSpace n d) :
    (∑ b ∈ pairs n, ‖pairProjection {i,j} b f‖ ^ 2) =
      (1 / 2 : ℝ) * ∑ k : Fin n, ∑ l : Fin n,
        if k ≠ l then ‖projection i j k l f‖ ^ 2 else 0 := by
  have h := UnorderedPairSums.sum_ordered_eq_two_mul
    (fun b : Finset (Fin n) => ‖pairProjection {i,j} b f‖ ^ 2)
  have he (k l : Fin n) :
      (if k ≠ l then ‖pairProjection {i,j} {k,l} f‖ ^ 2 else 0) =
        if k ≠ l then ‖projection i j k l f‖ ^ 2 else 0 := by
    by_cases hkl : k ≠ l
    · rw [ite_eq_left hkl, ite_eq_left hkl, pairProjection_pair i j k l hij hkl]
    · rw [ite_eq_right hkl, ite_eq_right hkl]
  simp_rw [he] at h
  change (∑ b ∈ (Finset.univ : Finset (Fin n)).powersetCard 2,
    ‖pairProjection {i,j} b f‖ ^ 2) = _
  linarith

theorem sum_disjoint_pairProjection_eq_half_ordered (i j : Fin n) (hij : i ≠ j)
    (f : StateSpace n d) :
    (∑ b ∈ pairs n,
      if Disjoint ({i,j} : Finset (Fin n)) b then
        ‖pairProjection {i,j} b f‖ ^ 2 else 0) =
      (1 / 2 : ℝ) * ∑ k : Fin n, ∑ l : Fin n,
        if k ≠ l then ‖projection i j k l f‖ ^ 2 else 0 := by
  rw [sum_pairProjection_norm_sq, sum_pairProjection_eq_half_ordered i j hij f]

theorem sum_pairProjection_eq_half_full (i j : Fin n) (hij : i ≠ j)
    (f : StateSpace n d) :
    (∑ b ∈ pairs n, ‖pairProjection {i,j} b f‖ ^ 2) =
      (1 / 2 : ℝ) * ∑ k : Fin n, ∑ l : Fin n, ‖projection i j k l f‖ ^ 2 := by
  rw [sum_pairProjection_eq_half_ordered i j hij f]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hkl : k ≠ l
  · rw [ite_eq_left hkl]
  · have he : k = l := not_ne_iff.mp hkl
    subst l
    simp [projection_diag_right]

end Problem315.PairEquality

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairEqualityUnorderedSum.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairEqualityBudgetUnordered.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem orderedGain_eq_gain (i j k l : Fin n) :
    orderedGain (d := d) i j k l = CrossToggle.gain {i,j} {k,l} :=
  (CrossToggle.gain_pair_eq_ordered i j k l).symm

theorem gain_diag_right (a : Finset (Fin n)) (k : Fin n) :
    CrossToggle.gain (d := d) a {k,k} = 0 := by
  simp [CrossToggle.gain]

theorem sum_gain_eq_half_ordered (i j : Fin n) (f : StateSpace n d) :
    (∑ b ∈ pairs n, ‖CrossToggle.gain {i,j} b f‖ ^ 2) =
      (1 / 2 : ℝ) * ∑ k : Fin n, ∑ l : Fin n, ‖orderedGain i j k l f‖ ^ 2 := by
  have h := UnorderedPairSums.sum_ordered_eq_two_mul
    (fun b : Finset (Fin n) => ‖CrossToggle.gain {i,j} b f‖ ^ 2)
  have he (k l : Fin n) :
      (if k ≠ l then ‖CrossToggle.gain {i,j} {k,l} f‖ ^ 2 else 0) =
        ‖orderedGain i j k l f‖ ^ 2 := by
    rw [orderedGain_eq_gain]
    by_cases hkl : k ≠ l
    · rw [ite_eq_left hkl]
    · have hkl' : k = l := not_ne_iff.mp hkl
      subst l
      simp [CrossToggle.gain]
  simp_rw [he] at h
  change (∑ b ∈ (Finset.univ : Finset (Fin n)).powersetCard 2,
    ‖CrossToggle.gain {i,j} b f‖ ^ 2) = _
  linarith

theorem pair_projection_budget (a : Finset (Fin n)) (f : StateSpace n d) :
    (∑ b ∈ pairs n, ‖pairProjection a b f‖ ^ 2) ≤
      ∑ b ∈ pairs n, ‖CrossToggle.gain a b f‖ ^ 2 := by
  by_cases ha : a.card = 2
  · obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp ha
    rw [sum_pairProjection_eq_half_ordered i j hij f, sum_gain_eq_half_ordered i j f]
    have h := ordered_projection_budget i j hij f
    have he (k l : Fin n) :
        (if k ≠ l then ‖projection i j k l f‖ ^ 2 else 0) =
        if k = l then 0 else ‖projection i j k l f‖ ^ 2 := by
      by_cases hkl : k = l <;> simp [hkl]
    simp_rw [he]
    exact mul_le_mul_of_nonneg_left h (by norm_num)
  · have hz (b : Finset (Fin n)) : pairProjection (d := d) a b = 0 :=
      pairProjection_eq_zero_left a b ha
    simp only [hz, zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero]
    exact Finset.sum_nonneg (fun b _ => sq_nonneg _)

theorem sum_gain_norm_sq (a : Finset (Fin n)) (s : Finset (Finset (Fin n)))
    (f : StateSpace n d) :
    (∑ b ∈ s, if Disjoint a b then ‖CrossToggle.gain a b f‖ ^ 2 else 0) =
      ∑ b ∈ s, ‖CrossToggle.gain a b f‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : Disjoint a b
  · rw [ite_eq_left hab]
  · rw [ite_eq_right hab, CrossToggle.gain_eq_zero_of_not_disjoint a b hab]
    simp

theorem disjoint_pair_projection_budget (a : Finset (Fin n)) (f : StateSpace n d) :
    (∑ b ∈ pairs n, if Disjoint a b then ‖pairProjection a b f‖ ^ 2 else 0) ≤
      ∑ b ∈ pairs n, if Disjoint a b then ‖CrossToggle.gain a b f‖ ^ 2 else 0 := by
  rw [sum_pairProjection_norm_sq, sum_gain_norm_sq]
  exact pair_projection_budget a f

end Problem315.PairEquality

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairEqualityBudgetUnordered.lean -/
