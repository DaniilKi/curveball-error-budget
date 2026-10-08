import AnalyticCrossToggle

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/DisjointEncoding.lean -/
section

namespace OAI

noncomputable section
open scoped Classical

namespace Problem315.DisjointEncoding

variable {V : Type*}

def edgeBit (G : SimpleGraph V) (u v : V) : Nat := if G.Adj u v then 1 else 0

@[simp] theorem edgeBit_eq_iff (G H : SimpleGraph V) (u v : V) :
    edgeBit G u v = edgeBit H u v ↔ (G.Adj u v ↔ H.Adj u v) := by
  by_cases hG : G.Adj u v <;> by_cases hH : H.Adj u v <;> simp [edgeBit, hG, hH]

def Outside (e : Fin 4 ↪ V) (w : V) : Prop := ∀ a, w ≠ e a

structure SameCell (e : Fin 4 ↪ V) (G H : SimpleGraph V) : Prop where
  outer : ∀ u v, Outside e u → Outside e v → (G.Adj u v ↔ H.Adj u v)
  leftInternal : G.Adj (e 0) (e 1) ↔ H.Adj (e 0) (e 1)
  rightInternal : G.Adj (e 2) (e 3) ↔ H.Adj (e 2) (e 3)
  leftCount : ∀ w, Outside e w →
    edgeBit G (e 0) w + edgeBit G (e 1) w =
      edgeBit H (e 0) w + edgeBit H (e 1) w
  rightCount : ∀ w, Outside e w →
    edgeBit G (e 2) w + edgeBit G (e 3) w =
      edgeBit H (e 2) w + edgeBit H (e 3) w

structure SameCoordinates (e : Fin 4 ↪ V) (G H : SimpleGraph V) : Prop where
  cross02 : G.Adj (e 0) (e 2) ↔ H.Adj (e 0) (e 2)
  cross03 : G.Adj (e 0) (e 3) ↔ H.Adj (e 0) (e 3)
  cross12 : G.Adj (e 1) (e 2) ↔ H.Adj (e 1) (e 2)
  cross13 : G.Adj (e 1) (e 3) ↔ H.Adj (e 1) (e 3)
  leftChoice : ∀ w, Outside e w → (G.Adj (e 0) w ↔ H.Adj (e 0) w)
  rightChoice : ∀ w, Outside e w → (G.Adj (e 2) w ↔ H.Adj (e 2) w)

theorem block_to_outside (e : Fin 4 ↪ V) (G H : SimpleGraph V)
    (hc : SameCell e G H) (he : SameCoordinates e G H)
    (a : Fin 4) (w : V) (hw : Outside e w) :
    G.Adj (e a) w ↔ H.Adj (e a) w := by
  fin_cases a
  · exact he.leftChoice w hw
  · change G.Adj (e 1) w ↔ H.Adj (e 1) w
    apply (edgeBit_eq_iff G H _ _).mp
    have hfirst := (edgeBit_eq_iff G H (e 0) w).mpr (he.leftChoice w hw)
    have hsum := hc.leftCount w hw
    omega
  · exact he.rightChoice w hw
  · change G.Adj (e 3) w ↔ H.Adj (e 3) w
    apply (edgeBit_eq_iff G H _ _).mp
    have hfirst := (edgeBit_eq_iff G H (e 2) w).mpr (he.rightChoice w hw)
    have hsum := hc.rightCount w hw
    omega

theorem block_to_block (e : Fin 4 ↪ V) (G H : SimpleGraph V)
    (hc : SameCell e G H) (he : SameCoordinates e G H) (a b : Fin 4) :
    G.Adj (e a) (e b) ↔ H.Adj (e a) (e b) := by
  have h01 := hc.leftInternal
  have h23 := hc.rightInternal
  have h02 := he.cross02
  have h03 := he.cross03
  have h12 := he.cross12
  have h13 := he.cross13
  fin_cases a <;> fin_cases b
  · simp
  · exact h01
  · exact h02
  · exact h03
  · exact (G.adj_comm _ _).trans (h01.trans (H.adj_comm _ _))
  · simp
  · exact h12
  · exact h13
  · exact (G.adj_comm _ _).trans (h02.trans (H.adj_comm _ _))
  · exact (G.adj_comm _ _).trans (h12.trans (H.adj_comm _ _))
  · simp
  · exact h23
  · exact (G.adj_comm _ _).trans (h03.trans (H.adj_comm _ _))
  · exact (G.adj_comm _ _).trans (h13.trans (H.adj_comm _ _))
  · exact (G.adj_comm _ _).trans (h23.trans (H.adj_comm _ _))
  · simp

theorem graph_eq_of_cell_coordinates (e : Fin 4 ↪ V) (G H : SimpleGraph V)
    (hc : SameCell e G H) (he : SameCoordinates e G H) : G = H := by
  ext u v
  by_cases hu : ∃ a, u = e a
  · obtain ⟨a, rfl⟩ := hu
    by_cases hv : ∃ b, v = e b
    · obtain ⟨b, rfl⟩ := hv
      exact block_to_block e G H hc he a b
    · exact block_to_outside e G H hc he a v (by simpa [Outside] using hv)
  · have hu' : Outside e u := by simpa [Outside] using hu
    by_cases hv : ∃ b, v = e b
    · obtain ⟨b, rfl⟩ := hv
      simpa only [SimpleGraph.adj_comm] using block_to_outside e G H hc he b u hu'
    · exact hc.outer u v hu' (by simpa [Outside] using hv)

theorem SameCell.refl (e : Fin 4 ↪ V) (G : SimpleGraph V) : SameCell e G G := by
  constructor <;> intros <;> rfl

theorem SameCell.symm {e : Fin 4 ↪ V} {G H : SimpleGraph V}
    (h : SameCell e G H) : SameCell e H G := by
  exact ⟨fun u v hu hv => (h.outer u v hu hv).symm,
    h.leftInternal.symm, h.rightInternal.symm,
    fun w hw => (h.leftCount w hw).symm, fun w hw => (h.rightCount w hw).symm⟩

theorem SameCell.trans {e : Fin 4 ↪ V} {G H K : SimpleGraph V}
    (h : SameCell e G H) (h' : SameCell e H K) : SameCell e G K := by
  exact ⟨fun u v hu hv => (h.outer u v hu hv).trans (h'.outer u v hu hv),
    h.leftInternal.trans h'.leftInternal, h.rightInternal.trans h'.rightInternal,
    fun w hw => (h.leftCount w hw).trans (h'.leftCount w hw),
    fun w hw => (h.rightCount w hw).trans (h'.rightCount w hw)⟩

def leftIndex (i : Fin 2) : Fin 4 := ⟨i.val, by omega⟩

def rightIndex (i : Fin 2) : Fin 4 := ⟨i.val + 2, by omega⟩

def encode (e : Fin 4 ↪ V) (G : SimpleGraph V) :
    (Fin 2 → Fin 2 → Bool) × Set V × Set V :=
  (fun i j => decide (G.Adj (e (leftIndex i)) (e (rightIndex j))),
    {w | Outside e w ∧ G.Adj (e 0) w}, {w | Outside e w ∧ G.Adj (e 2) w})

theorem sameCoordinates_of_encode_eq (e : Fin 4 ↪ V) (G H : SimpleGraph V)
    (h : encode e G = encode e H) : SameCoordinates e G H := by
  constructor
  · have h' := congrArg (fun z => z.1 0 0) h
    simpa [encode, leftIndex, rightIndex] using h'
  · have h' := congrArg (fun z => z.1 0 1) h
    simpa [encode, leftIndex, rightIndex] using h'
  · have h' := congrArg (fun z => z.1 1 0) h
    simpa [encode, leftIndex, rightIndex] using h'
  · have h' := congrArg (fun z => z.1 1 1) h
    simpa [encode, leftIndex, rightIndex] using h'
  · intro w hw
    have h' := Set.ext_iff.mp (congrArg (fun z => z.2.1) h) w
    simpa [encode, hw] using h'
  · intro w hw
    have h' := Set.ext_iff.mp (congrArg (fun z => z.2.2) h) w
    simpa [encode, hw] using h'

theorem encode_eq_iff (e : Fin 4 ↪ V) (G H : SimpleGraph V)
    (hc : SameCell e G H) : encode e G = encode e H ↔ G = H := by
  constructor
  · intro h
    exact graph_eq_of_cell_coordinates e G H hc (sameCoordinates_of_encode_eq e G H h)
  · intro h
    exact congrArg (encode e) h

theorem encode_cell_injective (e : Fin 4 ↪ V) (G₀ : SimpleGraph V) :
    Function.Injective (fun G : {G : SimpleGraph V // SameCell e G₀ G} => encode e G.val) := by
  intro G H h
  apply Subtype.ext
  exact (encode_eq_iff e G.val H.val (G.property.symm.trans H.property)).mp h

end Problem315.DisjointEncoding

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/DisjointEncoding.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/DisjointReconstruct.lean -/
section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.DisjointEncoding

variable {V : Type*}

def blockEquiv (e : Fin 4 ↪ V) : Fin 4 ⊕ {w : V // Outside e w} ≃ V :=
  Equiv.ofBijective (Sum.elim e Subtype.val) (by
    constructor
    · rintro (a | u) (b | v) h
      · exact congrArg Sum.inl (e.injective h)
      · exact False.elim (v.property a h.symm)
      · exact False.elim (u.property b h)
      · exact congrArg Sum.inr (Subtype.ext h)
    · intro v
      by_cases h : ∃ a, v = e a
      · obtain ⟨a, ha⟩ := h
        exact ⟨Sum.inl a, ha.symm⟩
      · exact ⟨Sum.inr ⟨v, by simpa [Outside] using h⟩, rfl⟩)

@[simp] theorem blockEquiv_inl (e : Fin 4 ↪ V) (a : Fin 4) :
    blockEquiv e (Sum.inl a) = e a := rfl

@[simp] theorem blockEquiv_inr (e : Fin 4 ↪ V) (w : {w : V // Outside e w}) :
    blockEquiv e (Sum.inr w) = w.val := rfl

@[simp] theorem blockEquiv_symm_endpoint (e : Fin 4 ↪ V) (a : Fin 4) :
    (blockEquiv e).symm (e a) = Sum.inl a :=
  (blockEquiv e).symm_apply_apply (Sum.inl a)

@[simp] theorem blockEquiv_symm_outside (e : Fin 4 ↪ V) (w : {w : V // Outside e w}) :
    (blockEquiv e).symm w.val = Sum.inr w :=
  (blockEquiv e).symm_apply_apply (Sum.inr w)

def glueGraph {α β : Type*} (I : SimpleGraph α) (B : α → β → Prop)
    (O : SimpleGraph β) : SimpleGraph (α ⊕ β) where
  Adj u v := match u, v with
    | Sum.inl a, Sum.inl b => I.Adj a b
    | Sum.inl a, Sum.inr w => B a w
    | Sum.inr w, Sum.inl a => B a w
    | Sum.inr u, Sum.inr v => O.Adj u v
  symm := by
    constructor
    rintro (a | u) (b | v) h
    · exact h.symm
    · exact h
    · exact h
    · exact h.symm
  loopless := by
    constructor
    rintro (a | w) h
    · exact I.irrefl h
    · exact O.irrefl h

def reconstruct (e : Fin 4 ↪ V) (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (O : SimpleGraph {w : V // Outside e w}) : SimpleGraph V :=
  (glueGraph I B O).comap (blockEquiv e).symm

@[simp] theorem reconstruct_block_block (e : Fin 4 ↪ V) (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (O : SimpleGraph {w : V // Outside e w}) (a b : Fin 4) :
    (reconstruct e I B O).Adj (e a) (e b) ↔ I.Adj a b := by
  simp [reconstruct, SimpleGraph.comap_adj, glueGraph]

@[simp] theorem reconstruct_block_outside (e : Fin 4 ↪ V) (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (O : SimpleGraph {w : V // Outside e w}) (a : Fin 4) (w : {w : V // Outside e w}) :
    (reconstruct e I B O).Adj (e a) w.val ↔ B a w := by
  simp [reconstruct, SimpleGraph.comap_adj, glueGraph]

@[simp] theorem reconstruct_outside_block (e : Fin 4 ↪ V) (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (O : SimpleGraph {w : V // Outside e w}) (a : Fin 4) (w : {w : V // Outside e w}) :
    (reconstruct e I B O).Adj w.val (e a) ↔ B a w := by
  simp [reconstruct, SimpleGraph.comap_adj, glueGraph]

@[simp] theorem reconstruct_outside_outside (e : Fin 4 ↪ V) (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (O : SimpleGraph {w : V // Outside e w}) (u v : {w : V // Outside e w}) :
    (reconstruct e I B O).Adj u.val v.val ↔ O.Adj u v := by
  simp [reconstruct, SimpleGraph.comap_adj, glueGraph]

theorem reconstruct_graph (e : Fin 4 ↪ V) (G : SimpleGraph V) :
    reconstruct e (G.comap e) (fun a w => G.Adj (e a) w.val)
      (G.comap (fun w : {w : V // Outside e w} => w.val)) = G := by
  ext u v
  obtain ⟨u, rfl⟩ := (blockEquiv e).surjective u
  obtain ⟨v, rfl⟩ := (blockEquiv e).surjective v
  cases u <;> cases v <;> simp [SimpleGraph.adj_comm]

def BoundaryMatches (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (B : Fin 4 → {w : V // Outside e w} → Prop) : Prop :=
  ∀ w, ((if B 0 w then 1 else 0) + (if B 1 w then 1 else 0) =
      edgeBit G (e 0) w.val + edgeBit G (e 1) w.val) ∧
    ((if B 2 w then 1 else 0) + (if B 3 w then 1 else 0) =
      edgeBit G (e 2) w.val + edgeBit G (e 3) w.val)

theorem sameCell_reconstruct (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (hleft : I.Adj 0 1 ↔ G.Adj (e 0) (e 1))
    (hright : I.Adj 2 3 ↔ G.Adj (e 2) (e 3))
    (hB : BoundaryMatches e G B) :
    SameCell e G (reconstruct e I B (G.comap Subtype.val)) := by
  constructor
  · intro u v hu hv
    simpa using (reconstruct_outside_outside e I B (G.comap Subtype.val)
      ⟨u, hu⟩ ⟨v, hv⟩).symm
  · simpa using hleft.symm
  · simpa using hright.symm
  · intro w hw
    simp only [edgeBit]
    rw [reconstruct_block_outside e I B (G.comap Subtype.val) 0 ⟨w, hw⟩,
      reconstruct_block_outside e I B (G.comap Subtype.val) 1 ⟨w, hw⟩]
    exact (hB ⟨w, hw⟩).1.symm
  · intro w hw
    simp only [edgeBit]
    rw [reconstruct_block_outside e I B (G.comap Subtype.val) 2 ⟨w, hw⟩,
      reconstruct_block_outside e I B (G.comap Subtype.val) 3 ⟨w, hw⟩]
    exact (hB ⟨w, hw⟩).2.symm

variable [Fintype V]

theorem degree_eq_sum_bits (G : SimpleGraph V) (v : V) :
    G.degree v = ∑ w, if G.Adj v w then (1 : Nat) else 0 := by
  simpa using G.degree_eq_sum_if_adj (R := Nat) v

theorem degree_reconstruct_block (e : Fin 4 ↪ V) (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (O : SimpleGraph {w : V // Outside e w}) (a : Fin 4) :
    (reconstruct e I B O).degree (e a) =
      I.degree a + (Finset.univ.filter (fun w => B a w)).card := by
  rw [degree_eq_sum_bits (reconstruct e I B O) _,
    ← (blockEquiv e).sum_comp
      (fun v => if (reconstruct e I B O).Adj (e a) v then (1 : Nat) else 0),
    Fintype.sum_sum_type]
  simp only [blockEquiv_inl, blockEquiv_inr, reconstruct_block_block,
    reconstruct_block_outside, degree_eq_sum_bits, Finset.card_filter]

theorem degree_reconstruct_outside (e : Fin 4 ↪ V) (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (O : SimpleGraph {w : V // Outside e w}) (w : {w : V // Outside e w}) :
    (reconstruct e I B O).degree w.val =
      (Finset.univ.filter (fun a => B a w)).card + O.degree w := by
  rw [degree_eq_sum_bits (reconstruct e I B O) _,
    ← (blockEquiv e).sum_comp
      (fun v => if (reconstruct e I B O).Adj w.val v then (1 : Nat) else 0),
    Fintype.sum_sum_type]
  simp only [blockEquiv_inl, blockEquiv_inr, reconstruct_outside_block,
    reconstruct_outside_outside, degree_eq_sum_bits, Finset.card_filter]

theorem degree_outside_preserved (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (hB : BoundaryMatches e G B) (w : {w : V // Outside e w}) :
    (reconstruct e I B (G.comap Subtype.val)).degree w.val = G.degree w.val := by
  have hcolumn : (Finset.univ.filter (fun a => B a w)).card =
      (Finset.univ.filter (fun a : Fin 4 => G.Adj (e a) w.val)).card := by
    simp only [Finset.card_filter, Fin.sum_univ_four]
    have h1 := (hB w).1
    have h2 := (hB w).2
    simp only [edgeBit] at h1 h2
    omega
  have hG := degree_reconstruct_outside e (G.comap e)
    (fun a w => G.Adj (e a) w.val) (G.comap Subtype.val) w
  rw [reconstruct_graph] at hG
  rw [degree_reconstruct_outside, hcolumn]
  exact hG.symm

theorem degree_preserved_of_block (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (hB : BoundaryMatches e G B)
    (hblock : ∀ a, I.degree a + (Finset.univ.filter (fun w => B a w)).card =
      G.degree (e a)) :
    ∀ v, (reconstruct e I B (G.comap Subtype.val)).degree v = G.degree v := by
  intro v
  obtain ⟨v, rfl⟩ := (blockEquiv e).surjective v
  cases v with
  | inl a =>
    change (reconstruct e I B (G.comap Subtype.val)).degree (e a) = G.degree (e a)
    rw [degree_reconstruct_block]
    exact hblock a
  | inr w => exact degree_outside_preserved e G I B hB w

end Problem315.DisjointEncoding

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/DisjointReconstruct.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/BinaryAssignments.lean -/
section

namespace OAI

noncomputable section
open scoped Classical

namespace Problem315.BinaryAssignments

variable {α : Type*} [Fintype α]

def singletons (c : α → Nat) : Finset α := Finset.univ.filter (fun w => c w = 1)
def common (c : α → Nat) : Finset α := Finset.univ.filter (fun w => c w = 2)

def first (c : α → Nat) (U : Finset α) (w : α) : Prop := c w = 2 ∨ w ∈ U
def second (c : α → Nat) (U : Finset α) (w : α) : Prop :=
  c w = 2 ∨ (c w = 1 ∧ w ∉ U)

theorem indicator_sum (c : α → Nat) (hc : ∀ w, c w ≤ 2)
    (U : Finset α) (hU : U ⊆ singletons c) (w : α) :
    (if first c U w then 1 else 0) + (if second c U w then 1 else 0) = c w := by
  have hw := hc w
  have hmem : w ∈ U → c w = 1 := fun h => (Finset.mem_filter.mp (hU h)).2
  by_cases hu : w ∈ U
  · have hc1 := hmem hu
    simp [first, second, hu, hc1]
  · rcases (show c w = 0 ∨ c w = 1 ∨ c w = 2 by omega) with h | h | h <;>
      simp [first, second, hu, h]

theorem first_on_singletons (c : α → Nat) (U : Finset α) (w : α)
    (hw : w ∈ singletons c) : first c U w ↔ w ∈ U := by
  have hc := (Finset.mem_filter.mp hw).2
  simp [first, hc]

theorem first_filter (c : α → Nat) (U : Finset α) :
    Finset.univ.filter (first c U) = common c ∪ U := by
  ext w
  simp [first, common]

theorem second_filter (c : α → Nat) (U : Finset α) :
    Finset.univ.filter (second c U) = common c ∪ (singletons c \ U) := by
  ext w
  simp [second, common, singletons]

theorem first_card (c : α → Nat) (U : Finset α) (hU : U ⊆ singletons c) :
    (Finset.univ.filter (first c U)).card = (common c).card + U.card := by
  rw [first_filter, Finset.card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro w hw hwu
  have h2 := (Finset.mem_filter.mp hw).2
  have h1 := (Finset.mem_filter.mp (hU hwu)).2
  omega

theorem second_card_add (c : α → Nat) (U : Finset α) (hU : U ⊆ singletons c) :
    (Finset.univ.filter (second c U)).card + U.card =
      (common c).card + (singletons c).card := by
  have hdis : Disjoint (common c) (singletons c \ U) := by
    apply Finset.disjoint_left.mpr
    intro w hw hws
    have h2 := (Finset.mem_filter.mp hw).2
    have h1 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hws).1).2
    omega
  rw [second_filter, Finset.card_union_of_disjoint hdis, Nat.add_assoc,
    Finset.card_sdiff_add_card_eq_card hU]

end Problem315.BinaryAssignments

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/BinaryAssignments.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/DisjointBoundary.lean -/
section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.DisjointEncoding

variable {V : Type*} [sectionFintypeV : Fintype V]

def leftCounts (e : Fin 4 ↪ V) (G : SimpleGraph V) (w : {w : V // Outside e w}) : Nat :=
  edgeBit G (e 0) w.val + edgeBit G (e 1) w.val

def rightCounts (e : Fin 4 ↪ V) (G : SimpleGraph V) (w : {w : V // Outside e w}) : Nat :=
  edgeBit G (e 2) w.val + edgeBit G (e 3) w.val

include sectionFintypeV in
theorem edgeBit_le_one (G : SimpleGraph V) (u v : V) : edgeBit G u v ≤ 1 := by
  have retainedsectionFintypeV := sectionFintypeV
  unfold edgeBit
  split_ifs <;> omega

theorem leftCounts_le_two (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (w : {w : V // Outside e w}) : leftCounts e G w ≤ 2 := by
  have h0 := edgeBit_le_one G (e 0) w.val
  have h1 := edgeBit_le_one G (e 1) w.val
  unfold leftCounts
  omega

theorem rightCounts_le_two (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (w : {w : V // Outside e w}) : rightCounts e G w ≤ 2 := by
  have h0 := edgeBit_le_one G (e 2) w.val
  have h1 := edgeBit_le_one G (e 3) w.val
  unfold rightCounts
  omega

def assignmentBoundary (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (U W : Finset {w : V // Outside e w}) :
    Fin 4 → {w : V // Outside e w} → Prop :=
  ![BinaryAssignments.first (leftCounts e G) U,
    BinaryAssignments.second (leftCounts e G) U,
    BinaryAssignments.first (rightCounts e G) W,
    BinaryAssignments.second (rightCounts e G) W]

theorem assignmentBoundary_matches (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (U W : Finset {w : V // Outside e w})
    (hU : U ⊆ BinaryAssignments.singletons (leftCounts e G))
    (hW : W ⊆ BinaryAssignments.singletons (rightCounts e G)) :
    BoundaryMatches e G (assignmentBoundary e G U W) := by
  intro w
  constructor
  · exact BinaryAssignments.indicator_sum (leftCounts e G) (leftCounts_le_two e G) U hU w
  · exact BinaryAssignments.indicator_sum (rightCounts e G) (rightCounts_le_two e G) W hW w

theorem assignmentBoundary_card_zero (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (U W : Finset {w : V // Outside e w})
    (hU : U ⊆ BinaryAssignments.singletons (leftCounts e G)) :
    (Finset.univ.filter (assignmentBoundary e G U W 0)).card =
      (BinaryAssignments.common (leftCounts e G)).card + U.card :=
  BinaryAssignments.first_card _ _ hU

theorem assignmentBoundary_card_one (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (U W : Finset {w : V // Outside e w})
    (hU : U ⊆ BinaryAssignments.singletons (leftCounts e G)) :
    (Finset.univ.filter (assignmentBoundary e G U W 1)).card + U.card =
      (BinaryAssignments.common (leftCounts e G)).card +
        (BinaryAssignments.singletons (leftCounts e G)).card :=
  BinaryAssignments.second_card_add _ _ hU

theorem assignmentBoundary_card_two (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (U W : Finset {w : V // Outside e w})
    (hW : W ⊆ BinaryAssignments.singletons (rightCounts e G)) :
    (Finset.univ.filter (assignmentBoundary e G U W 2)).card =
      (BinaryAssignments.common (rightCounts e G)).card + W.card :=
  BinaryAssignments.first_card _ _ hW

theorem assignmentBoundary_card_three (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (U W : Finset {w : V // Outside e w})
    (hW : W ⊆ BinaryAssignments.singletons (rightCounts e G)) :
    (Finset.univ.filter (assignmentBoundary e G U W 3)).card + W.card =
      (BinaryAssignments.common (rightCounts e G)).card +
        (BinaryAssignments.singletons (rightCounts e G)).card :=
  BinaryAssignments.second_card_add _ _ hW

end Problem315.DisjointEncoding

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/DisjointBoundary.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/CrossMatrix.lean -/
section

namespace OAI

namespace Problem315.CrossBlock

open scoped BigOperators

abbrev Matrix := Fin 2 → Fin 2 → Bool

def entry (M : Matrix) (i j : Fin 2) : Nat := if M i j then 1 else 0

def row (M : Matrix) (i : Fin 2) : Nat := ∑ j, entry M i j

def col (M : Matrix) (j : Fin 2) : Nat := ∑ i, entry M i j

def total (M : Matrix) : Nat := ∑ i, row M i

def count (s r c : Nat) : Nat :=
  (Finset.univ.filter (fun M : Matrix => total M = s ∧ row M 0 = r ∧ col M 0 = c)).card

theorem count_two : ∀ r c : Fin 3,
    count 2 r c = if r = 1 then (if c = 1 then 2 else 1) else (if c = 1 then 1 else 0) := by
  decide

theorem count_one : ∀ r c : Fin 3,
    count 1 r c = if r ≤ 1 ∧ c ≤ 1 then 1 else 0 := by
  decide

theorem count_three : ∀ r c : Fin 3,
    count 3 r c = if 1 ≤ r ∧ 1 ≤ c then 1 else 0 := by
  decide

theorem count_zero : ∀ r c : Fin 3,
    count 0 r c = if r = 0 ∧ c = 0 then 1 else 0 := by
  decide

theorem count_four : ∀ r c : Fin 3,
    count 4 r c = if r = 2 ∧ c = 2 then 1 else 0 := by
  decide

theorem off_center_disjoint : ∀ M : Matrix,
    total M = 2 → row M 0 ≠ 1 → col M 0 = 1 := by
  decide

theorem central_iff : ∀ M : Matrix,
    total M = 2 →
      (row M 0 = 1 ∧ col M 0 = 1 ↔ (∀ i, row M i = 1) ∧ ∀ j, col M j = 1) := by
  decide

def toggle (M : Matrix) : Matrix :=
  if (∀ i, row M i = 1) ∧ (∀ j, col M j = 1) then
    fun i j => !(M i j)
  else M

theorem toggle_involutive : ∀ M : Matrix, toggle (toggle M) = M := by
  decide

theorem toggle_row : ∀ (M : Matrix) (i : Fin 2), row (toggle M) i = row M i := by
  decide

theorem toggle_col : ∀ (M : Matrix) (j : Fin 2), col (toggle M) j = col M j := by
  decide

theorem toggle_total : ∀ M : Matrix, total (toggle M) = total M := by
  decide

theorem toggle_ne_iff : ∀ M : Matrix,
    toggle M ≠ M ↔ (∀ i, row M i = 1) ∧ ∀ j, col M j = 1 := by
  decide

theorem row_le_two : ∀ (M : Matrix) (i : Fin 2), row M i ≤ 2 := by
  decide

theorem col_le_two : ∀ (M : Matrix) (j : Fin 2), col M j ≤ 2 := by
  decide

theorem total_le_four : ∀ M : Matrix, total M ≤ 4 := by
  decide

theorem count_two_real (r c : Fin 3) :
    (count 2 r c : ℝ) =
      2 - (if r = 1 then 0 else 1) - (if c = 1 then 0 else 1) := by
  rw [count_two]
  by_cases hr : r = 1 <;> by_cases hc : c = 1 <;> norm_num [hr, hc]

end Problem315.CrossBlock

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/CrossMatrix.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/DisjointInternal.lean -/
section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.DisjointEncoding

def internalAdj (l r : Bool) (M : CrossBlock.Matrix) : Fin 4 → Fin 4 → Bool :=
  ![![false, l, M 0 0, M 0 1],
    ![l, false, M 1 0, M 1 1],
    ![M 0 0, M 1 0, false, r],
    ![M 0 1, M 1 1, r, false]]

def internalGraph (l r : Bool) (M : CrossBlock.Matrix) : SimpleGraph (Fin 4) where
  Adj a b := internalAdj l r M a b = true
  symm := by
    constructor
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [internalAdj]
  loopless := by
    constructor
    intro a h
    fin_cases a <;> simp_all [internalAdj]

@[simp] theorem internalGraph_left (l r : Bool) (M : CrossBlock.Matrix) :
    (internalGraph l r M).Adj 0 1 ↔ l = true := by simp [internalGraph, internalAdj]

@[simp] theorem internalGraph_right (l r : Bool) (M : CrossBlock.Matrix) :
    (internalGraph l r M).Adj 2 3 ↔ r = true := by simp [internalGraph, internalAdj]

@[simp] theorem internalGraph_cross (l r : Bool) (M : CrossBlock.Matrix) (a b : Fin 2) :
    (internalGraph l r M).Adj (leftIndex a) (rightIndex b) ↔ M a b = true := by
  fin_cases a <;> fin_cases b <;> simp [internalGraph, internalAdj, leftIndex, rightIndex]

theorem internalGraph_degree_left (l r : Bool) (M : CrossBlock.Matrix) (a : Fin 2) :
    (internalGraph l r M).degree (leftIndex a) =
      (if l then 1 else 0) + CrossBlock.row M a := by
  rw [degree_eq_sum_bits, Fin.sum_univ_four]
  simp only [CrossBlock.row, Fin.sum_univ_two, CrossBlock.entry]
  fin_cases a <;>
    simp [internalGraph, internalAdj, leftIndex] <;> ring_nf

theorem internalGraph_degree_right (l r : Bool) (M : CrossBlock.Matrix) (a : Fin 2) :
    (internalGraph l r M).degree (rightIndex a) =
      (if r then 1 else 0) + CrossBlock.col M a := by
  rw [degree_eq_sum_bits, Fin.sum_univ_four]
  simp only [CrossBlock.col, Fin.sum_univ_two, CrossBlock.entry]
  fin_cases a <;>
    simp [internalGraph, internalAdj, rightIndex] <;> ring_nf

end Problem315.DisjointEncoding

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/DisjointInternal.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/DisjointRealization.lean -/
section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.DisjointEncoding

variable {V : Type*} [sectionFintypeV : Fintype V]

def crossCode (e : Fin 4 ↪ V) (G : SimpleGraph V) : CrossBlock.Matrix :=
  fun a b => decide (G.Adj (e (leftIndex a)) (e (rightIndex b)))

def leftAssignment (e : Fin 4 ↪ V) (G H : SimpleGraph V) :
    Finset {w : V // Outside e w} :=
  (BinaryAssignments.singletons (leftCounts e G)).filter (fun w => H.Adj (e 0) w.val)

def rightAssignment (e : Fin 4 ↪ V) (G H : SimpleGraph V) :
    Finset {w : V // Outside e w} :=
  (BinaryAssignments.singletons (rightCounts e G)).filter (fun w => H.Adj (e 2) w.val)

def realizeCoordinates (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (M : CrossBlock.Matrix) (U W : Finset {w : V // Outside e w}) : SimpleGraph V :=
  reconstruct e (internalGraph (decide (G.Adj (e 0) (e 1)))
    (decide (G.Adj (e 2) (e 3))) M) (assignmentBoundary e G U W) (G.comap Subtype.val)

theorem realizeCoordinates_sameCell (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (M : CrossBlock.Matrix) (U W : Finset {w : V // Outside e w})
    (hU : U ⊆ BinaryAssignments.singletons (leftCounts e G))
    (hW : W ⊆ BinaryAssignments.singletons (rightCounts e G)) :
    SameCell e G (realizeCoordinates e G M U W) := by
  apply sameCell_reconstruct
  · simp
  · simp
  · exact assignmentBoundary_matches e G U W hU hW

@[simp] theorem crossCode_realizeCoordinates (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (M : CrossBlock.Matrix) (U W : Finset {w : V // Outside e w}) :
    crossCode e (realizeCoordinates e G M U W) = M := by
  have retainedsectionFintypeV := sectionFintypeV
  funext a b
  simp [crossCode, realizeCoordinates]

theorem leftAssignment_realizeCoordinates (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (M : CrossBlock.Matrix) (U W : Finset {w : V // Outside e w})
    (hU : U ⊆ BinaryAssignments.singletons (leftCounts e G)) :
    leftAssignment e G (realizeCoordinates e G M U W) = U := by
  ext w
  simp only [leftAssignment, Finset.mem_filter, realizeCoordinates,
    reconstruct_block_outside]
  change (w ∈ BinaryAssignments.singletons (leftCounts e G) ∧
    BinaryAssignments.first (leftCounts e G) U w) ↔ w ∈ U
  constructor
  · intro h
    exact (BinaryAssignments.first_on_singletons _ U w h.1).mp h.2
  · intro h
    exact ⟨hU h, (BinaryAssignments.first_on_singletons _ U w (hU h)).mpr h⟩

theorem rightAssignment_realizeCoordinates (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (M : CrossBlock.Matrix) (U W : Finset {w : V // Outside e w})
    (hW : W ⊆ BinaryAssignments.singletons (rightCounts e G)) :
    rightAssignment e G (realizeCoordinates e G M U W) = W := by
  ext w
  simp only [rightAssignment, Finset.mem_filter, realizeCoordinates,
    reconstruct_block_outside]
  change (w ∈ BinaryAssignments.singletons (rightCounts e G) ∧
    BinaryAssignments.first (rightCounts e G) W w) ↔ w ∈ W
  constructor
  · intro h
    exact (BinaryAssignments.first_on_singletons _ W w h.1).mp h.2
  · intro h
    exact ⟨hW h, (BinaryAssignments.first_on_singletons _ W w (hW h)).mpr h⟩

theorem feasible_coordinates_realized (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (M : CrossBlock.Matrix) (U W : Finset {w : V // Outside e w})
    (hU : U ⊆ BinaryAssignments.singletons (leftCounts e G))
    (hW : W ⊆ BinaryAssignments.singletons (rightCounts e G))
    (hdegree : ∀ a,
      (internalGraph (decide (G.Adj (e 0) (e 1))) (decide (G.Adj (e 2) (e 3))) M).degree a +
        (Finset.univ.filter (assignmentBoundary e G U W a)).card = G.degree (e a)) :
    ∃ H : SimpleGraph V, SameCell e G H ∧ (∀ v, H.degree v = G.degree v) ∧
      crossCode e H = M ∧ leftAssignment e G H = U ∧ rightAssignment e G H = W := by
  refine ⟨realizeCoordinates e G M U W, realizeCoordinates_sameCell e G M U W hU hW,
    ?_, crossCode_realizeCoordinates e G M U W,
    leftAssignment_realizeCoordinates e G M U W hU,
    rightAssignment_realizeCoordinates e G M U W hW⟩
  exact degree_preserved_of_block e G _ _ (assignmentBoundary_matches e G U W hU hW) hdegree

theorem first_edge_iff_of_counts (G H K : SimpleGraph V) (i j w : V)
    (hH : edgeBit G i w + edgeBit G j w = edgeBit H i w + edgeBit H j w)
    (hK : edgeBit G i w + edgeBit G j w = edgeBit K i w + edgeBit K j w)
    (hsingle : edgeBit G i w + edgeBit G j w = 1 → (H.Adj i w ↔ K.Adj i w)) :
    H.Adj i w ↔ K.Adj i w := by
  by_cases h : edgeBit G i w + edgeBit G j w = 1
  · exact hsingle h
  · apply (edgeBit_eq_iff H K i w).mp
    have hHi := edgeBit_le_one H i w
    have hHj := edgeBit_le_one H j w
    have hKi := edgeBit_le_one K i w
    have hKj := edgeBit_le_one K j w
    omega

theorem graph_eq_of_cell_assignments (e : Fin 4 ↪ V) (G H K : SimpleGraph V)
    (hH : SameCell e G H) (hK : SameCell e G K)
    (hM : crossCode e H = crossCode e K)
    (hU : leftAssignment e G H = leftAssignment e G K)
    (hW : rightAssignment e G H = rightAssignment e G K) : H = K := by
  apply graph_eq_of_cell_coordinates e H K (hH.symm.trans hK)
  constructor
  · have h := congrFun (congrFun hM 0) 0
    simpa [crossCode, leftIndex, rightIndex] using h
  · have h := congrFun (congrFun hM 0) 1
    simpa [crossCode, leftIndex, rightIndex] using h
  · have h := congrFun (congrFun hM 1) 0
    simpa [crossCode, leftIndex, rightIndex] using h
  · have h := congrFun (congrFun hM 1) 1
    simpa [crossCode, leftIndex, rightIndex] using h
  · intro w hw
    apply first_edge_iff_of_counts G H K (e 0) (e 1) w
      (hH.leftCount w hw) (hK.leftCount w hw)
    intro hs
    have h := Finset.ext_iff.mp hU ⟨w, hw⟩
    have member : ⟨w, hw⟩ ∈ BinaryAssignments.singletons (leftCounts e G) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
    constructor
    · intro adjacent
      exact (Finset.mem_filter.mp (h.mp (Finset.mem_filter.mpr ⟨member, adjacent⟩))).2
    · intro adjacent
      exact (Finset.mem_filter.mp (h.mpr (Finset.mem_filter.mpr ⟨member, adjacent⟩))).2
  · intro w hw
    apply first_edge_iff_of_counts G H K (e 2) (e 3) w
      (hH.rightCount w hw) (hK.rightCount w hw)
    intro hs
    have h := Finset.ext_iff.mp hW ⟨w, hw⟩
    have member : ⟨w, hw⟩ ∈ BinaryAssignments.singletons (rightCounts e G) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
    constructor
    · intro adjacent
      exact (Finset.mem_filter.mp (h.mp (Finset.mem_filter.mpr ⟨member, adjacent⟩))).2
    · intro adjacent
      exact (Finset.mem_filter.mp (h.mpr (Finset.mem_filter.mpr ⟨member, adjacent⟩))).2

theorem realizeCoordinates_encode (e : Fin 4 ↪ V) (G H : SimpleGraph V)
    (hH : SameCell e G H) :
    realizeCoordinates e G (crossCode e H) (leftAssignment e G H)
      (rightAssignment e G H) = H := by
  have hU : leftAssignment e G H ⊆ BinaryAssignments.singletons (leftCounts e G) :=
    Finset.filter_subset _ _
  have hW : rightAssignment e G H ⊆ BinaryAssignments.singletons (rightCounts e G) :=
    Finset.filter_subset _ _
  apply graph_eq_of_cell_assignments e G _ H
    (realizeCoordinates_sameCell e G _ _ _ hU hW) hH
  · exact crossCode_realizeCoordinates e G _ _ _
  · exact leftAssignment_realizeCoordinates e G _ _ _ hU
  · exact rightAssignment_realizeCoordinates e G _ _ _ hW

@[ext] structure FeasibleCoordinates (e : Fin 4 ↪ V) (G : SimpleGraph V) where
  matrix : CrossBlock.Matrix
  left : Finset {w : V // Outside e w}
  right : Finset {w : V // Outside e w}
  left_subset : left ⊆ BinaryAssignments.singletons (leftCounts e G)
  right_subset : right ⊆ BinaryAssignments.singletons (rightCounts e G)
  degrees : ∀ a,
    (internalGraph (decide (G.Adj (e 0) (e 1))) (decide (G.Adj (e 2) (e 3))) matrix).degree a +
      (Finset.univ.filter (assignmentBoundary e G left right a)).card = G.degree (e a)

abbrev DegreeCell (e : Fin 4 ↪ V) (G : SimpleGraph V) :=
  {H : SimpleGraph V // SameCell e G H ∧ ∀ v, H.degree v = G.degree v}

def cellEncode (e : Fin 4 ↪ V) (G : SimpleGraph V) (H : DegreeCell e G) :
    FeasibleCoordinates e G where
  matrix := crossCode e H.val
  left := leftAssignment e G H.val
  right := rightAssignment e G H.val
  left_subset := Finset.filter_subset _ _
  right_subset := Finset.filter_subset _ _
  degrees := by
    intro a
    have h := congrArg (fun K : SimpleGraph V => K.degree (e a))
      (realizeCoordinates_encode e G H.val H.property.1)
    unfold realizeCoordinates at h
    rw [degree_reconstruct_block] at h
    exact h.trans (H.property.2 (e a))

def cellDecode (e : Fin 4 ↪ V) (G : SimpleGraph V) (c : FeasibleCoordinates e G) :
    DegreeCell e G :=
  ⟨realizeCoordinates e G c.matrix c.left c.right,
    realizeCoordinates_sameCell e G _ _ _ c.left_subset c.right_subset,
    degree_preserved_of_block e G _ _
      (assignmentBoundary_matches e G _ _ c.left_subset c.right_subset) c.degrees⟩

def degreeCellEquiv (e : Fin 4 ↪ V) (G : SimpleGraph V) :
    DegreeCell e G ≃ FeasibleCoordinates e G where
  toFun := cellEncode e G
  invFun := cellDecode e G
  left_inv H := by
    apply Subtype.ext
    exact realizeCoordinates_encode e G H.val H.property.1
  right_inv c := by
    apply FeasibleCoordinates.ext
    · exact crossCode_realizeCoordinates e G _ _ _
    · exact leftAssignment_realizeCoordinates e G _ _ _ c.left_subset
    · exact rightAssignment_realizeCoordinates e G _ _ _ c.right_subset

end Problem315.DisjointEncoding

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/DisjointRealization.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/DisjointCoordinateFeasibility.lean -/
section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.CrossBlock

theorem total_eq_row_add (M : Matrix) : total M = row M 0 + row M 1 := by
  simp [total, Fin.sum_univ_two]

theorem total_eq_col_add (M : Matrix) : total M = col M 0 + col M 1 := by
  simp only [total, row, col, Fin.sum_univ_two]
  omega

end Problem315.CrossBlock

namespace Problem315.DisjointEncoding
variable {V : Type*} [Fintype V]

theorem coordinate_degrees_iff
    (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (M : CrossBlock.Matrix) (U W : Finset {w : V // Outside e w})
    (hU : U ⊆ BinaryAssignments.singletons (leftCounts e G))
    (hW : W ⊆ BinaryAssignments.singletons (rightCounts e G)) :
    (∀ a,
      (internalGraph (decide (G.Adj (e 0) (e 1)))
        (decide (G.Adj (e 2) (e 3))) M).degree a +
        (Finset.univ.filter (assignmentBoundary e G U W a)).card = G.degree (e a)) ↔
    CrossBlock.total M = CrossBlock.total (crossCode e G) ∧
      CrossBlock.row M 0 + U.card =
        CrossBlock.row (crossCode e G) 0 + (leftAssignment e G G).card ∧
      CrossBlock.col M 0 + W.card =
        CrossBlock.col (crossCode e G) 0 + (rightAssignment e G G).card := by
  let l := decide (G.Adj (e 0) (e 1))
  let r := decide (G.Adj (e 2) (e 3))
  let M₀ := crossCode e G
  let U₀ := leftAssignment e G G
  let W₀ := rightAssignment e G G
  have hU₀ : U₀ ⊆ BinaryAssignments.singletons (leftCounts e G) := Finset.filter_subset _ _
  have hW₀ : W₀ ⊆ BinaryAssignments.singletons (rightCounts e G) := Finset.filter_subset _ _
  have hbase := (cellEncode e G ⟨G, SameCell.refl e G, fun _ => rfl⟩).degrees
  change ∀ a, (internalGraph l r M₀).degree a +
    (Finset.univ.filter (assignmentBoundary e G U₀ W₀ a)).card = G.degree (e a) at hbase
  have hbase0 := hbase 0
  have hbase1 := hbase 1
  have hbase2 := hbase 2
  have hbase3 := hbase 3
  have hd0 := internalGraph_degree_left l r M 0
  have hd1 := internalGraph_degree_left l r M 1
  have hd2 := internalGraph_degree_right l r M 0
  have hd3 := internalGraph_degree_right l r M 1
  have hd00 := internalGraph_degree_left l r M₀ 0
  have hd01 := internalGraph_degree_left l r M₀ 1
  have hd02 := internalGraph_degree_right l r M₀ 0
  have hd03 := internalGraph_degree_right l r M₀ 1
  change (internalGraph l r M).degree 0 = _ at hd0
  change (internalGraph l r M).degree 1 = _ at hd1
  change (internalGraph l r M).degree 2 = _ at hd2
  change (internalGraph l r M).degree 3 = _ at hd3
  change (internalGraph l r M₀).degree 0 = _ at hd00
  change (internalGraph l r M₀).degree 1 = _ at hd01
  change (internalGraph l r M₀).degree 2 = _ at hd02
  change (internalGraph l r M₀).degree 3 = _ at hd03
  have hb0 := assignmentBoundary_card_zero e G U W hU
  have hb1 := assignmentBoundary_card_one e G U W hU
  have hb2 := assignmentBoundary_card_two e G U W hW
  have hb3 := assignmentBoundary_card_three e G U W hW
  have hb00 := assignmentBoundary_card_zero e G U₀ W₀ hU₀
  have hb01 := assignmentBoundary_card_one e G U₀ W₀ hU₀
  have hb02 := assignmentBoundary_card_two e G U₀ W₀ hW₀
  have hb03 := assignmentBoundary_card_three e G U₀ W₀ hW₀
  have ht := CrossBlock.total_eq_row_add M
  have ht₀ := CrossBlock.total_eq_row_add M₀
  have hc := CrossBlock.total_eq_col_add M
  have hc₀ := CrossBlock.total_eq_col_add M₀
  change (∀ a, (internalGraph l r M).degree a +
    (Finset.univ.filter (assignmentBoundary e G U W a)).card = G.degree (e a)) ↔
    CrossBlock.total M = CrossBlock.total M₀ ∧
      CrossBlock.row M 0 + U.card = CrossBlock.row M₀ 0 + U₀.card ∧
      CrossBlock.col M 0 + W.card = CrossBlock.col M₀ 0 + W₀.card
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    omega
  · rintro ⟨htotal, hleft, hright⟩ a
    have h0 : (internalGraph l r M).degree 0 +
        (Finset.univ.filter (assignmentBoundary e G U W 0)).card = G.degree (e 0) := by omega
    have h1 : (internalGraph l r M).degree 1 +
        (Finset.univ.filter (assignmentBoundary e G U W 1)).card = G.degree (e 1) := by omega
    have h2 : (internalGraph l r M).degree 2 +
        (Finset.univ.filter (assignmentBoundary e G U W 2)).card = G.degree (e 2) := by omega
    have h3 : (internalGraph l r M).degree 3 +
        (Finset.univ.filter (assignmentBoundary e G U W 3)).card = G.degree (e 3) := by omega
    fin_cases a
    · exact h0
    · exact h1
    · exact h2
    · exact h3

end Problem315.DisjointEncoding

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/DisjointCoordinateFeasibility.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/CrossCovariance.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.CrossCovariance

variable {α β : Type*} [sectionFintypeα : Fintype α] [Fintype β]

def jointMoment (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (f : α → ℝ) (g : β → ℝ) : ℝ :=
  ∑ x, ∑ y, a x * b y * (2 - p x - q y) * f x * g y

def mass (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ) : ℝ :=
  jointMoment a b p q (fun _ => 1) (fun _ => 1)

def jointAverage (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (f : α → ℝ) (g : β → ℝ) : ℝ :=
  jointMoment a b p q f g / mass a b p q

theorem jointMoment_eq (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (f : α → ℝ) (g : β → ℝ) :
    jointMoment a b p q f g =
      2 * (∑ x, a x * f x) * (∑ y, b y * g y) -
      (∑ x, a x * p x * f x) * (∑ y, b y * g y) -
      (∑ x, a x * f x) * (∑ y, b y * q y * g y) := by
  unfold jointMoment
  calc
    (∑ x, ∑ y, a x * b y * (2 - p x - q y) * f x * g y) =
        ∑ x, ∑ y, (2 * (a x * f x) * (b y * g y) -
          (a x * p x * f x) * (b y * g y) -
          (a x * f x) * (b y * q y * g y)) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]

theorem mass_eq (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ) :
    mass a b p q = 2 * (∑ x, a x) * (∑ y, b y) -
      (∑ x, a x * p x) * (∑ y, b y) -
      (∑ x, a x) * (∑ y, b y * q y) := by
  simp [mass, jointMoment_eq]

theorem covariance_rank_one
    (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (f : α → ℝ) (g : β → ℝ) :
    jointAverage a b p q f g -
        jointAverage a b p q f (fun _ => 1) *
          jointAverage a b p q (fun _ => 1) g =
      - ((∑ x, a x) * (∑ x, a x * p x * f x) -
          (∑ x, a x * p x) * (∑ x, a x * f x)) *
        ((∑ y, b y) * (∑ y, b y * q y * g y) -
          (∑ y, b y * q y) * (∑ y, b y * g y)) /
        (mass a b p q) ^ 2 := by
  by_cases hZ : mass a b p q = 0
  · simp [jointAverage, hZ]
  · unfold jointAverage
    rw [jointMoment_eq, jointMoment_eq, jointMoment_eq]
    simp only [mul_one]
    field_simp
    rw [mass_eq]
    ring

def rightSliceAverage (b : β → ℝ) (q : β → ℝ) (t : ℝ) (g : β → ℝ) : ℝ :=
  (∑ y, b y * (2 - t - q y) * g y) / (∑ y, b y * (2 - t - q y))

theorem rightSliceAverage_eq (b : β → ℝ) (q : β → ℝ) (t : ℝ) (g : β → ℝ) :
    rightSliceAverage b q t g =
      ((2 - t) * (∑ y, b y * g y) - (∑ y, b y * q y * g y)) /
        ((2 - t) * (∑ y, b y) - (∑ y, b y * q y)) := by
  unfold rightSliceAverage
  congr 1
  · calc
      (∑ y, b y * (2 - t - q y) * g y) =
          ∑ y, ((2 - t) * (b y * g y) - b y * q y * g y) := by
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  · calc
      (∑ y, b y * (2 - t - q y)) =
          ∑ y, ((2 - t) * b y - b y * q y) := by
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]

include sectionFintypeα in
theorem rightSliceAverage_span (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (hp : ∀ x, p x = 0 ∨ p x = 1) (g : β → ℝ) (x : α) :
    rightSliceAverage b q (p x) g =
      rightSliceAverage b q 0 g +
        (rightSliceAverage b q 1 g - rightSliceAverage b q 0 g) * p x := by
  have retainedsectionFintypeα := sectionFintypeα
  rcases hp x with h | h <;> rw [h] <;> ring

theorem offCenter_jointMoment_zero
    (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (hp : ∀ x, p x = 0 ∨ p x = 1) (hq : ∀ y, q y = 0 ∨ q y = 1) :
    jointMoment a b p q p q = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  rcases hp x with hpx | hpx <;> rcases hq y with hqy | hqy <;>
    norm_num [hpx, hqy]

theorem offCenter_covariance
    (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (hp : ∀ x, p x = 0 ∨ p x = 1) (hq : ∀ y, q y = 0 ∨ q y = 1) :
    jointAverage a b p q p q -
        jointAverage a b p q p (fun _ => 1) *
          jointAverage a b p q (fun _ => 1) q =
      -(jointAverage a b p q p (fun _ => 1) *
          jointAverage a b p q (fun _ => 1) q) := by
  have h : jointAverage a b p q p q = 0 := by
    simp only [jointAverage, offCenter_jointMoment_zero a b p q hp hq, zero_div]
  rw [h]
  ring

end Problem315.CrossCovariance

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/CrossCovariance.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/DisjointCellCounting.lean -/
section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.DisjointMarginal

variable {V : Type*} [Fintype V]
open DisjointEncoding

abbrev MarginData {α : Type*} [Fintype α] (A : Finset α) (q : Nat) :=
  {x : Fin 3 × Finset α // x.2 ⊆ A ∧ x.1.val + x.2.card = q}

abbrev LeftData (e : Fin 4 ↪ V) (G : SimpleGraph V) :=
  MarginData (BinaryAssignments.singletons (leftCounts e G))
    (CrossBlock.row (crossCode e G) 0 + (leftAssignment e G G).card)

abbrev RightData (e : Fin 4 ↪ V) (G : SimpleGraph V) :=
  MarginData (BinaryAssignments.singletons (rightCounts e G))
    (CrossBlock.col (crossCode e G) 0 + (rightAssignment e G G).card)

abbrev MatrixFiber (s : Nat) (r c : Fin 3) :=
  {M : CrossBlock.Matrix // CrossBlock.total M = s ∧
    CrossBlock.row M 0 = r.val ∧ CrossBlock.col M 0 = c.val}

abbrev JointData (e : Fin 4 ↪ V) (G : SimpleGraph V) :=
  Σ x : LeftData e G, Σ y : RightData e G,
    MatrixFiber (CrossBlock.total (crossCode e G)) x.val.1 y.val.1

def leftData (e : Fin 4 ↪ V) (G : SimpleGraph V) (c : FeasibleCoordinates e G) :
    LeftData e G :=
  ⟨(⟨CrossBlock.row c.matrix 0, by have := CrossBlock.row_le_two c.matrix 0; omega⟩, c.left),
    c.left_subset,
    ((coordinate_degrees_iff e G c.matrix c.left c.right c.left_subset c.right_subset).mp
      c.degrees).2.1⟩

def rightData (e : Fin 4 ↪ V) (G : SimpleGraph V) (c : FeasibleCoordinates e G) :
    RightData e G :=
  ⟨(⟨CrossBlock.col c.matrix 0, by have := CrossBlock.col_le_two c.matrix 0; omega⟩, c.right),
    c.right_subset,
    ((coordinate_degrees_iff e G c.matrix c.left c.right c.left_subset c.right_subset).mp
      c.degrees).2.2⟩

def toJointData (e : Fin 4 ↪ V) (G : SimpleGraph V) (c : FeasibleCoordinates e G) :
    JointData e G :=
  ⟨leftData e G c, rightData e G c, c.matrix,
    ((coordinate_degrees_iff e G c.matrix c.left c.right c.left_subset c.right_subset).mp
      c.degrees).1, rfl, rfl⟩

def fromJointData (e : Fin 4 ↪ V) (G : SimpleGraph V) (z : JointData e G) :
    FeasibleCoordinates e G where
  matrix := z.2.2.val
  left := z.1.val.2
  right := z.2.1.val.2
  left_subset := z.1.property.1
  right_subset := z.2.1.property.1
  degrees := by
    apply (coordinate_degrees_iff e G _ _ _ z.1.property.1 z.2.1.property.1).mpr
    exact ⟨z.2.2.property.1,
      by rw [z.2.2.property.2.1]; exact z.1.property.2,
      by rw [z.2.2.property.2.2]; exact z.2.1.property.2⟩

def coordinatesEquiv (e : Fin 4 ↪ V) (G : SimpleGraph V) :
    FeasibleCoordinates e G ≃ JointData e G where
  toFun := toJointData e G
  invFun := fromJointData e G
  left_inv c := by ext <;> rfl
  right_inv z := by
    rcases z with ⟨⟨⟨⟨r,hrlt⟩,U⟩,hU⟩, ⟨⟨⟨c,hclt⟩,W⟩,hW⟩, M, hs, hr, hc⟩
    dsimp only at hr hc
    subst r
    subst c
    rfl

def degreeCellJointEquiv (e : Fin 4 ↪ V) (G : SimpleGraph V) :
    DegreeCell e G ≃ JointData e G :=
  (degreeCellEquiv e G).trans (coordinatesEquiv e G)

theorem matrixFiber_card (s : Nat) (r c : Fin 3) :
    Fintype.card (MatrixFiber s r c) = CrossBlock.count s r c := by
  simp only [MatrixFiber, Fintype.card_subtype, CrossBlock.count]

theorem sum_degreeCell_joint
    (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (f : LeftData e G → ℝ) (g : RightData e G → ℝ) :
    (∑ H : DegreeCell e G,
      f (leftData e G (cellEncode e G H)) * g (rightData e G (cellEncode e G H))) =
    ∑ x : LeftData e G, ∑ y : RightData e G,
      (CrossBlock.count (CrossBlock.total (crossCode e G)) x.val.1 y.val.1 : ℝ) *
        f x * g y := by
  calc
    _ = ∑ z : JointData e G, f z.1 * g z.2.1 := by
      exact (degreeCellJointEquiv e G).sum_comp (fun z => f z.1 * g z.2.1)
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro y hy
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, matrixFiber_card]
      ring

theorem card_degreeCell_eq_sum_count (e : Fin 4 ↪ V) (G : SimpleGraph V) :
    (Fintype.card (DegreeCell e G) : ℝ) =
      ∑ x : LeftData e G, ∑ y : RightData e G,
        (CrossBlock.count (CrossBlock.total (crossCode e G)) x.val.1 y.val.1 : ℝ) := by
  simpa using sum_degreeCell_joint e G (fun _ => 1) (fun _ => 1)

theorem average_degreeCell_joint
    (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (f : LeftData e G → ℝ) (g : RightData e G → ℝ) :
    (∑ H : DegreeCell e G,
      f (leftData e G (cellEncode e G H)) * g (rightData e G (cellEncode e G H))) /
        (Fintype.card (DegreeCell e G) : ℝ) =
    (∑ x : LeftData e G, ∑ y : RightData e G,
      (CrossBlock.count (CrossBlock.total (crossCode e G)) x.val.1 y.val.1 : ℝ) *
        f x * g y) /
      (∑ x : LeftData e G, ∑ y : RightData e G,
        (CrossBlock.count (CrossBlock.total (crossCode e G)) x.val.1 y.val.1 : ℝ)) := by
  rw [sum_degreeCell_joint, card_degreeCell_eq_sum_count]

def flag (r : Fin 3) : ℝ := if r = 1 then 0 else 1

theorem flag_zero_or_one (r : Fin 3) : flag r = 0 ∨ flag r = 1 := by
  unfold flag
  split_ifs <;> simp

theorem sum_degreeCell_joint_two
    (e : Fin 4 ↪ V) (G : SimpleGraph V) (hs : CrossBlock.total (crossCode e G) = 2)
    (f : LeftData e G → ℝ) (g : RightData e G → ℝ) :
    (∑ H : DegreeCell e G,
      f (leftData e G (cellEncode e G H)) * g (rightData e G (cellEncode e G H))) =
    CrossCovariance.jointMoment (fun _ : LeftData e G => 1)
      (fun _ : RightData e G => 1) (fun x => flag x.val.1) (fun y => flag y.val.1) f g := by
  rw [sum_degreeCell_joint, hs]
  unfold CrossCovariance.jointMoment
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [CrossBlock.count_two_real]
  simp only [flag, one_mul]

theorem card_degreeCell_eq_mass_two
    (e : Fin 4 ↪ V) (G : SimpleGraph V) (hs : CrossBlock.total (crossCode e G) = 2) :
    (Fintype.card (DegreeCell e G) : ℝ) =
    CrossCovariance.mass (fun _ : LeftData e G => 1)
      (fun _ : RightData e G => 1) (fun x => flag x.val.1) (fun y => flag y.val.1) := by
  simpa only [CrossCovariance.mass, mul_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] using sum_degreeCell_joint_two e G hs (fun _ => 1) (fun _ => 1)

theorem average_degreeCell_joint_two
    (e : Fin 4 ↪ V) (G : SimpleGraph V) (hs : CrossBlock.total (crossCode e G) = 2)
    (f : LeftData e G → ℝ) (g : RightData e G → ℝ) :
    (∑ H : DegreeCell e G,
      f (leftData e G (cellEncode e G H)) * g (rightData e G (cellEncode e G H))) /
        (Fintype.card (DegreeCell e G) : ℝ) =
    CrossCovariance.jointAverage (fun _ : LeftData e G => 1)
      (fun _ : RightData e G => 1) (fun x => flag x.val.1) (fun y => flag y.val.1) f g := by
  rw [sum_degreeCell_joint_two e G hs, card_degreeCell_eq_mass_two e G hs]
  rfl

end Problem315.DisjointMarginal

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/DisjointCellCounting.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/DisjointStateCell.lean -/
section

namespace OAI

noncomputable section
open scoped Classical

namespace Problem315.DisjointEncoding

private theorem qualified_degree (n : Nat) (G : SimpleGraph (Fin n)) (v : Fin n) :
    graphDegree G v = G.degree v := by
  unfold graphDegree SimpleGraph.degree
  congr 1
  ext w
  simp

def stateCellToDegreeCell {n : Nat} {d : Fin n → Nat}
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    {H : GraphState n d // SameCell e G.val H.val} ≃ DegreeCell e G.val where
  toFun H := ⟨H.val.val, H.property, by
    intro v
    rw [← qualified_degree, ← qualified_degree]
    exact (H.val.property v).trans (G.property v).symm⟩
  invFun H := ⟨⟨H.val, by
    intro v
    rw [qualified_degree, H.property.2 v, ← qualified_degree]
    exact G.property v⟩, H.property.1⟩
  left_inv H := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv H := by apply Subtype.ext; rfl

def graphStateCellEquiv {n : Nat} {d : Fin n → Nat}
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    {H : GraphState n d // SameCell e G.val H.val} ≃ FeasibleCoordinates e G.val :=
  (stateCellToDegreeCell e G).trans (degreeCellEquiv e G.val)

end Problem315.DisjointEncoding

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/DisjointStateCell.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/DisjointFiberCell.lean -/
section

namespace OAI

noncomputable section
open scoped Classical

namespace Problem315.DisjointEncoding

private theorem pair_count {n : Nat} (G : SimpleGraph (Fin n))
    (u v w : Fin n) (huv : u ≠ v) :
    (({u, v} : Finset (Fin n)).filter (G.Adj w)).card = edgeBit G u w + edgeBit G v w := by
  rw [Finset.card_filter, Finset.sum_pair huv]
  simp [edgeBit, SimpleGraph.adj_comm]

private theorem outside_pair {n : Nat} (e : Fin 4 ↪ Fin n) (w : Fin n)
    (hw : Outside e w) (a b : Fin 4) : w ∉ ({e a, e b} : Finset (Fin n)) := by
  simp [hw a, hw b]

theorem sameCell_of_leftFiber {n : Nat} (e : Fin 4 ↪ Fin n)
    (G H : SimpleGraph (Fin n))
    (h : PairResampling.SameFiber {e 0, e 1} G H) : SameCell e G H := by
  have h01 : e 0 ≠ e 1 := e.injective.ne (by decide)
  have h20 : e 2 ≠ e 0 := e.injective.ne (by decide)
  have h21 : e 2 ≠ e 1 := e.injective.ne (by decide)
  have h30 : e 3 ≠ e 0 := e.injective.ne (by decide)
  have h31 : e 3 ≠ e 1 := e.injective.ne (by decide)
  have h2 : e 2 ∉ ({e 0, e 1} : Finset (Fin n)) := by simp [h20, h21]
  have h3 : e 3 ∉ ({e 0, e 1} : Finset (Fin n)) := by simp [h30, h31]
  constructor
  · intro u v hu hv
    exact h.1 u (outside_pair e u hu 0 1) v (outside_pair e v hv 0 1)
  · exact h.2.1 (e 0) (by simp) (e 1) (by simp)
  · exact h.1 (e 2) h2 (e 3) h3
  · intro w hw
    have hc := h.2.2 w (outside_pair e w hw 0 1)
    simpa only [pair_count G (e 0) (e 1) w h01, pair_count H (e 0) (e 1) w h01] using hc
  · intro w hw
    have h2w := h.1 (e 2) h2 w (outside_pair e w hw 0 1)
    have h3w := h.1 (e 3) h3 w (outside_pair e w hw 0 1)
    rw [(edgeBit_eq_iff G H (e 2) w).mpr h2w, (edgeBit_eq_iff G H (e 3) w).mpr h3w]

theorem sameCell_of_rightFiber {n : Nat} (e : Fin 4 ↪ Fin n)
    (G H : SimpleGraph (Fin n))
    (h : PairResampling.SameFiber {e 2, e 3} G H) : SameCell e G H := by
  have h23 : e 2 ≠ e 3 := e.injective.ne (by decide)
  have h02 : e 0 ≠ e 2 := e.injective.ne (by decide)
  have h03 : e 0 ≠ e 3 := e.injective.ne (by decide)
  have h12 : e 1 ≠ e 2 := e.injective.ne (by decide)
  have h13 : e 1 ≠ e 3 := e.injective.ne (by decide)
  have h0 : e 0 ∉ ({e 2, e 3} : Finset (Fin n)) := by simp [h02, h03]
  have h1 : e 1 ∉ ({e 2, e 3} : Finset (Fin n)) := by simp [h12, h13]
  constructor
  · intro u v hu hv
    exact h.1 u (outside_pair e u hu 2 3) v (outside_pair e v hv 2 3)
  · exact h.1 (e 0) h0 (e 1) h1
  · exact h.2.1 (e 2) (by simp) (e 3) (by simp)
  · intro w hw
    have h0w := h.1 (e 0) h0 w (outside_pair e w hw 2 3)
    have h1w := h.1 (e 1) h1 w (outside_pair e w hw 2 3)
    rw [(edgeBit_eq_iff G H (e 0) w).mpr h0w, (edgeBit_eq_iff G H (e 1) w).mpr h1w]
  · intro w hw
    have hc := h.2.2 w (outside_pair e w hw 2 3)
    simpa only [pair_count G (e 2) (e 3) w h23, pair_count H (e 2) (e 3) w h23] using hc

end Problem315.DisjointEncoding

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/DisjointFiberCell.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/DisjointFiberCoordinates.lean -/
section

namespace OAI

noncomputable section
open scoped Classical

namespace Problem315.DisjointEncoding

variable {V : Type*} [Fintype V]

theorem rightAssignment_eq_iff_first_edges
    (e : Fin 4 ↪ V) (G H K : SimpleGraph V)
    (hH : SameCell e G H) (hK : SameCell e G K) :
    rightAssignment e G H = rightAssignment e G K ↔
      ∀ w, Outside e w → (H.Adj (e 2) w ↔ K.Adj (e 2) w) := by
  constructor
  · intro h w hw
    apply first_edge_iff_of_counts G H K (e 2) (e 3) w
      (hH.rightCount w hw) (hK.rightCount w hw)
    intro hs
    have he := Finset.ext_iff.mp h ⟨w, hw⟩
    have member : ⟨w, hw⟩ ∈ BinaryAssignments.singletons (rightCounts e G) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
    constructor
    · intro adjacent
      exact (Finset.mem_filter.mp
        (he.mp (Finset.mem_filter.mpr ⟨member, adjacent⟩))).2
    · intro adjacent
      exact (Finset.mem_filter.mp
        (he.mpr (Finset.mem_filter.mpr ⟨member, adjacent⟩))).2
  · intro h
    ext w
    simp only [rightAssignment, Finset.mem_filter]
    rw [h w.val w.property]

theorem leftAssignment_eq_iff_first_edges
    (e : Fin 4 ↪ V) (G H K : SimpleGraph V)
    (hH : SameCell e G H) (hK : SameCell e G K) :
    leftAssignment e G H = leftAssignment e G K ↔
      ∀ w, Outside e w → (H.Adj (e 0) w ↔ K.Adj (e 0) w) := by
  constructor
  · intro h w hw
    apply first_edge_iff_of_counts G H K (e 0) (e 1) w
      (hH.leftCount w hw) (hK.leftCount w hw)
    intro hs
    have he := Finset.ext_iff.mp h ⟨w, hw⟩
    have member : ⟨w, hw⟩ ∈ BinaryAssignments.singletons (leftCounts e G) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
    constructor
    · intro adjacent
      exact (Finset.mem_filter.mp
        (he.mp (Finset.mem_filter.mpr ⟨member, adjacent⟩))).2
    · intro adjacent
      exact (Finset.mem_filter.mp
        (he.mpr (Finset.mem_filter.mpr ⟨member, adjacent⟩))).2
  · intro h
    ext w
    simp only [leftAssignment, Finset.mem_filter]
    rw [h w.val w.property]

theorem right_boundary_eq_of_assignment_eq
    (e : Fin 4 ↪ V) (G H K : SimpleGraph V)
    (hH : SameCell e G H) (hK : SameCell e G K)
    (h : rightAssignment e G H = rightAssignment e G K)
    (w : V) (hw : Outside e w) :
    (H.Adj (e 2) w ↔ K.Adj (e 2) w) ∧
      (H.Adj (e 3) w ↔ K.Adj (e 3) w) := by
  have hfirst := (rightAssignment_eq_iff_first_edges e G H K hH hK).mp h w hw
  refine ⟨hfirst, ?_⟩
  apply (edgeBit_eq_iff H K (e 3) w).mp
  have hbit := (edgeBit_eq_iff H K (e 2) w).mpr hfirst
  have hHcount := hH.rightCount w hw
  have hKcount := hK.rightCount w hw
  omega

theorem left_boundary_eq_of_assignment_eq
    (e : Fin 4 ↪ V) (G H K : SimpleGraph V)
    (hH : SameCell e G H) (hK : SameCell e G K)
    (h : leftAssignment e G H = leftAssignment e G K)
    (w : V) (hw : Outside e w) :
    (H.Adj (e 0) w ↔ K.Adj (e 0) w) ∧
      (H.Adj (e 1) w ↔ K.Adj (e 1) w) := by
  have hfirst := (leftAssignment_eq_iff_first_edges e G H K hH hK).mp h w hw
  refine ⟨hfirst, ?_⟩
  apply (edgeBit_eq_iff H K (e 1) w).mp
  have hbit := (edgeBit_eq_iff H K (e 0) w).mpr hfirst
  have hHcount := hH.leftCount w hw
  have hKcount := hK.leftCount w hw
  omega

variable {n : Nat} {d : Fin n → Nat}

theorem sameFiber_left_iff_rightAssignment_eq
    (e : Fin 4 ↪ Fin n) (G H K : GraphState n d)
    (hH : SameCell e G.val H.val) (hK : SameCell e G.val K.val) :
    PairResampling.SameFiber {e 0, e 1} H.val K.val ↔
      rightAssignment e G.val H.val = rightAssignment e G.val K.val := by
  have he (a b : Fin 4) (h : a ≠ b) : e a ≠ e b := fun heq => h (e.injective heq)
  constructor
  · intro h
    apply (rightAssignment_eq_iff_first_edges e G.val H.val K.val hH hK).mpr
    intro w hw
    exact h.1 (e 2) (by simp [he 2 0 (by decide), he 2 1 (by decide)])
      w (by simp [hw 0, hw 1])
  · intro h
    apply (PairResampling.sameFiber_state_iff {e 0,e 1} H K).mpr
    have hc := hH.symm.trans hK
    have hb := right_boundary_eq_of_assignment_eq e G.val H.val K.val hH hK h
    constructor
    · intro u hu v hv
      obtain ⟨u, rfl⟩ := (blockEquiv e).surjective u
      obtain ⟨v, rfl⟩ := (blockEquiv e).surjective v
      cases u with
      | inl a =>
        fin_cases a
        · simp at hu
        · simp at hu
        · cases v with
          | inl b =>
            fin_cases b
            · simp at hv
            · simp at hv
            · simp
            · exact hc.rightInternal
          | inr w => exact (hb w.val w.property).1
        · cases v with
          | inl b =>
            fin_cases b
            · simp at hv
            · simp at hv
            · exact (H.val.adj_comm _ _).trans (hc.rightInternal.trans (K.val.adj_comm _ _))
            · simp
          | inr w => exact (hb w.val w.property).2
      | inr u =>
        cases v with
        | inl b =>
          fin_cases b
          · simp at hv
          · simp at hv
          · exact (H.val.adj_comm _ _).trans
              ((hb u.val u.property).1.trans (K.val.adj_comm _ _))
          · exact (H.val.adj_comm _ _).trans
              ((hb u.val u.property).2.trans (K.val.adj_comm _ _))
        | inr v => exact hc.outer u.val v.val u.property v.property
    · intro u hu v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · simp
      · exact hc.leftInternal
      · exact (H.val.adj_comm _ _).trans (hc.leftInternal.trans (K.val.adj_comm _ _))
      · simp

theorem sameFiber_right_iff_leftAssignment_eq
    (e : Fin 4 ↪ Fin n) (G H K : GraphState n d)
    (hH : SameCell e G.val H.val) (hK : SameCell e G.val K.val) :
    PairResampling.SameFiber {e 2, e 3} H.val K.val ↔
      leftAssignment e G.val H.val = leftAssignment e G.val K.val := by
  have he (a b : Fin 4) (h : a ≠ b) : e a ≠ e b := fun heq => h (e.injective heq)
  constructor
  · intro h
    apply (leftAssignment_eq_iff_first_edges e G.val H.val K.val hH hK).mpr
    intro w hw
    exact h.1 (e 0) (by simp [he 0 2 (by decide), he 0 3 (by decide)])
      w (by simp [hw 2, hw 3])
  · intro h
    apply (PairResampling.sameFiber_state_iff {e 2,e 3} H K).mpr
    have hc := hH.symm.trans hK
    have hb := left_boundary_eq_of_assignment_eq e G.val H.val K.val hH hK h
    constructor
    · intro u hu v hv
      obtain ⟨u, rfl⟩ := (blockEquiv e).surjective u
      obtain ⟨v, rfl⟩ := (blockEquiv e).surjective v
      cases u with
      | inl a =>
        fin_cases a
        · cases v with
          | inl b =>
            fin_cases b
            · simp
            · exact hc.leftInternal
            · simp at hv
            · simp at hv
          | inr w => exact (hb w.val w.property).1
        · cases v with
          | inl b =>
            fin_cases b
            · exact (H.val.adj_comm _ _).trans (hc.leftInternal.trans (K.val.adj_comm _ _))
            · simp
            · simp at hv
            · simp at hv
          | inr w => exact (hb w.val w.property).2
        · simp at hu
        · simp at hu
      | inr u =>
        cases v with
        | inl b =>
          fin_cases b
          · exact (H.val.adj_comm _ _).trans
              ((hb u.val u.property).1.trans (K.val.adj_comm _ _))
          · exact (H.val.adj_comm _ _).trans
              ((hb u.val u.property).2.trans (K.val.adj_comm _ _))
          · simp at hv
          · simp at hv
        | inr v => exact hc.outer u.val v.val u.property v.property
    · intro u hu v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · simp
      · exact hc.rightInternal
      · exact (H.val.adj_comm _ _).trans (hc.rightInternal.trans (K.val.adj_comm _ _))
      · simp

end Problem315.DisjointEncoding

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/DisjointFiberCoordinates.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/DisjointStateLaw.lean -/
section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.DisjointMarginal
open DisjointEncoding

theorem marginData_eq_iff_subset_eq {α : Type*} [Fintype α]
    {A : Finset α} {q : Nat} (x y : MarginData A q) :
    x = y ↔ x.val.2 = y.val.2 := by
  constructor
  · rintro rfl
    rfl
  · intro h
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      have hx := x.property.2
      have hy := y.property.2
      rw [h] at hx
      omega
    · exact h

variable {n : Nat} {d : Fin n → Nat}

abbrev StateCell (e : Fin 4 ↪ Fin n) (G : GraphState n d) :=
  {H : GraphState n d // SameCell e G.val H.val}

instance stateCellNonempty (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    Nonempty (StateCell e G) := ⟨⟨G, SameCell.refl e G.val⟩⟩

def stateLeftData (e : Fin 4 ↪ Fin n) (G : GraphState n d) (H : StateCell e G) :
    LeftData e G.val := leftData e G.val (graphStateCellEquiv e G H)

def stateRightData (e : Fin 4 ↪ Fin n) (G : GraphState n d) (H : StateCell e G) :
    RightData e G.val := rightData e G.val (graphStateCellEquiv e G H)

@[simp] theorem stateLeftData_subset (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) : (stateLeftData e G H).val.2 = leftAssignment e G.val H.val.val := rfl

@[simp] theorem stateRightData_subset (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) : (stateRightData e G H).val.2 = rightAssignment e G.val H.val.val := rfl

theorem sameFiber_left_iff_stateRightData_eq
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (H K : StateCell e G) :
    PairResampling.SameFiber {e 0,e 1} H.val.val K.val.val ↔
      stateRightData e G H = stateRightData e G K := by
  rw [marginData_eq_iff_subset_eq, stateRightData_subset, stateRightData_subset]
  exact sameFiber_left_iff_rightAssignment_eq e G H.val K.val H.property K.property

theorem sameFiber_right_iff_stateLeftData_eq
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (H K : StateCell e G) :
    PairResampling.SameFiber {e 2,e 3} H.val.val K.val.val ↔
      stateLeftData e G H = stateLeftData e G K := by
  rw [marginData_eq_iff_subset_eq, stateLeftData_subset, stateLeftData_subset]
  exact sameFiber_right_iff_leftAssignment_eq e G H.val K.val H.property K.property

theorem stateCell_of_leftFiber
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (H : StateCell e G)
    (K : GraphState n d) (h : PairResampling.SameFiber {e 0,e 1} H.val.val K.val) :
    SameCell e G.val K.val :=
  H.property.trans (sameCell_of_leftFiber e H.val.val K.val h)

theorem stateCell_of_rightFiber
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (H : StateCell e G)
    (K : GraphState n d) (h : PairResampling.SameFiber {e 2,e 3} H.val.val K.val) :
    SameCell e G.val K.val :=
  H.property.trans (sameCell_of_rightFiber e H.val.val K.val h)

def stateCellJointEquiv (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    StateCell e G ≃ JointData e G.val :=
  (stateCellToDegreeCell e G).trans (degreeCellJointEquiv e G.val)

theorem stateCell_card_eq (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    Fintype.card (StateCell e G) = Fintype.card (DegreeCell e G.val) :=
  Fintype.card_congr (stateCellToDegreeCell e G)

theorem sum_stateCell_joint
    (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (f : LeftData e G.val → ℝ) (g : RightData e G.val → ℝ) :
    (∑ H : StateCell e G, f (stateLeftData e G H) * g (stateRightData e G H)) =
    ∑ x : LeftData e G.val, ∑ y : RightData e G.val,
      (CrossBlock.count (CrossBlock.total (crossCode e G.val)) x.val.1 y.val.1 : ℝ) *
        f x * g y := by
  calc
    _ = ∑ z : JointData e G.val, f z.1 * g z.2.1 :=
      (stateCellJointEquiv e G).sum_comp _
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro y hy
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, matrixFiber_card]
      ring

theorem stateCell_card_eq_sum_count (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    (Fintype.card (StateCell e G) : ℝ) =
      ∑ x : LeftData e G.val, ∑ y : RightData e G.val,
        (CrossBlock.count (CrossBlock.total (crossCode e G.val)) x.val.1 y.val.1 : ℝ) := by
  simpa using sum_stateCell_joint e G (fun _ => 1) (fun _ => 1)

theorem average_stateCell_joint
    (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (f : LeftData e G.val → ℝ) (g : RightData e G.val → ℝ) :
    (∑ H : StateCell e G, f (stateLeftData e G H) * g (stateRightData e G H)) /
        (Fintype.card (StateCell e G) : ℝ) =
    (∑ x : LeftData e G.val, ∑ y : RightData e G.val,
      (CrossBlock.count (CrossBlock.total (crossCode e G.val)) x.val.1 y.val.1 : ℝ) *
        f x * g y) /
      (∑ x : LeftData e G.val, ∑ y : RightData e G.val,
        (CrossBlock.count (CrossBlock.total (crossCode e G.val)) x.val.1 y.val.1 : ℝ)) := by
  rw [sum_stateCell_joint, stateCell_card_eq_sum_count]

theorem average_stateCell_joint_two
    (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (hs : CrossBlock.total (crossCode e G.val) = 2)
    (f : LeftData e G.val → ℝ) (g : RightData e G.val → ℝ) :
    (∑ H : StateCell e G, f (stateLeftData e G H) * g (stateRightData e G H)) /
        (Fintype.card (StateCell e G) : ℝ) =
    CrossCovariance.jointAverage (fun _ : LeftData e G.val => 1)
      (fun _ : RightData e G.val => 1) (fun x => flag x.val.1) (fun y => flag y.val.1) f g := by
  rw [average_stateCell_joint]
  unfold CrossCovariance.jointAverage CrossCovariance.mass CrossCovariance.jointMoment
  rw [hs]
  simp only [CrossBlock.count_two_real, flag, one_mul, mul_one]

theorem stateCell_joint_fiber_card
    (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (x : LeftData e G.val) (y : RightData e G.val) :
    ((Finset.univ : Finset (StateCell e G)).filter
      (fun H => stateLeftData e G H = x ∧ stateRightData e G H = y)).card =
      CrossBlock.count (CrossBlock.total (crossCode e G.val)) x.val.1 y.val.1 := by
  have h := sum_stateCell_joint e G
    (fun z => if z = x then (1 : ℝ) else 0)
    (fun z => if z = y then (1 : ℝ) else 0)
  have hc :
      (((Finset.univ : Finset (StateCell e G)).filter
        (fun H => stateLeftData e G H = x ∧ stateRightData e G H = y)).card : ℝ) =
      ∑ H : StateCell e G,
        (if stateLeftData e G H = x then (1 : ℝ) else 0) *
          (if stateRightData e G H = y then (1 : ℝ) else 0) := by
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro H hH
    by_cases hx : stateLeftData e G H = x <;>
      by_cases hy : stateRightData e G H = y <;> simp [hx,hy]
  rw [← hc] at h
  have hh :
      (((Finset.univ : Finset (StateCell e G)).filter
        (fun H => stateLeftData e G H = x ∧ stateRightData e G H = y)).card : ℝ) =
        (CrossBlock.count (CrossBlock.total (crossCode e G.val)) x.val.1 y.val.1 : ℝ) := by
    simpa [mul_ite] using h
  exact_mod_cast hh

theorem stateCell_card_pos (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    0 < Fintype.card (StateCell e G) := Fintype.card_pos

theorem stateCell_mass_two_pos
    (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (hs : CrossBlock.total (crossCode e G.val) = 2) :
    0 < CrossCovariance.mass (fun _ : LeftData e G.val => 1)
      (fun _ : RightData e G.val => 1) (fun x => flag x.val.1) (fun y => flag y.val.1) := by
  have hcard := stateCell_card_eq_sum_count e G
  rw [hs] at hcard
  have hm : CrossCovariance.mass (fun _ : LeftData e G.val => 1)
      (fun _ : RightData e G.val => 1) (fun x => flag x.val.1) (fun y => flag y.val.1) =
      (Fintype.card (StateCell e G) : ℝ) := by
    rw [hcard]
    simp only [CrossCovariance.mass, CrossCovariance.jointMoment,
      CrossBlock.count_two_real, flag, one_mul, mul_one]
  rw [hm]
  exact_mod_cast stateCell_card_pos e G

end Problem315.DisjointMarginal

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/DisjointStateLaw.lean -/
