import AnalyticPrelude

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/TripleStateReindex.lean -/
section

namespace OAI

noncomputable section

namespace Problem315.TripleStateReindex

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {V W : Type*} [sectionFintypeV : Fintype V] [sectionFintypeW : Fintype W]

def degreeCount (G : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (G.Adj v)).card

theorem degreeCount_comap (e : V ≃ W) (G : SimpleGraph W) (v : V) :
    degreeCount (G.comap e) v = degreeCount G (e v) := by
  classical
  unfold degreeCount
  apply Finset.card_bij (fun w _ => e w)
  · intro w hw
    simpa using hw
  · intro u hu w hw he
    exact e.injective he
  · intro w hw
    refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
    simpa using hw

def graphEquiv (e : V ≃ W) : SimpleGraph W ≃ SimpleGraph V where
  toFun G := G.comap e
  invFun G := G.comap e.symm
  left_inv G := by ext u v; simp
  right_inv G := by ext u v; simp

include sectionFintypeV sectionFintypeW in
@[simp] theorem graphEquiv_adj (e : V ≃ W) (G : SimpleGraph W) (u v : V) :
    (graphEquiv e G).Adj u v ↔ G.Adj (e u) (e v) := by
  have retainedsectionFintypeV := sectionFintypeV
  have retainedsectionFintypeW := sectionFintypeW
  exact Iff.rfl

def fixedDegreeEquiv (e : V ≃ W) (d : W → ℕ) :
    {G : SimpleGraph W // ∀ v, degreeCount G v = d v} ≃
      {G : SimpleGraph V // ∀ v, degreeCount G v = d (e v)} where
  toFun G := ⟨graphEquiv e G.val, fun v => by
    rw [show graphEquiv e G.val = G.val.comap e from rfl, degreeCount_comap]
    exact G.property (e v)⟩
  invFun G := ⟨(graphEquiv e).symm G.val, fun v => by
    change degreeCount (G.val.comap e.symm) v = d v
    rw [degreeCount_comap, G.property, e.apply_symm_apply]⟩
  left_inv G := by apply Subtype.ext; exact (graphEquiv e).left_inv G.val
  right_inv G := by apply Subtype.ext; exact (graphEquiv e).right_inv G.val

variable {n : ℕ} (s : Finset (Fin n)) (hs : s.card = 3)

abbrev Outside := {v : Fin n // v ∉ s}

def tripleEnum : Fin 3 ≃ ↥s :=
  (Fintype.equivFinOfCardEq (by simpa using hs)).symm

def splitEquiv : (Fin 3 ⊕ Outside s) ≃ Fin n :=
  (Equiv.sumCongr (tripleEnum s hs) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun v : Fin n => v ∈ s))

@[simp] theorem splitEquiv_inl (i : Fin 3) :
    splitEquiv s hs (Sum.inl i) = (tripleEnum s hs i).val := rfl

@[simp] theorem splitEquiv_inr (v : Outside s) :
    splitEquiv s hs (Sum.inr v) = v.val := rfl

@[simp] theorem splitEquiv_inl_mem (i : Fin 3) :
    splitEquiv s hs (Sum.inl i) ∈ s := (tripleEnum s hs i).property

@[simp] theorem splitEquiv_inr_not_mem (v : Outside s) :
    splitEquiv s hs (Sum.inr v) ∉ s := v.property

def stateEquiv (d : Fin n → ℕ) : GraphState n d ≃
    {G : SimpleGraph (Fin 3 ⊕ Outside s) //
      ∀ v, degreeCount G v = d (splitEquiv s hs v)} :=
  fixedDegreeEquiv (splitEquiv s hs) d

@[simp] theorem stateEquiv_adj (d : Fin n → ℕ) (G : GraphState n d)
    (u v : Fin 3 ⊕ Outside s) :
    (stateEquiv s hs d G).val.Adj u v ↔
      G.val.Adj (splitEquiv s hs u) (splitEquiv s hs v) := Iff.rfl

@[simp] theorem stateEquiv_outside_adj (d : Fin n → ℕ) (G : GraphState n d)
    (u v : Outside s) :
    (stateEquiv s hs d G).val.Adj (Sum.inr u) (Sum.inr v) ↔
      G.val.Adj u.val v.val := Iff.rfl

theorem sum_stateEquiv (d : Fin n → ℕ)
    (f : {G : SimpleGraph (Fin 3 ⊕ Outside s) //
      ∀ v, degreeCount G v = d (splitEquiv s hs v)} → ℝ) :
    ∑ G : GraphState n d, f (stateEquiv s hs d G) = ∑ G, f G :=
  (stateEquiv s hs d).sum_comp f

theorem stateCount_eq (d : Fin n → ℕ) :
    stateCount n d = Fintype.card
      {G : SimpleGraph (Fin 3 ⊕ Outside s) //
        ∀ v, degreeCount G v = d (splitEquiv s hs v)} := by
  change Fintype.card (GraphState n d) = _
  exact Fintype.card_congr (stateEquiv s hs d)

theorem uniformAverage_stateEquiv (d : Fin n → ℕ)
    (f : {G : SimpleGraph (Fin 3 ⊕ Outside s) //
      ∀ v, degreeCount G v = d (splitEquiv s hs v)} → ℝ) :
    uniformAverage n d (fun G => f (stateEquiv s hs d G)) =
      (∑ G, f G) / (Fintype.card
        {G : SimpleGraph (Fin 3 ⊕ Outside s) //
          ∀ v, degreeCount G v = d (splitEquiv s hs v)} : ℝ) := by
  unfold uniformAverage
  rw [stateCount_eq s hs d]
  congr 1
  exact sum_stateEquiv s hs d f

theorem uniformVariance_stateEquiv (d : Fin n → ℕ)
    (f : {G : SimpleGraph (Fin 3 ⊕ Outside s) //
      ∀ v, degreeCount G v = d (splitEquiv s hs v)} → ℝ) :
    uniformVariance n d (fun G => f (stateEquiv s hs d G)) =
      (∑ G, (f G - (∑ H, f H) / (Fintype.card
        {H : SimpleGraph (Fin 3 ⊕ Outside s) //
          ∀ v, degreeCount H v = d (splitEquiv s hs v)} : ℝ)) ^ 2) /
            (Fintype.card
              {G : SimpleGraph (Fin 3 ⊕ Outside s) //
                ∀ v, degreeCount G v = d (splitEquiv s hs v)} : ℝ) := by
  unfold uniformVariance
  rw [uniformAverage_stateEquiv]
  exact uniformAverage_stateEquiv s hs d (fun G =>
    (f G - (∑ H, f H) / (Fintype.card
      {H : SimpleGraph (Fin 3 ⊕ Outside s) //
        ∀ v, degreeCount H v = d (splitEquiv s hs v)} : ℝ)) ^ 2)

end Problem315.TripleStateReindex

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/TripleStateReindex.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/TripleInternalEncoding.lean -/
section

namespace OAI

noncomputable section
namespace Problem315.TripleInternalEncoding
attribute [local instance] Classical.propDecidable

def edgeBit (G : SimpleGraph (Fin 3)) (u v : Fin 3) : ℕ :=
  if G.Adj u v then 1 else 0

def internalEdgeCount (G : SimpleGraph (Fin 3)) : ℕ :=
  edgeBit G 0 1 + edgeBit G 0 2 + edgeBit G 1 2

theorem degree_zero (G : SimpleGraph (Fin 3)) :
    graphDegree G 0 = edgeBit G 0 1 + edgeBit G 0 2 := by
  classical
  simp only [graphDegree, Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_three]
  simp [edgeBit]

theorem degree_one (G : SimpleGraph (Fin 3)) :
    graphDegree G 1 = edgeBit G 0 1 + edgeBit G 1 2 := by
  classical
  simp only [graphDegree, Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_three]
  simp [edgeBit, G.adj_comm]

theorem degree_two (G : SimpleGraph (Fin 3)) :
    graphDegree G 2 = edgeBit G 0 2 + edgeBit G 1 2 := by
  classical
  simp only [graphDegree, Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_three]
  simp [edgeBit, G.adj_comm]

theorem edgeBit_le_one (G : SimpleGraph (Fin 3)) (u v : Fin 3) :
    edgeBit G u v ≤ 1 := by
  unfold edgeBit
  split <;> omega

theorem edgeBit_eq_iff (G H : SimpleGraph (Fin 3)) (u v : Fin 3) :
    edgeBit G u v = edgeBit H u v ↔ (G.Adj u v ↔ H.Adj u v) := by
  by_cases hg : G.Adj u v <;> by_cases hh : H.Adj u v <;> simp [edgeBit, hg, hh]

theorem degree_injective : Function.Injective
    (fun G : SimpleGraph (Fin 3) => graphDegree G) := by
  intro G H h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  change graphDegree G 0 = graphDegree H 0 at h0
  change graphDegree G 1 = graphDegree H 1 at h1
  change graphDegree G 2 = graphDegree H 2 at h2
  rw [degree_zero, degree_zero] at h0
  rw [degree_one, degree_one] at h1
  rw [degree_two, degree_two] at h2
  have h01 : G.Adj 0 1 ↔ H.Adj 0 1 :=
    (edgeBit_eq_iff G H 0 1).mp (by omega)
  have h02 : G.Adj 0 2 ↔ H.Adj 0 2 :=
    (edgeBit_eq_iff G H 0 2).mp (by omega)
  have h12 : G.Adj 1 2 ↔ H.Adj 1 2 :=
    (edgeBit_eq_iff G H 1 2).mp (by omega)
  have h10 : G.Adj 1 0 ↔ H.Adj 1 0 :=
    (G.adj_comm 1 0).trans (h01.trans (H.adj_comm 0 1))
  have h20 : G.Adj 2 0 ↔ H.Adj 2 0 :=
    (G.adj_comm 2 0).trans (h02.trans (H.adj_comm 0 2))
  have h21 : G.Adj 2 1 ↔ H.Adj 2 1 :=
    (G.adj_comm 2 1).trans (h12.trans (H.adj_comm 1 2))
  ext u v
  fin_cases u <;> fin_cases v <;> simp_all

theorem internalEdgeCount_le_three (G : SimpleGraph (Fin 3)) :
    internalEdgeCount G ≤ 3 := by
  have h01 := edgeBit_le_one G 0 1
  have h02 := edgeBit_le_one G 0 2
  have h12 := edgeBit_le_one G 1 2
  unfold internalEdgeCount
  omega

theorem sum_degrees (G : SimpleGraph (Fin 3)) :
    ∑ v, graphDegree G v = 2 * internalEdgeCount G := by
  rw [Fin.sum_univ_three, degree_zero, degree_one, degree_two]
  unfold internalEdgeCount
  omega

theorem degree_le_internalEdgeCount (G : SimpleGraph (Fin 3)) (v : Fin 3) :
    graphDegree G v ≤ internalEdgeCount G := by
  fin_cases v
  · change graphDegree G 0 ≤ _
    rw [degree_zero]
    unfold internalEdgeCount
    omega
  · change graphDegree G 1 ≤ _
    rw [degree_one]
    unfold internalEdgeCount
    omega
  · change graphDegree G 2 ≤ _
    rw [degree_two]
    unfold internalEdgeCount
    omega

theorem degree_le_two (G : SimpleGraph (Fin 3)) (v : Fin 3) :
    graphDegree G v ≤ 2 := by
  have h01 := edgeBit_le_one G 0 1
  have h02 := edgeBit_le_one G 0 2
  have h12 := edgeBit_le_one G 1 2
  fin_cases v
  · change graphDegree G 0 ≤ 2
    rw [degree_zero]
    omega
  · change graphDegree G 1 ≤ 2
    rw [degree_one]
    omega
  · change graphDegree G 2 ≤ 2
    rw [degree_two]
    omega

theorem one_le_degree_of_two_edges (G : SimpleGraph (Fin 3))
    (he : internalEdgeCount G = 2) (v : Fin 3) :
    1 ≤ graphDegree G v := by
  have h01 := edgeBit_le_one G 0 1
  have h02 := edgeBit_le_one G 0 2
  have h12 := edgeBit_le_one G 1 2
  unfold internalEdgeCount at he
  fin_cases v
  · change 1 ≤ graphDegree G 0
    rw [degree_zero]
    omega
  · change 1 ≤ graphDegree G 1
    rw [degree_one]
    omega
  · change 1 ≤ graphDegree G 2
    rw [degree_two]
    omega

theorem degree_eq_zero_of_no_edges (G : SimpleGraph (Fin 3))
    (he : internalEdgeCount G = 0) (v : Fin 3) : graphDegree G v = 0 := by
  have h := degree_le_internalEdgeCount G v
  omega

theorem degree_eq_two_of_three_edges (G : SimpleGraph (Fin 3))
    (he : internalEdgeCount G = 3) (v : Fin 3) : graphDegree G v = 2 := by
  have h01 := edgeBit_le_one G 0 1
  have h02 := edgeBit_le_one G 0 2
  have h12 := edgeBit_le_one G 1 2
  unfold internalEdgeCount at he
  fin_cases v
  · change graphDegree G 0 = 2
    rw [degree_zero]
    omega
  · change graphDegree G 1 = 2
    rw [degree_one]
    omega
  · change graphDegree G 2 = 2
    rw [degree_two]
    omega

def extraColumn (G : SimpleGraph (Fin 3)) (v : Fin 3) : ℕ :=
  if internalEdgeCount G = 1 then graphDegree G v
  else if internalEdgeCount G = 2 then graphDegree G v - 1 else 0

theorem extraColumn_le_one (G : SimpleGraph (Fin 3)) (v : Fin 3) :
    extraColumn G v ≤ 1 := by
  unfold extraColumn
  split
  · have h := degree_le_internalEdgeCount G v
    omega
  · split
    · have h := degree_le_two G v
      omega
    · omega

theorem sum_extraColumn (G : SimpleGraph (Fin 3)) :
    ∑ v, extraColumn G v =
      if internalEdgeCount G = 1 then 2 else if internalEdgeCount G = 2 then 1 else 0 := by
  by_cases h1 : internalEdgeCount G = 1
  · simp only [extraColumn, h1, ite_true]
    rw [sum_degrees, h1]
  · by_cases h2 : internalEdgeCount G = 2
    · simp only [extraColumn, h2, show (2 : ℕ) ≠ 1 by decide, ite_false, ite_true, Fin.sum_univ_three]
      have hsum := sum_degrees G
      rw [Fin.sum_univ_three, h2] at hsum
      have h0 := one_le_degree_of_two_edges G h2 0
      have h1 := one_le_degree_of_two_edges G h2 1
      have h2 := one_le_degree_of_two_edges G h2 2
      omega
    · simp [extraColumn, h1, h2]

theorem degree_from_extraColumn (G : SimpleGraph (Fin 3)) (v : Fin 3) :
    graphDegree G v =
      if internalEdgeCount G = 0 then 0
      else if internalEdgeCount G = 1 then extraColumn G v
      else if internalEdgeCount G = 2 then extraColumn G v + 1 else 2 := by
  have he := internalEdgeCount_le_three G
  have hcases : internalEdgeCount G = 0 ∨ internalEdgeCount G = 1 ∨
      internalEdgeCount G = 2 ∨ internalEdgeCount G = 3 := by omega
  rcases hcases with h | h | h | h
  · simp [h, degree_eq_zero_of_no_edges G h v]
  · simp [h, extraColumn]
  · have hd := one_le_degree_of_two_edges G h v
    simp [h, extraColumn]
    omega
  · simp [h, degree_eq_two_of_three_edges G h v]

theorem encoded_graph_injective : Function.Injective
    (fun G : SimpleGraph (Fin 3) => (internalEdgeCount G, extraColumn G)) := by
  intro G H h
  have he : internalEdgeCount G = internalEdgeCount H := congrArg Prod.fst h
  have hx : extraColumn G = extraColumn H := congrArg Prod.snd h
  apply degree_injective
  funext v
  change graphDegree G v = graphDegree H v
  rw [degree_from_extraColumn, degree_from_extraColumn, he, hx]

def oneEdgeGraph (x : Fin 3 → ℕ) : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel (fun u v => x u = 1 ∧ x v = 1)

def twoEdgeGraph (x : Fin 3 → ℕ) : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel (fun u v => x u = 1 ∨ x v = 1)

theorem oneEdgeGraph_spec (x : Fin 3 → ℕ) (hx : ∀ v, x v ≤ 1)
    (hs : ∑ v, x v = 2) :
    internalEdgeCount (oneEdgeGraph x) = 1 ∧ graphDegree (oneEdgeGraph x) = x := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  rw [Fin.sum_univ_three] at hs
  have hcases : (x 0 = 0 ∧ x 1 = 1 ∧ x 2 = 1) ∨
      (x 0 = 1 ∧ x 1 = 0 ∧ x 2 = 1) ∨
      (x 0 = 1 ∧ x 1 = 1 ∧ x 2 = 0) := by omega
  rcases hcases with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  all_goals
    have hd0 : graphDegree (oneEdgeGraph x) 0 = x 0 := by
      rw [degree_zero]
      simp [edgeBit, oneEdgeGraph, SimpleGraph.fromRel_adj, h0, h1, h2]
    have hd1 : graphDegree (oneEdgeGraph x) 1 = x 1 := by
      rw [degree_one]
      simp [edgeBit, oneEdgeGraph, SimpleGraph.fromRel_adj, h0, h1, h2]
    have hd2 : graphDegree (oneEdgeGraph x) 2 = x 2 := by
      rw [degree_two]
      simp [edgeBit, oneEdgeGraph, SimpleGraph.fromRel_adj, h0, h1, h2]
    refine ⟨?_, ?_⟩
    · simp [internalEdgeCount, edgeBit, oneEdgeGraph, SimpleGraph.fromRel_adj, h0, h1, h2]
    · funext v
      fin_cases v
      · exact hd0
      · exact hd1
      · exact hd2

theorem twoEdgeGraph_spec (x : Fin 3 → ℕ) (hx : ∀ v, x v ≤ 1)
    (hs : ∑ v, x v = 1) :
    internalEdgeCount (twoEdgeGraph x) = 2 ∧
      graphDegree (twoEdgeGraph x) = fun v => x v + 1 := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  rw [Fin.sum_univ_three] at hs
  have hcases : (x 0 = 1 ∧ x 1 = 0 ∧ x 2 = 0) ∨
      (x 0 = 0 ∧ x 1 = 1 ∧ x 2 = 0) ∨
      (x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 1) := by omega
  rcases hcases with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  all_goals
    have hd0 : graphDegree (twoEdgeGraph x) 0 = x 0 + 1 := by
      rw [degree_zero]
      simp [edgeBit, twoEdgeGraph, SimpleGraph.fromRel_adj, h0, h1, h2]
    have hd1 : graphDegree (twoEdgeGraph x) 1 = x 1 + 1 := by
      rw [degree_one]
      simp [edgeBit, twoEdgeGraph, SimpleGraph.fromRel_adj, h0, h1, h2]
    have hd2 : graphDegree (twoEdgeGraph x) 2 = x 2 + 1 := by
      rw [degree_two]
      simp [edgeBit, twoEdgeGraph, SimpleGraph.fromRel_adj, h0, h1, h2]
    refine ⟨?_, ?_⟩
    · simp [internalEdgeCount, edgeBit, twoEdgeGraph, SimpleGraph.fromRel_adj, h0, h1, h2]
    · funext v
      fin_cases v
      · exact hd0
      · exact hd1
      · exact hd2

def columnSum (e : ℕ) : ℕ := if e = 1 then 2 else if e = 2 then 1 else 0

theorem exists_graph_of_column (e : ℕ) (he : e ≤ 3) (x : Fin 3 → ℕ)
    (hx : ∀ v, x v ≤ 1) (hs : ∑ v, x v = columnSum e) :
    ∃ G : SimpleGraph (Fin 3), internalEdgeCount G = e ∧ extraColumn G = x := by
  have hcases : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · have hx0 : ∀ v, x v = 0 := by
      have hs0 : ∑ v, x v = 0 := by simpa [columnSum] using hs
      intro v
      exact Finset.sum_eq_zero_iff.mp hs0 v (Finset.mem_univ v)
    refine ⟨⊥, ?_, ?_⟩
    · simp [internalEdgeCount, edgeBit]
    · funext v
      simp [extraColumn, internalEdgeCount, edgeBit, hx0]
  · have hs2 : ∑ v, x v = 2 := by simpa [columnSum] using hs
    obtain ⟨he, hd⟩ := oneEdgeGraph_spec x hx hs2
    refine ⟨oneEdgeGraph x, he, ?_⟩
    funext v
    simp only [extraColumn, he, ite_true, hd]
  · have hs1 : ∑ v, x v = 1 := by simpa [columnSum] using hs
    obtain ⟨he, hd⟩ := twoEdgeGraph_spec x hx hs1
    refine ⟨twoEdgeGraph x, he, ?_⟩
    funext v
    simp [extraColumn, he, hd]
  · have hx0 : ∀ v, x v = 0 := by
      have hs0 : ∑ v, x v = 0 := by simpa [columnSum] using hs
      intro v
      exact Finset.sum_eq_zero_iff.mp hs0 v (Finset.mem_univ v)
    refine ⟨⊤, ?_, ?_⟩
    · simp [internalEdgeCount, edgeBit]
    · funext v
      simp [extraColumn, internalEdgeCount, edgeBit, hx0]

abbrev Column (e : ℕ) :=
  {x : Fin 3 → ℕ // (∀ v, x v ≤ 1) ∧ ∑ v, x v = columnSum e}

def fixedEdgeEncodingEquiv (e : ℕ) (he : e ≤ 3) :
    {G : SimpleGraph (Fin 3) // internalEdgeCount G = e} ≃ Column e := by
  let F : {G : SimpleGraph (Fin 3) // internalEdgeCount G = e} → Column e :=
    fun G => ⟨extraColumn G.val, extraColumn_le_one G.val, by
      simpa only [columnSum, G.property] using sum_extraColumn G.val⟩
  apply Equiv.ofBijective F
  constructor
  · intro G H h
    apply Subtype.ext
    apply encoded_graph_injective
    apply Prod.ext
    · exact G.property.trans H.property.symm
    · exact congrArg Subtype.val h
  · intro x
    obtain ⟨G, hG, hx⟩ := exists_graph_of_column e he x.val x.property.1 x.property.2
    refine ⟨⟨G, hG⟩, ?_⟩
    apply Subtype.ext
    exact hx

end Problem315.TripleInternalEncoding

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/TripleInternalEncoding.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/TripleMatrixEncoding.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315.TripleInternalEncoding

def rowOffset (e : ℕ) : ℕ := if e = 2 then 1 else if e = 3 then 2 else 0

theorem degree_eq_extra_add_offset (G : SimpleGraph (Fin 3)) (v : Fin 3) :
    graphDegree G v = extraColumn G v + rowOffset (internalEdgeCount G) := by
  have he := internalEdgeCount_le_three G
  have hcases : internalEdgeCount G = 0 ∨ internalEdgeCount G = 1 ∨
      internalEdgeCount G = 2 ∨ internalEdgeCount G = 3 := by omega
  rcases hcases with h | h | h | h
  · simp [extraColumn, rowOffset, h, degree_eq_zero_of_no_edges G h v]
  · simp [extraColumn, rowOffset, h]
  · have hd := one_le_degree_of_two_edges G h v
    simp [extraColumn, rowOffset, h]
    omega
  · simp [extraColumn, rowOffset, h, degree_eq_two_of_three_edges G h v]

variable (W : Type*) [Fintype W]

@[ext]
structure TripleCell (e : ℕ) (d : Fin 3 → ℕ) (c : W → ℕ) where
  outside : Fin 3 → W → ℕ
  inside : SimpleGraph (Fin 3)
  edge_count : internalEdgeCount inside = e
  binary : ∀ v w, outside v w ≤ 1
  columns : ∀ w, ∑ v, outside v w = c w
  rows : ∀ v, (∑ w, outside v w) + graphDegree inside v = d v

@[ext]
structure AugmentedMatrix (e : ℕ) (d : Fin 3 → ℕ) (c : W → ℕ) where
  matrix : Fin 3 → Option W → ℕ
  binary : ∀ v w, matrix v w ≤ 1
  columns : ∀ w, ∑ v, matrix v w = w.elim (columnSum e) c
  rows : ∀ v, (∑ w, matrix v w) = d v - rowOffset e

variable {W}

def encodeCell {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (A : TripleCell W e d c) : AugmentedMatrix W e d c where
  matrix v w := w.elim (extraColumn A.inside v) (A.outside v)
  binary v w := by
    cases w with
    | none => exact extraColumn_le_one A.inside v
    | some w => exact A.binary v w
  columns w := by
    cases w with
    | none =>
        simpa only [Option.elim_none, A.edge_count, columnSum] using sum_extraColumn A.inside
    | some w => exact A.columns w
  rows v := by
    rw [Fintype.sum_option]
    dsimp only [Option.elim_none, Option.elim_some]
    have hrow := A.rows v
    rw [degree_eq_extra_add_offset, A.edge_count] at hrow
    omega

def internalOfAugmented {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (he : e ≤ 3) (A : AugmentedMatrix W e d c) :
    {G : SimpleGraph (Fin 3) // internalEdgeCount G = e} :=
  (fixedEdgeEncodingEquiv e he).symm
    ⟨fun v => A.matrix v none, (fun v => A.binary v none), A.columns none⟩

theorem extraColumn_internalOfAugmented {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (he : e ≤ 3) (A : AugmentedMatrix W e d c) :
    extraColumn (internalOfAugmented he A).val = fun v => A.matrix v none := by
  exact congrArg Subtype.val ((fixedEdgeEncodingEquiv e he).apply_symm_apply
    ⟨fun v => A.matrix v none, (fun v => A.binary v none), A.columns none⟩)

def decodeMatrix {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (he : e ≤ 3) (hd : ∀ v, rowOffset e ≤ d v)
    (A : AugmentedMatrix W e d c) : TripleCell W e d c where
  outside v w := A.matrix v (some w)
  inside := (internalOfAugmented he A).val
  edge_count := (internalOfAugmented he A).property
  binary v w := A.binary v (some w)
  columns w := A.columns (some w)
  rows v := by
    rw [degree_eq_extra_add_offset, (internalOfAugmented he A).property,
      extraColumn_internalOfAugmented]
    have hrow := A.rows v
    rw [Fintype.sum_option] at hrow
    dsimp
    have hmargin := hd v
    omega

@[simp] theorem decode_encode {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (he : e ≤ 3) (hd : ∀ v, rowOffset e ≤ d v) (A : TripleCell W e d c) :
    decodeMatrix he hd (encodeCell A) = A := by
  apply TripleCell.ext
  · rfl
  · apply encoded_graph_injective
    apply Prod.ext
    · exact (internalOfAugmented he (encodeCell A)).property.trans A.edge_count.symm
    · exact extraColumn_internalOfAugmented he (encodeCell A)

@[simp] theorem encode_decode {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (he : e ≤ 3) (hd : ∀ v, rowOffset e ≤ d v) (A : AugmentedMatrix W e d c) :
    encodeCell (decodeMatrix he hd A) = A := by
  apply AugmentedMatrix.ext
  funext v w
  cases w with
  | none => exact congrFun (extraColumn_internalOfAugmented he A) v
  | some w => rfl

def tripleMatrixEquiv (e : ℕ) (he : e ≤ 3) (d : Fin 3 → ℕ) (c : W → ℕ)
    (hd : ∀ v, rowOffset e ≤ d v) :
    TripleCell W e d c ≃ AugmentedMatrix W e d c where
  toFun := encodeCell
  invFun := decodeMatrix he hd
  left_inv := decode_encode he hd
  right_inv := encode_decode he hd

theorem rowOffset_le_of_nonempty {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (h : Nonempty (TripleCell W e d c)) : ∀ v, rowOffset e ≤ d v := by
  obtain ⟨A⟩ := h
  intro v
  have hrow := A.rows v
  rw [degree_eq_extra_add_offset, A.edge_count] at hrow
  omega

theorem extraColumn_eq_margin_sub_row {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (A : TripleCell W e d c) (v : Fin 3) :
    extraColumn A.inside v = d v - rowOffset e - ∑ w, A.outside v w := by
  have hrow := A.rows v
  rw [degree_eq_extra_add_offset, A.edge_count] at hrow
  omega

theorem encode_row_eq_iff {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (A B : TripleCell W e d c) (v : Fin 3) :
    (encodeCell A).matrix v = (encodeCell B).matrix v ↔ A.outside v = B.outside v := by
  constructor
  · intro h
    funext w
    exact congrFun h (some w)
  · intro h
    funext w
    cases w with
    | none =>
        change extraColumn A.inside v = extraColumn B.inside v
        rw [extraColumn_eq_margin_sub_row, extraColumn_eq_margin_sub_row, h]
    | some w => exact congrFun h w

end Problem315.TripleInternalEncoding

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/TripleMatrixEncoding.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/TripleGraphEncoding.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315.TripleInternalEncoding
attribute [local instance] Classical.propDecidable

variable {W : Type*} [Fintype W]

def adjacencyBit {V : Type*} (G : SimpleGraph V) (u v : V) : ℕ :=
  if G.Adj u v then 1 else 0

def leftDegree (G : SimpleGraph (Fin 3 ⊕ W)) (v : Fin 3) : ℕ :=
  ∑ w, adjacencyBit G (Sum.inl v) w

def crossColumn (G : SimpleGraph (Fin 3 ⊕ W)) (w : W) : ℕ :=
  ∑ v : Fin 3, adjacencyBit G (Sum.inl v) (Sum.inr w)

def internalGraph (G : SimpleGraph (Fin 3 ⊕ W)) : SimpleGraph (Fin 3) :=
  G.comap Sum.inl

def outsideGraph (G : SimpleGraph (Fin 3 ⊕ W)) : SimpleGraph W :=
  G.comap Sum.inr

theorem leftDegree_eq_degree (G : SimpleGraph (Fin 3 ⊕ W)) (v : Fin 3) :
    leftDegree G v = G.degree (Sum.inl v) := by
  simpa only [leftDegree, adjacencyBit, Nat.cast_id] using
    (G.degree_eq_sum_if_adj (R := ℕ) (Sum.inl v)).symm

theorem leftDegree_decompose (G : SimpleGraph (Fin 3 ⊕ W)) (v : Fin 3) :
    leftDegree G v = graphDegree (internalGraph G) v +
      ∑ w, adjacencyBit G (Sum.inl v) (Sum.inr w) := by
  simp only [leftDegree, Fintype.sum_sum_type, graphDegree, Finset.card_eq_sum_ones,
    Finset.sum_filter, internalGraph, SimpleGraph.comap_adj, adjacencyBit]

abbrev GraphTripleCell (O : SimpleGraph W) (e : ℕ) (d : Fin 3 → ℕ) (c : W → ℕ) :=
  {G : SimpleGraph (Fin 3 ⊕ W) // outsideGraph G = O ∧
    internalEdgeCount (internalGraph G) = e ∧
    (∀ v, leftDegree G v = d v) ∧ ∀ w, crossColumn G w = c w}

variable {O : SimpleGraph W} {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}

def graphToCell (G : GraphTripleCell O e d c) : TripleCell W e d c where
  outside v w := adjacencyBit G.val (Sum.inl v) (Sum.inr w)
  inside := internalGraph G.val
  edge_count := G.property.2.1
  binary v w := by unfold adjacencyBit; split <;> omega
  columns w := G.property.2.2.2 w
  rows v := by
    have h := G.property.2.2.1 v
    rw [leftDegree_decompose] at h
    omega

def assembleGraph (O : SimpleGraph W) (A : TripleCell W e d c) :
    SimpleGraph (Fin 3 ⊕ W) where
  Adj x y := match x, y with
    | Sum.inl v, Sum.inl u => A.inside.Adj v u
    | Sum.inl v, Sum.inr w => A.outside v w = 1
    | Sum.inr w, Sum.inl v => A.outside v w = 1
    | Sum.inr w, Sum.inr z => O.Adj w z
  symm := by
    constructor
    intro x y h
    cases x with
    | inl v =>
        cases y with
        | inl u => exact A.inside.symm.symm v u h
        | inr w => exact h
    | inr w =>
        cases y with
        | inl v => exact h
        | inr z => exact O.symm.symm w z h
  loopless := by
    constructor
    intro x h
    cases x with
    | inl v => exact A.inside.loopless.irrefl v h
    | inr w => exact O.loopless.irrefl w h

@[simp] theorem internalGraph_assemble (O : SimpleGraph W) (A : TripleCell W e d c) :
    internalGraph (assembleGraph O A) = A.inside := by
  ext v u
  rfl

@[simp] theorem outsideGraph_assemble (O : SimpleGraph W) (A : TripleCell W e d c) :
    outsideGraph (assembleGraph O A) = O := by
  ext w z
  rfl

@[simp] theorem adjacencyBit_assemble_cross (O : SimpleGraph W)
    (A : TripleCell W e d c) (v : Fin 3) (w : W) :
    adjacencyBit (assembleGraph O A) (Sum.inl v) (Sum.inr w) = A.outside v w := by
  unfold adjacencyBit
  have h := A.binary v w
  split_ifs with hedge
  · exact (show A.outside v w = 1 from hedge).symm
  · have hne : A.outside v w ≠ 1 := hedge
    omega

def cellToGraph (O : SimpleGraph W) (A : TripleCell W e d c) :
    GraphTripleCell O e d c :=
  ⟨assembleGraph O A, outsideGraph_assemble O A, by
    rw [internalGraph_assemble]; exact A.edge_count, by
    intro v
    rw [leftDegree_decompose, internalGraph_assemble]
    simp only [adjacencyBit_assemble_cross]
    have h := A.rows v
    omega, by
    intro w
    simpa only [crossColumn, adjacencyBit_assemble_cross] using A.columns w⟩

@[simp] theorem graphToCell_cellToGraph (O : SimpleGraph W) (A : TripleCell W e d c) :
    graphToCell (cellToGraph O A) = A := by
  apply TripleCell.ext
  · funext v w
    exact adjacencyBit_assemble_cross O A v w
  · exact internalGraph_assemble O A

@[simp] theorem cellToGraph_graphToCell (G : GraphTripleCell O e d c) :
    cellToGraph O (graphToCell G) = G := by
  apply Subtype.ext
  ext x y
  cases x with
  | inl v =>
      cases y with
      | inl u => rfl
      | inr w => simp [cellToGraph, assembleGraph, graphToCell, adjacencyBit]
  | inr w =>
      cases y with
      | inl v =>
          simpa [cellToGraph, assembleGraph, graphToCell, adjacencyBit] using
            G.val.adj_comm (Sum.inl v) (Sum.inr w)
      | inr z =>
          change O.Adj w z ↔ G.val.Adj (Sum.inr w) (Sum.inr z)
          exact Iff.of_eq (congrArg (fun K : SimpleGraph W => K.Adj w z) G.property.1).symm

def graphTripleCellEquiv (O : SimpleGraph W) (e : ℕ) (d : Fin 3 → ℕ) (c : W → ℕ) :
    GraphTripleCell O e d c ≃ TripleCell W e d c where
  toFun := graphToCell
  invFun := cellToGraph O
  left_inv := cellToGraph_graphToCell
  right_inv := graphToCell_cellToGraph O

def graphTripleMatrixEquiv (O : SimpleGraph W) (e : ℕ) (he : e ≤ 3)
    (d : Fin 3 → ℕ) (c : W → ℕ) (hd : ∀ v, rowOffset e ≤ d v) :
    GraphTripleCell O e d c ≃ AugmentedMatrix W e d c :=
  (graphTripleCellEquiv O e d c).trans (tripleMatrixEquiv e he d c hd)

end Problem315.TripleInternalEncoding

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/TripleGraphEncoding.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/OrthogonalPairResampling.lean -/
section

namespace OAI

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace Problem315
namespace PairResampling

attribute [local instance] Classical.propDecidable

abbrev StateSpace (n : ℕ) (d : Fin n → ℕ) := EuclideanSpace ℝ (GraphState n d)

def fiberSpace (n : ℕ) (d : Fin n → ℕ) (a : Finset (Fin n)) :
    Submodule ℝ (StateSpace n d) where
  carrier := {f | ∀ G H : GraphState n d, SameFiber a G.val H.val → f G = f H}
  zero_mem' := by intro G H h; rfl
  add_mem' := by
    intro f g hf hg G H h
    change f G + g G = f H + g H
    rw [hf G H h, hg G H h]
  smul_mem' := by
    intro c f hf G H h
    change c * f G = c * f H
    rw [hf G H h]

def expectation (n : ℕ) (d : Fin n → ℕ) (a : Finset (Fin n)) :
    StateSpace n d →L[ℝ] StateSpace n d := (fiberSpace n d a).starProjection

def fluctuation (n : ℕ) (d : Fin n → ℕ) (a : Finset (Fin n)) :
    StateSpace n d →L[ℝ] StateSpace n d := (fiberSpace n d a)ᗮ.starProjection

variable {n : ℕ} {d : Fin n → ℕ} (a : Finset (Fin n))

@[simp] theorem expectation_mem (f : StateSpace n d) :
    expectation n d a f ∈ fiberSpace n d a :=
  (fiberSpace n d a).starProjection_apply_mem f

@[simp] theorem expectation_eq_self_iff (f : StateSpace n d) :
    expectation n d a f = f ↔ f ∈ fiberSpace n d a :=
  (fiberSpace n d a).starProjection_eq_self_iff

theorem expectation_isSymmetric :
    (expectation n d a).toLinearMap.IsSymmetric :=
  (fiberSpace n d a).starProjection_isSymmetric

theorem fluctuation_isSymmetric :
    (fluctuation n d a).toLinearMap.IsSymmetric :=
  (fiberSpace n d a)ᗮ.starProjection_isSymmetric

@[simp] theorem expectation_idempotent (f : StateSpace n d) :
    expectation n d a (expectation n d a f) = expectation n d a f :=
  (expectation_eq_self_iff a _).mpr (expectation_mem a f)

@[simp] theorem fluctuation_idempotent (f : StateSpace n d) :
    fluctuation n d a (fluctuation n d a f) = fluctuation n d a f :=
  (Submodule.starProjection_eq_self_iff).mpr
    ((fiberSpace n d a)ᗮ.starProjection_apply_mem f)

theorem fluctuation_eq_sub (f : StateSpace n d) :
    fluctuation n d a f = f - expectation n d a f := by
  exact (fiberSpace n d a).starProjection_orthogonal_val f

@[simp] theorem fluctuation_eq_zero_iff (f : StateSpace n d) :
    fluctuation n d a f = 0 ↔ f ∈ fiberSpace n d a := by
  rw [fluctuation_eq_sub, sub_eq_zero, eq_comm, expectation_eq_self_iff]

theorem inner_fluctuation (f : StateSpace n d) :
    ⟪f, fluctuation n d a f⟫ = ‖fluctuation n d a f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  have h := ((fluctuation_isSymmetric a) f (fluctuation n d a f)).symm
  change ⟪f, fluctuation n d a (fluctuation n d a f)⟫ =
    ⟪fluctuation n d a f, fluctuation n d a f⟫ at h
  simpa only [fluctuation_idempotent] using h

theorem fluctuation_nonneg (f : StateSpace n d) :
    0 ≤ ⟪f, fluctuation n d a f⟫ := by
  rw [inner_fluctuation]
  exact sq_nonneg _

def generator (n : ℕ) (d : Fin n → ℕ) : StateSpace n d →L[ℝ] StateSpace n d :=
  ∑ a ∈ pairs n, fluctuation n d a

theorem generator_apply (f : StateSpace n d) :
    generator n d f = ∑ a ∈ pairs n, fluctuation n d a f := by
  simp [generator]

theorem generator_isSymmetric : (generator n d).toLinearMap.IsSymmetric := by
  intro f g
  change ⟪generator n d f, g⟫ = ⟪f, generator n d g⟫
  simp only [generator_apply, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro b hb
  exact fluctuation_isSymmetric b f g

theorem inner_generator (f : StateSpace n d) :
    ⟪f, generator n d f⟫ = ∑ a ∈ pairs n, ‖fluctuation n d a f‖ ^ 2 := by
  simp only [generator_apply, inner_sum, inner_fluctuation]

theorem generator_nonneg (f : StateSpace n d) : 0 ≤ ⟪f, generator n d f⟫ := by
  rw [inner_generator]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem generator_eq_zero_iff (f : StateSpace n d) :
    generator n d f = 0 ↔ ∀ a ∈ pairs n, f ∈ fiberSpace n d a := by
  constructor
  · intro h a ha
    have hz : (∑ b ∈ pairs n, ‖fluctuation n d b f‖ ^ 2) = 0 := by
      rw [← inner_generator, h, inner_zero_right]
    have hterm : ‖fluctuation n d a f‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => sq_nonneg ‖fluctuation n d b f‖)).mp hz a ha
    exact (fluctuation_eq_zero_iff a f).mp
      (norm_eq_zero.mp (sq_eq_zero_iff.mp hterm))
  · intro h
    rw [generator_apply]
    apply Finset.sum_eq_zero
    intro a ha
    exact (fluctuation_eq_zero_iff a f).mpr (h a ha)

theorem state_inner (f g : StateSpace n d) :
    ⟪f, g⟫ = ∑ G : GraphState n d, f G * g G := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

theorem constant_mem (c : ℝ) :
    WithLp.toLp 2 (fun _ : GraphState n d => c) ∈ fiberSpace n d a := by
  intro G H h
  rfl

@[simp] theorem generator_constant (c : ℝ) :
    generator n d (WithLp.toLp 2 (fun _ : GraphState n d => c)) = 0 := by
  apply (generator_eq_zero_iff _).mpr
  intro a ha
  exact constant_mem a c

def fiberIndicator (a : Finset (Fin n)) (G : GraphState n d) : StateSpace n d :=
  WithLp.toLp 2 (fun H => if SameFiber a G.val H.val then 1 else 0)

theorem fiberIndicator_mem (G : GraphState n d) :
    fiberIndicator a G ∈ fiberSpace n d a := by
  intro H K hHK
  change (if SameFiber a G.val H.val then (1 : ℝ) else 0) =
    if SameFiber a G.val K.val then 1 else 0
  have hi : SameFiber a G.val H.val ↔ SameFiber a G.val K.val :=
    ⟨fun h => h.trans hHK, fun h => h.trans hHK.symm⟩
  simp only [hi]

theorem expectation_eq_average (f : StateSpace n d) (G : GraphState n d) :
    expectation n d a f G = (∑ H ∈ fiberStates a G, f H) / (fiberStates a G).card := by
  have horth := Submodule.starProjection_inner_eq_zero (K := fiberSpace n d a)
    f (fiberIndicator a G) (fiberIndicator_mem a G)
  change ⟪f - expectation n d a f, fiberIndicator a G⟫ = 0 at horth
  rw [state_inner] at horth
  have hsum : (∑ H ∈ fiberStates a G, (f H - expectation n d a f H)) = 0 := by
    calc
      _ = ∑ H : GraphState n d, (f - expectation n d a f) H * fiberIndicator a G H := by
        unfold fiberStates
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro H hH
        by_cases h : SameFiber a G.val H.val <;> simp [fiberIndicator, h]
      _ = 0 := horth
  have hequal : ∀ H ∈ fiberStates a G, expectation n d a f H = expectation n d a f G := by
    intro H hH
    exact (expectation_mem a f) H G ((mem_fiberStates a G H).mp hH).symm
  have hsconst : (∑ H ∈ fiberStates a G, expectation n d a f H) =
      (fiberStates a G).card * expectation n d a f G := by
    calc
      _ = ∑ _H ∈ fiberStates a G, expectation n d a f G := Finset.sum_congr rfl hequal
      _ = _ := by simp
  rw [Finset.sum_sub_distrib, hsconst] at hsum
  have hcard : (0 : ℝ) < (fiberStates a G).card := by
    exact_mod_cast Finset.card_pos.mpr (fiberStates_nonempty a G)
  apply (eq_div_iff (ne_of_gt hcard)).mpr
  linarith

end PairResampling
end Problem315

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/OrthogonalPairResampling.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/TriplePairFiber.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315.TripleInternalEncoding
attribute [local instance] Classical.propDecidable

theorem complement_edges_eq (G H : SimpleGraph (Fin 3)) (i : Fin 3)
    (he : internalEdgeCount G = internalEdgeCount H)
    (hd : graphDegree G i = graphDegree H i) :
    ∀ u v, u ≠ i → v ≠ i → (G.Adj u v ↔ H.Adj u v) := by
  unfold internalEdgeCount at he
  fin_cases i
  · change graphDegree G 0 = graphDegree H 0 at hd
    rw [degree_zero, degree_zero] at hd
    have h12 : G.Adj 1 2 ↔ H.Adj 1 2 := (edgeBit_eq_iff G H 1 2).mp (by omega)
    have h21 : G.Adj 2 1 ↔ H.Adj 2 1 :=
      (G.adj_comm 2 1).trans (h12.trans (H.adj_comm 1 2))
    intro u v hu hv
    fin_cases u <;> fin_cases v <;> simp_all
  · change graphDegree G 1 = graphDegree H 1 at hd
    rw [degree_one, degree_one] at hd
    have h02 : G.Adj 0 2 ↔ H.Adj 0 2 := (edgeBit_eq_iff G H 0 2).mp (by omega)
    have h20 : G.Adj 2 0 ↔ H.Adj 2 0 :=
      (G.adj_comm 2 0).trans (h02.trans (H.adj_comm 0 2))
    intro u v hu hv
    fin_cases u <;> fin_cases v <;> simp_all
  · change graphDegree G 2 = graphDegree H 2 at hd
    rw [degree_two, degree_two] at hd
    have h01 : G.Adj 0 1 ↔ H.Adj 0 1 := (edgeBit_eq_iff G H 0 1).mp (by omega)
    have h10 : G.Adj 1 0 ↔ H.Adj 1 0 :=
      (G.adj_comm 1 0).trans (h01.trans (H.adj_comm 0 1))
    intro u v hu hv
    fin_cases u <;> fin_cases v <;> simp_all

variable {W : Type*} [Fintype W]

def complementaryPair (i : Fin 3) : Finset (Fin 3 ⊕ W) := by
  classical
  exact (Finset.univ.image Sum.inl).erase (Sum.inl i)

omit [Fintype W] in
@[simp] theorem inl_mem_complementaryPair (i v : Fin 3) :
    (Sum.inl v : Fin 3 ⊕ W) ∈ complementaryPair i ↔ v ≠ i := by
  classical
  simp [complementaryPair]

omit [Fintype W] in
@[simp] theorem inr_notMem_complementaryPair (i : Fin 3) (w : W) :
    (Sum.inr w : Fin 3 ⊕ W) ∉ complementaryPair i := by
  classical
  simp [complementaryPair]

def SamePairRestrictions {V : Type*} (a : Finset V) (G H : SimpleGraph V) : Prop :=
  (∀ u ∉ a, ∀ v ∉ a, G.Adj u v ↔ H.Adj u v) ∧
  (∀ u ∈ a, ∀ v ∈ a, G.Adj u v ↔ H.Adj u v)

variable {O : SimpleGraph W} {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}

theorem adjacencyBit_eq_one {V : Type*} (G : SimpleGraph V) (u v : V) :
    adjacencyBit G u v = 1 ↔ G.Adj u v := by simp [adjacencyBit]

theorem samePairRestrictions_iff_row (G H : GraphTripleCell O e d c) (i : Fin 3) :
    SamePairRestrictions (complementaryPair i) G.val H.val ↔
      (graphToCell G).outside i = (graphToCell H).outside i := by
  classical
  constructor
  · intro h
    funext w
    have ha := h.1 (Sum.inl i) (by simp) (Sum.inr w) (by simp)
    simp only [graphToCell, adjacencyBit, ha]
  · intro hrow
    have hcross (w : W) : G.val.Adj (Sum.inl i) (Sum.inr w) ↔
        H.val.Adj (Sum.inl i) (Sum.inr w) := by
      have hb := congrFun hrow w
      exact (adjacencyBit_eq_one G.val _ _).symm.trans
        ((iff_of_eq (congrArg (fun x : ℕ => x = 1) hb)).trans
          (adjacencyBit_eq_one H.val _ _))
    have houtside (w z : W) : G.val.Adj (Sum.inr w) (Sum.inr z) ↔
        H.val.Adj (Sum.inr w) (Sum.inr z) := by
      have heq : outsideGraph G.val = outsideGraph H.val :=
        G.property.1.trans H.property.1.symm
      exact Iff.of_eq (congrArg (fun K : SimpleGraph W => K.Adj w z) heq)
    have hdegree : graphDegree (internalGraph G.val) i =
        graphDegree (internalGraph H.val) i := by
      have hG := (graphToCell G).rows i
      have hH := (graphToCell H).rows i
      rw [hrow] at hG
      exact Nat.add_left_cancel (hG.trans hH.symm)
    have hcomp := complement_edges_eq (internalGraph G.val) (internalGraph H.val) i
      (G.property.2.1.trans H.property.2.1.symm) hdegree
    constructor
    · intro u hu v hv
      cases u with
      | inl j =>
          have hji : j = i := by simpa using hu
          subst j
          cases v with
          | inl k =>
              have hki : k = i := by simpa using hv
              subst k
              simp
          | inr w => exact hcross w
      | inr w =>
          cases v with
          | inl j =>
              have hji : j = i := by simpa using hv
              subst j
              exact (G.val.adj_comm _ _).trans ((hcross w).trans (H.val.adj_comm _ _))
          | inr z => exact houtside w z
    · intro u hu v hv
      cases u with
      | inl j =>
          have hji : j ≠ i := by simpa using hu
          cases v with
          | inl k => exact hcomp j k hji (by simpa using hv)
          | inr w => simp at hv
      | inr w => simp at hu

theorem rightDegree_eq (G : GraphTripleCell O e d c) (w : W) :
    G.val.degree (Sum.inr w) = c w + O.degree w := by
  have hsum := G.val.degree_eq_sum_if_adj (R := ℕ) (Sum.inr w)
  simp only [Nat.cast_id, Fintype.sum_sum_type] at hsum
  rw [hsum]
  have hleft : (∑ v : Fin 3, if G.val.Adj (Sum.inr w) (Sum.inl v) then 1 else 0) =
      crossColumn G.val w := by
    unfold crossColumn adjacencyBit
    apply Finset.sum_congr rfl
    intro v hv
    rw [G.val.adj_comm (Sum.inr w) (Sum.inl v)]
  have hright : (∑ z : W, if G.val.Adj (Sum.inr w) (Sum.inr z) then 1 else 0) =
      O.degree w := by
    have ho := O.degree_eq_sum_if_adj (R := ℕ) w
    simp only [Nat.cast_id] at ho
    rw [ho]
    apply Finset.sum_congr rfl
    intro z hz
    have ha : G.val.Adj (Sum.inr w) (Sum.inr z) ↔ O.Adj w z :=
      Iff.of_eq (congrArg (fun K : SimpleGraph W => K.Adj w z) G.property.1)
    simp only [ha]
  rw [hleft, hright, G.property.2.2.2]

theorem graphCell_degrees_eq (G H : GraphTripleCell O e d c) :
    ∀ v, G.val.degree v = H.val.degree v := by
  intro v
  cases v with
  | inl i =>
      rw [← leftDegree_eq_degree, ← leftDegree_eq_degree]
      exact (G.property.2.2.1 i).trans (H.property.2.2.1 i).symm
  | inr w => rw [rightDegree_eq, rightDegree_eq]

def SamePairData {V : Type*} (a : Finset V) (G H : SimpleGraph V) : Prop :=
  (∀ u ∉ a, ∀ v ∉ a, G.Adj u v ↔ H.Adj u v) ∧
  (∀ u ∈ a, ∀ v ∈ a, G.Adj u v ↔ H.Adj u v) ∧
  (∀ w ∉ a, (a.filter (G.Adj w)).card = (a.filter (H.Adj w)).card)

theorem samePairData_iff_restrictions {V : Type*} [Fintype V]
    (a : Finset V) (G H : SimpleGraph V)
    (hdeg : ∀ w, G.degree w = H.degree w) :
    SamePairData a G H ↔ SamePairRestrictions a G H := by
  classical
  constructor
  · intro h
    exact ⟨h.1, h.2.1⟩
  · rintro ⟨hout, hin⟩
    refine ⟨hout, hin, ?_⟩
    intro w hw
    have hsplit (K : SimpleGraph V) :
        K.degree w = (a.filter (K.Adj w)).card +
          ((Finset.univ.filter (K.Adj w)).filter (fun v => v ∉ a)).card := by
      have h := (Finset.univ.filter (K.Adj w)).card_filter_add_card_filter_not
        (fun v => v ∈ a)
      have hinset : (Finset.univ.filter (K.Adj w)).filter (fun v => v ∈ a) =
          a.filter (K.Adj w) := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
      rw [hinset] at h
      have hcard : (Finset.univ.filter (K.Adj w)).card = K.degree w := by
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
        exact (K.degree_eq_sum_if_adj (R := ℕ) w).symm
      rw [hcard] at h
      exact h.symm
    have hs : ((Finset.univ.filter (G.Adj w)).filter (fun v => v ∉ a)) =
        ((Finset.univ.filter (H.Adj w)).filter (fun v => v ∉ a)) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hG, hv⟩
        exact ⟨(hout w hw v hv).mp hG, hv⟩
      · rintro ⟨hH, hv⟩
        exact ⟨(hout w hw v hv).mpr hH, hv⟩
    have h := hdeg w
    rw [hsplit G, hsplit H, hs] at h
    exact Nat.add_right_cancel h

theorem samePairData_iff_row (G H : GraphTripleCell O e d c) (i : Fin 3) :
    SamePairData (complementaryPair i) G.val H.val ↔
      (graphToCell G).outside i = (graphToCell H).outside i := by
  rw [samePairData_iff_restrictions _ _ _ (graphCell_degrees_eq G H),
    samePairRestrictions_iff_row]

theorem samePairData_iff_sameFiber {n : ℕ} (a : Finset (Fin n))
    (G H : SimpleGraph (Fin n)) :
    SamePairData a G H ↔ PairResampling.SameFiber a G H := Iff.rfl

theorem samePairData_iff_augmentedRow (G H : GraphTripleCell O e d c) (i : Fin 3) :
    SamePairData (complementaryPair i) G.val H.val ↔
      (encodeCell (graphToCell G)).matrix i = (encodeCell (graphToCell H)).matrix i := by
  exact (samePairData_iff_row G H i).trans
    (encode_row_eq_iff (graphToCell G) (graphToCell H) i).symm

theorem rightDegree_decompose (G : SimpleGraph (Fin 3 ⊕ W)) (w : W) :
    G.degree (Sum.inr w) = crossColumn G w + (outsideGraph G).degree w := by
  let A : GraphTripleCell (outsideGraph G) (internalEdgeCount (internalGraph G))
      (leftDegree G) (crossColumn G) := ⟨G, rfl, rfl, (fun _ => rfl), (fun _ => rfl)⟩
  exact rightDegree_eq A w

theorem edgeCount_eq_of_complement (G H : SimpleGraph (Fin 3)) (i : Fin 3)
    (hd : graphDegree G i = graphDegree H i)
    (ho : ∀ u v, u ≠ i → v ≠ i → (G.Adj u v ↔ H.Adj u v)) :
    internalEdgeCount G = internalEdgeCount H := by
  unfold internalEdgeCount
  fin_cases i
  · change graphDegree G 0 = graphDegree H 0 at hd
    rw [degree_zero, degree_zero] at hd
    have hb := (edgeBit_eq_iff G H 1 2).mpr (ho 1 2 (by decide) (by decide))
    omega
  · change graphDegree G 1 = graphDegree H 1 at hd
    rw [degree_one, degree_one] at hd
    have hb := (edgeBit_eq_iff G H 0 2).mpr (ho 0 2 (by decide) (by decide))
    omega
  · change graphDegree G 2 = graphDegree H 2 at hd
    rw [degree_two, degree_two] at hd
    have hb := (edgeBit_eq_iff G H 0 1).mpr (ho 0 1 (by decide) (by decide))
    omega

theorem cell_preserved_by_pair_data (G : GraphTripleCell O e d c)
    (H : SimpleGraph (Fin 3 ⊕ W)) (i : Fin 3)
    (hdeg : ∀ v, G.val.degree v = H.degree v)
    (hf : SamePairData (complementaryPair i) G.val H) :
    outsideGraph H = O ∧ internalEdgeCount (internalGraph H) = e ∧
      (∀ v, leftDegree H v = d v) ∧ ∀ w, crossColumn H w = c w := by
  classical
  have hout : outsideGraph G.val = outsideGraph H := by
    ext w z
    exact hf.1 (Sum.inr w) (by simp) (Sum.inr z) (by simp)
  have hrow : (fun w : W => adjacencyBit G.val (Sum.inl i) (Sum.inr w)) =
      (fun w : W => adjacencyBit H (Sum.inl i) (Sum.inr w)) := by
    funext w
    have ha := hf.1 (Sum.inl i) (by simp) (Sum.inr w) (by simp)
    simp only [adjacencyBit, ha]
  have hleft : ∀ v, leftDegree G.val v = leftDegree H v := by
    intro v
    rw [leftDegree_eq_degree, leftDegree_eq_degree]
    exact hdeg (Sum.inl v)
  have hdinternal : graphDegree (internalGraph G.val) i =
      graphDegree (internalGraph H) i := by
    have h := hleft i
    rw [leftDegree_decompose, leftDegree_decompose, hrow] at h
    exact Nat.add_right_cancel h
  have hecount : internalEdgeCount (internalGraph G.val) =
      internalEdgeCount (internalGraph H) := by
    apply edgeCount_eq_of_complement _ _ i hdinternal
    intro u v hu hv
    exact hf.2.1 (Sum.inl u) (by simpa using hu) (Sum.inl v) (by simpa using hv)
  refine ⟨hout.symm.trans G.property.1, hecount.symm.trans G.property.2.1, ?_, ?_⟩
  · intro v
    exact (hleft v).symm.trans (G.property.2.2.1 v)
  · intro w
    have h := hdeg (Sum.inr w)
    rw [rightDegree_decompose, rightDegree_decompose, hout] at h
    exact (Nat.add_right_cancel h).symm.trans (G.property.2.2.2 w)

end Problem315.TripleInternalEncoding

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/TriplePairFiber.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/TripleCellTransport.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.TripleCellTransport

open TripleStateReindex TripleInternalEncoding
attribute [local instance] Classical.propDecidable

theorem degreeCount_eq_degree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) : degreeCount G v = G.degree v := by
  classical
  simp only [degreeCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact (G.degree_eq_sum_if_adj (R := ℕ) v).symm

variable {n : ℕ} {d : Fin n → ℕ}
variable (T : Finset (Fin n)) (hT : T.card = 3)

def splitGraph (G : GraphState n d) : SimpleGraph (Fin 3 ⊕ Outside T) :=
  G.val.comap (splitEquiv T hT)

theorem splitGraph_degree (G : GraphState n d) (v : Fin 3 ⊕ Outside T) :
    (splitGraph T hT G).degree v = d (splitEquiv T hT v) := by
  rw [← degreeCount_eq_degree]
  change degreeCount (G.val.comap (splitEquiv T hT)) v = _
  rw [degreeCount_comap]
  exact G.property _

abbrev Cell (G : GraphState n d) :=
  {H : GraphState n d //
    outsideGraph (splitGraph T hT H) = outsideGraph (splitGraph T hT G) ∧
    internalEdgeCount (internalGraph (splitGraph T hT H)) =
      internalEdgeCount (internalGraph (splitGraph T hT G)) ∧
    ∀ w, crossColumn (splitGraph T hT H) w = crossColumn (splitGraph T hT G) w}

abbrev Model (G : GraphState n d) :=
  GraphTripleCell (outsideGraph (splitGraph T hT G))
    (internalEdgeCount (internalGraph (splitGraph T hT G)))
    (leftDegree (splitGraph T hT G)) (crossColumn (splitGraph T hT G))

def referenceModel (G : GraphState n d) : Model T hT G :=
  ⟨splitGraph T hT G, rfl, rfl, (fun _ => rfl), (fun _ => rfl)⟩

def toModel (G : GraphState n d) (H : Cell T hT G) : Model T hT G :=
  ⟨splitGraph T hT H.val, H.property.1, H.property.2.1, by
    intro v
    rw [leftDegree_eq_degree, leftDegree_eq_degree, splitGraph_degree,
      splitGraph_degree], H.property.2.2⟩

def modelState (G : GraphState n d) (H : Model T hT G) : GraphState n d :=
  (stateEquiv T hT d).symm ⟨H.val, by
    intro v
    rw [degreeCount_eq_degree,
      graphCell_degrees_eq H (referenceModel T hT G) v]
    exact splitGraph_degree T hT G v⟩

@[simp] theorem splitGraph_modelState (G : GraphState n d) (H : Model T hT G) :
    splitGraph T hT (modelState T hT G H) = H.val := by
  change ((stateEquiv T hT d) ((stateEquiv T hT d).symm _)).val = H.val
  simp only [Equiv.apply_symm_apply]

def fromModel (G : GraphState n d) (H : Model T hT G) : Cell T hT G :=
  ⟨modelState T hT G H, by
    rw [splitGraph_modelState]
    exact ⟨H.property.1, H.property.2.1, H.property.2.2.2⟩⟩

def cellEquiv (G : GraphState n d) : Cell T hT G ≃ Model T hT G where
  toFun := toModel T hT G
  invFun := fromModel T hT G
  left_inv H := by
    apply Subtype.ext
    apply (stateEquiv T hT d).injective
    apply Subtype.ext
    exact splitGraph_modelState T hT G (toModel T hT G H)
  right_inv H := by
    apply Subtype.ext
    exact splitGraph_modelState T hT G H

def referenceCell (G : GraphState n d) : Cell T hT G :=
  ⟨G, rfl, rfl, fun _ => rfl⟩

def matrixEquiv (G : GraphState n d) : Cell T hT G ≃
    AugmentedMatrix (Outside T)
      (internalEdgeCount (internalGraph (splitGraph T hT G)))
      (leftDegree (splitGraph T hT G)) (crossColumn (splitGraph T hT G)) :=
  (cellEquiv T hT G).trans (graphTripleMatrixEquiv _ _
    (internalEdgeCount_le_three _) _ _
    (rowOffset_le_of_nonempty ⟨graphToCell (referenceModel T hT G)⟩))

def pair (i : Fin 3) : Finset (Fin n) :=
  (complementaryPair (W := Outside T) i).map (splitEquiv T hT).toEmbedding

@[simp] theorem split_mem_pair (i : Fin 3) (v : Fin 3 ⊕ Outside T) :
    splitEquiv T hT v ∈ pair T hT i ↔ v ∈ complementaryPair i := by
  classical
  simp [pair]

theorem pair_eq_erase (i : Fin 3) :
    pair T hT i = T.erase (splitEquiv T hT (Sum.inl i)) := by
  classical
  ext v
  obtain ⟨x, rfl⟩ := (splitEquiv T hT).surjective v
  rw [split_mem_pair]
  cases x with
  | inl j =>
      simp only [inl_mem_complementaryPair, Finset.mem_erase,
        splitEquiv_inl_mem, and_true]
      constructor
      · intro h heq
        exact h (Sum.inl.inj ((splitEquiv T hT).injective heq))
      · intro h heq
        exact h (congrArg (fun j => splitEquiv T hT (Sum.inl j)) heq)
  | inr w =>
      simp only [inr_notMem_complementaryPair, Finset.mem_erase,
        splitEquiv_inr_not_mem, and_false]

theorem restrictions_map_iff {V W : Type*} (e : V ≃ W) (a : Finset V)
    (G H : SimpleGraph W) :
    SamePairRestrictions (a.map e.toEmbedding) G H ↔
      SamePairRestrictions a (G.comap e) (H.comap e) := by
  classical
  constructor
  · rintro ⟨hout, hin⟩
    constructor
    · intro u hu v hv
      exact hout (e u) (by simpa using hu) (e v) (by simpa using hv)
    · intro u hu v hv
      exact hin (e u) (by simpa using hu) (e v) (by simpa using hv)
  · rintro ⟨hout, hin⟩
    constructor
    · intro u hu v hv
      obtain ⟨x, rfl⟩ := e.surjective u
      obtain ⟨y, rfl⟩ := e.surjective v
      exact hout x (by simpa using hu) y (by simpa using hv)
    · intro u hu v hv
      obtain ⟨x, rfl⟩ := e.surjective u
      obtain ⟨y, rfl⟩ := e.surjective v
      exact hin x (by simpa using hu) y (by simpa using hv)

theorem sameFiber_iff_splitPairData (G H : GraphState n d) (i : Fin 3) :
    PairResampling.SameFiber (pair T hT i) G.val H.val ↔
      SamePairData (complementaryPair i) (splitGraph T hT G) (splitGraph T hT H) := by
  rw [PairResampling.sameFiber_state_iff]
  rw [samePairData_iff_restrictions _ _ _ (by
    intro v
    rw [splitGraph_degree, splitGraph_degree])]
  exact restrictions_map_iff (splitEquiv T hT) _ G.val H.val

theorem cell_of_sameFiber (G H : GraphState n d) (i : Fin 3)
    (hf : PairResampling.SameFiber (pair T hT i) G.val H.val) :
    outsideGraph (splitGraph T hT H) = outsideGraph (splitGraph T hT G) ∧
    internalEdgeCount (internalGraph (splitGraph T hT H)) =
      internalEdgeCount (internalGraph (splitGraph T hT G)) ∧
    ∀ w, crossColumn (splitGraph T hT H) w = crossColumn (splitGraph T hT G) w := by
  have h := cell_preserved_by_pair_data (referenceModel T hT G)
    (splitGraph T hT H) i (by
      intro v
      exact (splitGraph_degree T hT G v).trans (splitGraph_degree T hT H v).symm)
    ((sameFiber_iff_splitPairData T hT G H i).mp hf)
  exact ⟨h.1, h.2.1, h.2.2.2⟩

theorem sameFiber_iff_matrixRow (G : GraphState n d)
    (H K : Cell T hT G) (i : Fin 3) :
    PairResampling.SameFiber (pair T hT i) H.val.val K.val.val ↔
      (matrixEquiv T hT G H).matrix i = (matrixEquiv T hT G K).matrix i := by
  rw [sameFiber_iff_splitPairData]
  exact samePairData_iff_augmentedRow (toModel T hT G H) (toModel T hT G K) i

theorem cell_of_sameFiber_of_cell (G : GraphState n d) (H : Cell T hT G)
    (K : GraphState n d) (i : Fin 3)
    (hf : PairResampling.SameFiber (pair T hT i) H.val.val K.val) :
    outsideGraph (splitGraph T hT K) = outsideGraph (splitGraph T hT G) ∧
    internalEdgeCount (internalGraph (splitGraph T hT K)) =
      internalEdgeCount (internalGraph (splitGraph T hT G)) ∧
    ∀ w, crossColumn (splitGraph T hT K) w = crossColumn (splitGraph T hT G) w := by
  have h := cell_of_sameFiber T hT H.val K i hf
  exact ⟨h.1.trans H.property.1, h.2.1.trans H.property.2.1,
    fun w => (h.2.2 w).trans (H.property.2.2 w)⟩

theorem pair_card (i : Fin 3) : (pair T hT i).card = 2 := by
  rw [pair_eq_erase, Finset.card_erase_of_mem (splitEquiv_inl_mem T hT i), hT]

theorem pair_mem_powersetCard (i : Fin 3) : pair T hT i ∈ T.powersetCard 2 := by
  rw [Finset.mem_powersetCard]
  exact ⟨by rw [pair_eq_erase]; exact Finset.erase_subset _ _, pair_card T hT i⟩

theorem pair_injective : Function.Injective (pair T hT) := by
  intro i j heq
  by_contra hij
  have hi : splitEquiv T hT (Sum.inl i) ∈ pair T hT j := by
    rw [split_mem_pair]
    exact (inl_mem_complementaryPair j i).mpr hij
  rw [← heq, split_mem_pair] at hi
  simp at hi

def pairEquiv : Fin 3 ≃ T.powersetCard 2 := by
  let f : Fin 3 → T.powersetCard 2 := fun i => ⟨pair T hT i, pair_mem_powersetCard T hT i⟩
  apply Equiv.ofBijective f
  have hinj : Function.Injective f := by
    intro i j h
    exact pair_injective T hT (congrArg Subtype.val h)
  refine ⟨hinj, ?_⟩
  have hc : Fintype.card (Fin 3) = Fintype.card (T.powersetCard 2) := by
    rw [Fintype.card_coe, Finset.card_powersetCard, hT]
    rfl
  exact (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hc⟩ |>.2

theorem sum_pair {E : Type*} [AddCommMonoid E] (f : Finset (Fin n) → E) :
    ∑ i : Fin 3, f (pair T hT i) = ∑ a ∈ T.powersetCard 2, f a := by
  change (∑ i : Fin 3, (fun a : T.powersetCard 2 => f a.val) (pairEquiv T hT i)) = _
  exact ((pairEquiv T hT).sum_comp (fun a => f a.val)).trans
    (Finset.sum_coe_sort _ _)

theorem sum_leftDegree_decompose {W : Type*} [Fintype W]
    (G : SimpleGraph (Fin 3 ⊕ W)) :
    (∑ i, leftDegree G i) = 2 * internalEdgeCount (internalGraph G) +
      ∑ w, crossColumn G w := by
  simp_rw [leftDegree_decompose]
  rw [Finset.sum_add_distrib, sum_degrees, Finset.sum_comm]
  rfl

theorem cellData_iff_outsideGraph (G H : GraphState n d) :
    (outsideGraph (splitGraph T hT H) = outsideGraph (splitGraph T hT G) ∧
      internalEdgeCount (internalGraph (splitGraph T hT H)) =
        internalEdgeCount (internalGraph (splitGraph T hT G)) ∧
      ∀ w, crossColumn (splitGraph T hT H) w = crossColumn (splitGraph T hT G) w) ↔
    outsideGraph (splitGraph T hT H) = outsideGraph (splitGraph T hT G) := by
  refine ⟨And.left, fun ho => ?_⟩
  have hc : ∀ w, crossColumn (splitGraph T hT H) w =
      crossColumn (splitGraph T hT G) w := by
    intro w
    have hd := (splitGraph_degree T hT H (Sum.inr w)).trans
      (splitGraph_degree T hT G (Sum.inr w)).symm
    rw [rightDegree_decompose, rightDegree_decompose, ho] at hd
    exact Nat.add_right_cancel hd
  have hl : ∀ i, leftDegree (splitGraph T hT H) i =
      leftDegree (splitGraph T hT G) i := by
    intro i
    rw [leftDegree_eq_degree, leftDegree_eq_degree,
      splitGraph_degree, splitGraph_degree]
  have hs : (∑ i, leftDegree (splitGraph T hT H) i) =
      ∑ i, leftDegree (splitGraph T hT G) i := Finset.sum_congr rfl (fun i _ => hl i)
  rw [sum_leftDegree_decompose, sum_leftDegree_decompose] at hs
  simp_rw [hc] at hs
  exact ⟨ho, by omega, hc⟩

theorem outsideGraph_eq_iff (G H : GraphState n d) :
    outsideGraph (splitGraph T hT H) = outsideGraph (splitGraph T hT G) ↔
      ∀ u ∉ T, ∀ v ∉ T, H.val.Adj u v ↔ G.val.Adj u v := by
  constructor
  · intro h u hu v hv
    exact Iff.of_eq (congrArg (fun K : SimpleGraph (Outside T) =>
      K.Adj ⟨u, hu⟩ ⟨v, hv⟩) h)
  · intro h
    ext u v
    exact h u.val u.property v.val v.property

def outsideCellEquiv (G : GraphState n d) :
    {H : GraphState n d //
      outsideGraph (splitGraph T hT H) = outsideGraph (splitGraph T hT G)} ≃
      Cell T hT G where
  toFun H := ⟨H.val, (cellData_iff_outsideGraph T hT G H.val).mpr H.property⟩
  invFun H := ⟨H.val, H.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Problem315.TripleCellTransport

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/TripleCellTransport.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/FixedBlockPartitions.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.FixedBlock

variable {α : Type*} [Fintype α] [sectionDecidableEqα : DecidableEq α]

def row (c : α → Fin 3) (i : Fin 3) : Finset α :=
  Finset.univ.filter (fun a => c a = i)

include sectionDecidableEqα in
@[simp] lemma mem_row (c : α → Fin 3) (i : Fin 3) (a : α) :
    a ∈ row c i ↔ c a = i := by
  have retainedsectionDecidableEqα := sectionDecidableEqα
  simp [row]

lemma row_relabel (σ : Equiv.Perm α) (c : α → Fin 3) (i : Fin 3) :
    row (fun a => c (σ.symm a)) i = (row c i).map σ.toEmbedding := by
  ext a
  simp []

abbrev Partition (sizes : Fin 3 → ℕ) :=
  {c : α → Fin 3 // ∀ i, (row c i).card = sizes i}

def relabel {sizes : Fin 3 → ℕ} (σ : Equiv.Perm α) (c : Partition (α := α) sizes) :
    Partition (α := α) sizes :=
  ⟨fun a => c.val (σ.symm a), by
    intro i
    rw [row_relabel, Finset.card_map]
    exact c.property i⟩

@[simp] lemma relabel_val {sizes : Fin 3 → ℕ} (σ : Equiv.Perm α)
    (c : Partition (α := α) sizes) (a : α) :
    (relabel σ c).val a = c.val (σ.symm a) := rfl

@[simp] lemma relabel_one {sizes : Fin 3 → ℕ} (c : Partition (α := α) sizes) :
    relabel 1 c = c := by apply Subtype.ext; rfl

lemma relabel_mul {sizes : Fin 3 → ℕ} (σ τ : Equiv.Perm α)
    (c : Partition (α := α) sizes) :
    relabel (σ * τ) c = relabel σ (relabel τ c) := by
  apply Subtype.ext
  rfl

lemma row_swap_unchanged (c : α → Fin 3) (a b : α) (i : Fin 3)
    (hai : c a ≠ i) (hbi : c b ≠ i) :
    row (fun x => c ((Equiv.swap a b).symm x)) i = row c i := by
  ext x
  simp only [mem_row, Equiv.symm_swap]
  by_cases hxa : x = a
  · subst x
    simp [hai, hbi]
  · by_cases hxb : x = b
    · subst x
      simp [hai, hbi]
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

lemma exists_unused_color (a b : Fin 3) : ∃ i : Fin 3, i ≠ a ∧ i ≠ b := by
  fin_cases a <;> fin_cases b <;> decide

lemma three_sum_sq_le_twice (f : Fin 3 → ℝ) (i : Fin 3) (hi : f i = 0) :
    (∑ j, f j) ^ 2 ≤ 2 * ∑ j, (f j) ^ 2 := by
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  fin_cases i
  · change f 0 = 0 at hi
    rw [hi]
    nlinarith [sq_nonneg (f 1 - f 2)]
  · change f 1 = 0 at hi
    rw [hi]
    nlinarith [sq_nonneg (f 0 - f 2)]
  · change f 2 = 0 at hi
    rw [hi]
    nlinarith [sq_nonneg (f 0 - f 1)]

lemma row_transposition_energy (c : α → Fin 3) (a b : α)
    (g : Fin 3 → Finset α → ℝ) :
    (∑ i, (g i (row c i) -
      g i (row (fun x => c ((Equiv.swap a b).symm x)) i))) ^ 2 ≤
    2 * ∑ i, (g i (row c i) -
      g i (row (fun x => c ((Equiv.swap a b).symm x)) i)) ^ 2 := by
  obtain ⟨i, hia, hib⟩ := exists_unused_color (c a) (c b)
  apply three_sum_sq_le_twice _ i
  rw [row_swap_unchanged c a b i (Ne.symm hia) (Ne.symm hib)]
  ring

lemma exists_relabel {sizes : Fin 3 → ℕ}
    (c d : Partition (α := α) sizes) :
    ∃ σ : Equiv.Perm α, relabel σ c = d := by
  classical
  have hcard (i : Fin 3) :
      Fintype.card {a : α // c.val a = i} = Fintype.card {a : α // d.val a = i} := by
    simpa [Fintype.card_subtype, row] using (c.property i).trans (d.property i).symm
  let e (i : Fin 3) : {a : α // c.val a = i} ≃ {a : α // d.val a = i} :=
    Fintype.equivOfCardEq (hcard i)
  let σ : Equiv.Perm α := Equiv.ofFiberEquiv e
  refine ⟨σ, Subtype.ext ?_⟩
  funext a
  have h := Equiv.ofFiberEquiv_map e (σ.symm a)
  change d.val (σ (σ.symm a)) = c.val (σ.symm a) at h
  change c.val (σ.symm a) = d.val a
  simpa only [Equiv.apply_symm_apply] using h.symm

lemma eq_of_swap_invariant {sizes : Fin 3 → ℕ}
    (f : Partition (α := α) sizes → ℝ)
    (hf : ∀ a b c, f (relabel (Equiv.swap a b) c) = f c)
    (c d : Partition (α := α) sizes) : f c = f d := by
  obtain ⟨σ, hσ⟩ := exists_relabel c d
  have hperm (σ : Equiv.Perm α) : ∀ c, f (relabel σ c) = f c := by
    induction σ using Equiv.Perm.swap_induction_on with
    | one => intro c; simp
    | swap_mul σ a b hab ih =>
      intro c
      rw [relabel_mul, hf, ih]
  rw [← hσ, hperm]

end Problem315.FixedBlock

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/FixedBlockPartitions.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/BinaryColumnPartitions.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.BinaryColumnPartitions

abbrev Column (q : ℕ) := {c : Fin 3 → Fin 2 // ∑ i, (c i : ℕ) = q}

def unitColumn (i : Fin 3) : Column 1 :=
  ⟨fun j => if j = i then 1 else 0, by
    simp only [Fin.sum_univ_three]
    fin_cases i <;> decide⟩

def complementColumn (c : Fin 3 → Fin 2) : Fin 3 → Fin 2 :=
  fun i => if c i = 0 then 1 else 0

lemma column_one_surjective : Function.Surjective unitColumn := by
  decide

lemma column_one_injective : Function.Injective unitColumn := by
  decide

noncomputable def oneColumnEquiv : Fin 3 ≃ Column 1 :=
  Equiv.ofBijective unitColumn ⟨column_one_injective, column_one_surjective⟩

noncomputable def complementEquiv : Column 1 ≃ Column 2 where
  toFun c := ⟨complementColumn c.val, by
    have h : ∀ c : Column 1, ∑ i, (complementColumn c.val i : ℕ) = 2 := by decide
    exact h c⟩
  invFun c := ⟨complementColumn c.val, by
    have h : ∀ c : Column 2, ∑ i, (complementColumn c.val i : ℕ) = 1 := by decide
    exact h c⟩
  left_inv := by decide
  right_inv := by decide

def twoColumnEquiv : Fin 3 ≃ Column 2 := oneColumnEquiv.trans complementEquiv

variable (U W : Type*)

abbrev MatrixSpace :=
  {M : Fin 3 → U ⊕ W → Fin 2 //
    (∀ u, ∑ i, (M i (Sum.inl u) : ℕ) = 1) ∧
    (∀ w, ∑ i, (M i (Sum.inr w) : ℕ) = 2)}

def matrixEquiv : ((U → Fin 3) × (W → Fin 3)) ≃ MatrixSpace U W where
  toFun c := ⟨fun i j => Sum.elim
    (fun u => (oneColumnEquiv (c.1 u)).val i)
    (fun w => (twoColumnEquiv (c.2 w)).val i) j,
    ⟨fun u => (oneColumnEquiv (c.1 u)).property,
     fun w => (twoColumnEquiv (c.2 w)).property⟩⟩
  invFun M :=
    (fun u => oneColumnEquiv.symm ⟨fun i => M.val i (Sum.inl u), M.property.1 u⟩,
     fun w => twoColumnEquiv.symm ⟨fun i => M.val i (Sum.inr w), M.property.2 w⟩)
  left_inv c := by
    apply Prod.ext
    · funext u
      exact oneColumnEquiv.symm_apply_apply (c.1 u)
    · funext w
      exact twoColumnEquiv.symm_apply_apply (c.2 w)
  right_inv M := by
    apply Subtype.ext
    funext i j
    cases j with
    | inl u =>
      exact congrArg (fun c : Column 1 => c.val i)
        (oneColumnEquiv.apply_symm_apply ⟨fun k => M.val k (Sum.inl u), M.property.1 u⟩)
    | inr w =>
      exact congrArg (fun c : Column 2 => c.val i)
        (twoColumnEquiv.apply_symm_apply ⟨fun k => M.val k (Sum.inr w), M.property.2 w⟩)

@[simp] theorem matrixEquiv_inl (c : (U → Fin 3) × (W → Fin 3)) (i : Fin 3) (u : U) :
    (matrixEquiv U W c).val i (Sum.inl u) = if i = c.1 u then 1 else 0 := rfl

@[simp] theorem matrixEquiv_inr (c : (U → Fin 3) × (W → Fin 3)) (i : Fin 3) (w : W) :
    (matrixEquiv U W c).val i (Sum.inr w) = if i = c.2 w then 0 else 1 := by
  change (if (if i = c.2 w then (1 : Fin 2) else 0) = 0 then 1 else 0) = _
  split_ifs <;> simp_all

variable [Fintype U] [Fintype W]

theorem row_sum_add (c : (U → Fin 3) × (W → Fin 3)) (i : Fin 3) :
    (∑ j, ((matrixEquiv U W c).val i j : ℕ)) + (FixedBlock.row c.2 i).card =
      (FixedBlock.row c.1 i).card + Fintype.card W := by
  classical
  have hU : (∑ u : U, ((matrixEquiv U W c).val i (Sum.inl u) : ℕ)) =
      (FixedBlock.row c.1 i).card := by
    have hu (u : U) : ((matrixEquiv U W c).val i (Sum.inl u) : ℕ) =
        if c.1 u = i then 1 else 0 := by
      rw [matrixEquiv_inl]
      by_cases h : i = c.1 u
      · simp [h]
      · simp [h, Ne.symm h]
    simp_rw [hu]
    simp [FixedBlock.row]
  have hW : (∑ w : W, ((matrixEquiv U W c).val i (Sum.inr w) : ℕ)) +
      (FixedBlock.row c.2 i).card = Fintype.card W := by
    have hh (w : W) : ((matrixEquiv U W c).val i (Sum.inr w) : ℕ) +
        (if c.2 w = i then 1 else 0) = 1 := by
      rw [matrixEquiv_inr]
      by_cases h : i = c.2 w
      · simp [h]
      · simp [h, Ne.symm h]
    have hs := congrArg (fun f : W → ℕ => ∑ w, f w) (funext hh)
    simpa [Finset.sum_add_distrib, FixedBlock.row] using hs
  rw [Fintype.sum_sum_type, hU]
  omega

def fixedMarginsEquiv (r : Fin 3 → ℕ) :
    {c : (U → Fin 3) × (W → Fin 3) // ∀ i,
      (FixedBlock.row c.1 i).card + Fintype.card W = r i + (FixedBlock.row c.2 i).card} ≃
    {M : MatrixSpace U W // ∀ i, ∑ j, (M.val i j : ℕ) = r i} :=
  (matrixEquiv U W).subtypeEquiv (fun c => by
    constructor
    · intro h i
      have hh := row_sum_add U W c i
      have hi := h i
      omega
    · intro h i
      have hh := row_sum_add U W c i
      rw [h i] at hh
      exact hh.symm)

theorem row_eq_iff (c d : (U → Fin 3) × (W → Fin 3)) (i : Fin 3) :
    (matrixEquiv U W c).val i = (matrixEquiv U W d).val i ↔
      FixedBlock.row c.1 i = FixedBlock.row d.1 i ∧
      FixedBlock.row c.2 i = FixedBlock.row d.2 i := by
  classical
  have h1 : ∀ a b i : Fin 3,
      (if i = a then (1 : Fin 2) else 0) = (if i = b then 1 else 0) ↔
        (a = i ↔ b = i) := by decide
  have h2 : ∀ a b i : Fin 3,
      (if i = a then (0 : Fin 2) else 1) = (if i = b then 0 else 1) ↔
        (a = i ↔ b = i) := by decide
  constructor
  · intro h
    constructor
    · ext u
      have he := congrFun h (Sum.inl u)
      simpa only [FixedBlock.mem_row, matrixEquiv_inl, h1] using he
    · ext w
      have he := congrFun h (Sum.inr w)
      simpa only [FixedBlock.mem_row, matrixEquiv_inr, h2] using he
  · rintro ⟨hu, hw⟩
    funext j
    cases j with
    | inl u =>
      rw [matrixEquiv_inl, matrixEquiv_inl, h1]
      simpa only [FixedBlock.mem_row] using (Finset.ext_iff.mp hu u)
    | inr w =>
      rw [matrixEquiv_inr, matrixEquiv_inr, h2]
      simpa only [FixedBlock.mem_row] using (Finset.ext_iff.mp hw w)

end Problem315.BinaryColumnPartitions

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/BinaryColumnPartitions.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/ForcedColumns.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.ForcedColumns

variable {C : Type*}

abbrev MatrixSpace (k : C → ℕ) :=
  {M : Fin 3 → C → Fin 2 // ∀ c, ∑ i, (M i c : ℕ) = k c}

abbrev One (k : C → ℕ) := {c : C // k c = 1}
abbrev Two (k : C → ℕ) := {c : C // k c = 2}

lemma column_zero (v : Fin 3 → Fin 2) (h : ∑ i, (v i : ℕ) = 0) :
    ∀ i, v i = 0 := by
  have ht : ∀ v : Fin 3 → Fin 2, (∑ i, (v i : ℕ)) = 0 → ∀ i, v i = 0 := by decide
  exact ht v h

lemma column_three (v : Fin 3 → Fin 2) (h : ∑ i, (v i : ℕ) = 3) :
    ∀ i, v i = 1 := by
  have ht : ∀ v : Fin 3 → Fin 2, (∑ i, (v i : ℕ)) = 3 → ∀ i, v i = 1 := by decide
  exact ht v h

def restrict (k : C → ℕ) (M : MatrixSpace k) :
    BinaryColumnPartitions.MatrixSpace (One k) (Two k) :=
  ⟨fun i => Sum.elim (fun c => M.val i c.val) (fun c => M.val i c.val),
    ⟨fun c => (M.property c.val).trans c.property,
     fun c => (M.property c.val).trans c.property⟩⟩

def extend (k : C → ℕ) (hk : ∀ c, k c ≤ 3)
    (M : BinaryColumnPartitions.MatrixSpace (One k) (Two k)) : MatrixSpace k := by
  classical
  refine ⟨fun i c => if h1 : k c = 1 then M.val i (Sum.inl ⟨c, h1⟩)
    else if h2 : k c = 2 then M.val i (Sum.inr ⟨c, h2⟩)
    else if k c = 3 then 1 else 0, ?_⟩
  intro c
  by_cases h1 : k c = 1
  · simpa [h1] using M.property.1 ⟨c, h1⟩
  · by_cases h2 : k c = 2
    · simpa [h2] using M.property.2 ⟨c, h2⟩
    · by_cases h3 : k c = 3
      · simp [h3]
      · have h0 : k c = 0 := by have := hk c; omega
        simp [h0]

@[simp] theorem restrict_extend (k : C → ℕ) (hk : ∀ c, k c ≤ 3)
    (M : BinaryColumnPartitions.MatrixSpace (One k) (Two k)) :
    restrict k (extend k hk M) = M := by
  classical
  apply Subtype.ext
  funext i c
  cases c with
  | inl c => simp [restrict, extend, c.property]
  | inr c => simp [restrict, extend, c.property]

@[simp] theorem extend_restrict (k : C → ℕ) (hk : ∀ c, k c ≤ 3)
    (M : MatrixSpace k) : extend k hk (restrict k M) = M := by
  classical
  apply Subtype.ext
  funext i c
  by_cases h1 : k c = 1
  · simp [extend, restrict, h1]
  · by_cases h2 : k c = 2
    · simp [extend, restrict, h2]
    · by_cases h3 : k c = 3
      · have he : M.val i c = 1 := column_three (fun j => M.val j c)
          ((M.property c).trans h3) i
        simp [extend, h3, he]
      · have h0 : k c = 0 := by have := hk c; omega
        have he : M.val i c = 0 := column_zero (fun j => M.val j c)
          ((M.property c).trans h0) i
        simp [extend, h0, he]

def matrixEquiv (k : C → ℕ) (hk : ∀ c, k c ≤ 3) :
    MatrixSpace k ≃ BinaryColumnPartitions.MatrixSpace (One k) (Two k) where
  toFun := restrict k
  invFun := extend k hk
  left_inv := extend_restrict k hk
  right_inv := restrict_extend k hk

theorem row_eq_iff (k : C → ℕ) (hk : ∀ c, k c ≤ 3)
    (M N : MatrixSpace k) (i : Fin 3) :
    (restrict k M).val i = (restrict k N).val i ↔ M.val i = N.val i := by
  constructor
  · intro h
    funext c
    by_cases h1 : k c = 1
    · exact congrFun h (Sum.inl ⟨c, h1⟩)
    · by_cases h2 : k c = 2
      · exact congrFun h (Sum.inr ⟨c, h2⟩)
      · by_cases h3 : k c = 3
        · exact (column_three _ ((M.property c).trans h3) i).trans
            (column_three _ ((N.property c).trans h3) i).symm
        · have h0 : k c = 0 := by have := hk c; omega
          exact (column_zero _ ((M.property c).trans h0) i).trans
            (column_zero _ ((N.property c).trans h0) i).symm
  · intro h
    funext c
    cases c with
    | inl c => exact congrFun h c.val
    | inr c => exact congrFun h c.val

attribute [local instance] Classical.propDecidable
variable [Fintype C]

def offset (k : C → ℕ) : ℕ := Fintype.card {c : C // k c = 3}

theorem row_sum (k : C → ℕ) (hk : ∀ c, k c ≤ 3)
    (M : MatrixSpace k) (i : Fin 3) :
    (∑ c, (M.val i c : ℕ)) =
      (∑ c, ((restrict k M).val i c : ℕ)) + offset k := by
  classical
  have hs (a : ℕ) : (∑ c : {c : C // k c = a}, (M.val i c.val : ℕ)) =
      ∑ c : C, if k c = a then (M.val i c : ℕ) else 0 := by
    symm
    simpa only [Finset.sum_filter] using
      (Finset.sum_subtype (Finset.univ.filter (fun c => k c = a))
        (by intro c; simp) (fun c => (M.val i c : ℕ)))
  have hp (c : C) : (M.val i c : ℕ) =
      (if k c = 1 then (M.val i c : ℕ) else 0) +
      (if k c = 2 then (M.val i c : ℕ) else 0) +
      (if k c = 3 then 1 else 0) := by
    have hc : k c = 0 ∨ k c = 1 ∨ k c = 2 ∨ k c = 3 := by
      have := hk c
      omega
    rcases hc with h | h | h | h
    · have he := column_zero _ ((M.property c).trans h) i
      simp [h, he]
    · simp [h]
    · simp [h]
    · have he := column_three _ ((M.property c).trans h) i
      simp [h, he]
  have ht := congrArg (fun f : C → ℕ => ∑ c, f c) (funext hp)
  simp only [Finset.sum_add_distrib] at ht
  rw [Fintype.sum_sum_type]
  change (∑ c, (M.val i c : ℕ)) =
    ((∑ c : One k, (M.val i c.val : ℕ)) +
      ∑ c : Two k, (M.val i c.val : ℕ)) + offset k
  rw [hs 1, hs 2]
  have ho : (∑ c : C, if k c = 3 then 1 else 0) = offset k := by
    simp [offset, Fintype.card_subtype]
  simpa only [ho] using ht

theorem offset_le_row_sum (k : C → ℕ) (hk : ∀ c, k c ≤ 3)
    (M : MatrixSpace k) (i : Fin 3) : offset k ≤ ∑ c, (M.val i c : ℕ) := by
  rw [row_sum k hk M i]
  omega

def fixedMarginsEquiv (k : C → ℕ) (hk : ∀ c, k c ≤ 3)
    (r : Fin 3 → ℕ) (hr : ∀ i, offset k ≤ r i) :
    {M : MatrixSpace k // ∀ i, ∑ c, (M.val i c : ℕ) = r i} ≃
      {M : BinaryColumnPartitions.MatrixSpace (One k) (Two k) //
        ∀ i, ∑ c, (M.val i c : ℕ) = r i - offset k} :=
  (matrixEquiv k hk).subtypeEquiv (fun M => by
    constructor
    · intro h i
      have hh := row_sum k hk M i
      have hi := h i
      change (∑ c, ((restrict k M).val i c : ℕ)) = r i - offset k
      omega
    · intro h i
      have hh := row_sum k hk M i
      have hi := h i
      have hle := hr i
      change (∑ c, ((restrict k M).val i c : ℕ)) = r i - offset k at hi
      omega)

abbrev FullMargins (k : C → ℕ) (r : Fin 3 → ℕ) :=
  {M : Fin 3 → C → Fin 2 //
    (∀ i, ∑ c, (M i c : ℕ) = r i) ∧ ∀ c, ∑ i, (M i c : ℕ) = k c}

def nestEquiv (k : C → ℕ) (r : Fin 3 → ℕ) :
    FullMargins k r ≃ {M : MatrixSpace k // ∀ i, ∑ c, (M.val i c : ℕ) = r i} where
  toFun M := ⟨⟨M.val, M.property.2⟩, M.property.1⟩
  invFun M := ⟨M.val.val, M.property, M.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem bounds_of_nonempty (k : C → ℕ) (r : Fin 3 → ℕ)
    (h : Nonempty (FullMargins k r)) :
    (∀ c, k c ≤ 3) ∧ ∀ i, offset k ≤ r i := by
  obtain ⟨M⟩ := h
  have hk (c : C) : k c ≤ 3 := by
    rw [← M.property.2 c]
    calc
      (∑ i, (M.val i c : ℕ)) ≤ ∑ _i : Fin 3, 1 := by
        apply Finset.sum_le_sum
        intro i hi
        have := (M.val i c).isLt
        omega
      _ = 3 := by simp
  refine ⟨hk, ?_⟩
  intro i
  have hi := offset_le_row_sum k hk ⟨M.val, M.property.2⟩ i
  simpa only [M.property.1 i] using hi

abbrev Colorings (k : C → ℕ) (r : Fin 3 → ℕ) :=
  {c : (One k → Fin 3) × (Two k → Fin 3) // ∀ i,
    (FixedBlock.row c.1 i).card + Fintype.card (Two k) =
      (r i - offset k) + (FixedBlock.row c.2 i).card}

def coloringEquiv (k : C → ℕ) (r : Fin 3 → ℕ)
    (h : Nonempty (FullMargins k r)) : FullMargins k r ≃ Colorings k r :=
  (nestEquiv k r).trans
    ((fixedMarginsEquiv k (bounds_of_nonempty k r h).1 r
      (bounds_of_nonempty k r h).2).trans
      (BinaryColumnPartitions.fixedMarginsEquiv (One k) (Two k)
        (fun i => r i - offset k)).symm)

theorem coloring_row_eq_iff (k : C → ℕ) (r : Fin 3 → ℕ)
    (h : Nonempty (FullMargins k r)) (M N : FullMargins k r) (i : Fin 3) :
    M.val i = N.val i ↔
      FixedBlock.row (coloringEquiv k r h M).val.1 i =
        FixedBlock.row (coloringEquiv k r h N).val.1 i ∧
      FixedBlock.row (coloringEquiv k r h M).val.2 i =
        FixedBlock.row (coloringEquiv k r h N).val.2 i := by
  let m : MatrixSpace k := ⟨M.val, M.property.2⟩
  let n : MatrixSpace k := ⟨N.val, N.property.2⟩
  have hm : BinaryColumnPartitions.matrixEquiv (One k) (Two k)
      (coloringEquiv k r h M).val = restrict k m := by
    change BinaryColumnPartitions.matrixEquiv (One k) (Two k)
      ((BinaryColumnPartitions.matrixEquiv (One k) (Two k)).symm (restrict k m)) = _
    exact Equiv.apply_symm_apply _ _
  have hn : BinaryColumnPartitions.matrixEquiv (One k) (Two k)
      (coloringEquiv k r h N).val = restrict k n := by
    change BinaryColumnPartitions.matrixEquiv (One k) (Two k)
      ((BinaryColumnPartitions.matrixEquiv (One k) (Two k)).symm (restrict k n)) = _
    exact Equiv.apply_symm_apply _ _
  have hb := BinaryColumnPartitions.row_eq_iff (One k) (Two k)
    (coloringEquiv k r h M).val (coloringEquiv k r h N).val i
  rw [hm, hn] at hb
  exact (row_eq_iff k (bounds_of_nonempty k r h).1 m n i).symm.trans hb

end Problem315.ForcedColumns

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/ForcedColumns.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/TripleMatrixFinEquiv.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.TripleMatrixFinEquiv
open TripleInternalEncoding
attribute [local instance] Classical.propDecidable

variable {W : Type*} [Fintype W]

def margins (e : ℕ) (c : W → ℕ) : Option W → ℕ :=
  fun w => w.elim (columnSum e) c

def augmentedEquiv (e : ℕ) (d : Fin 3 → ℕ) (c : W → ℕ) :
    AugmentedMatrix W e d c ≃
      ForcedColumns.FullMargins (margins e c) (fun i => d i - rowOffset e) where
  toFun M := ⟨fun i w => ⟨M.matrix i w, by have := M.binary i w; omega⟩,
    M.rows, M.columns⟩
  invFun M :=
    { matrix := fun i w => (M.val i w : ℕ)
      binary := fun i w => by have := (M.val i w).isLt; omega
      columns := M.property.2
      rows := M.property.1 }
  left_inv M := by apply AugmentedMatrix.ext; rfl
  right_inv M := by apply Subtype.ext; rfl

@[simp] theorem augmentedEquiv_apply_val (e : ℕ) (d : Fin 3 → ℕ) (c : W → ℕ)
    (M : AugmentedMatrix W e d c) (i : Fin 3) (w : Option W) :
    ((augmentedEquiv e d c M).val i w : ℕ) = M.matrix i w := rfl

theorem augmented_row_eq_iff (e : ℕ) (d : Fin 3 → ℕ) (c : W → ℕ)
    (M N : AugmentedMatrix W e d c) (i : Fin 3) :
    (augmentedEquiv e d c M).val i = (augmentedEquiv e d c N).val i ↔
      M.matrix i = N.matrix i := by
  constructor
  · intro h
    funext w
    exact congrArg Fin.val (congrFun h w)
  · intro h
    funext w
    apply Fin.ext
    exact congrFun h w

def graphEquiv (O : SimpleGraph W) (e : ℕ) (he : e ≤ 3)
    (d : Fin 3 → ℕ) (c : W → ℕ) (hd : ∀ i, rowOffset e ≤ d i) :
    GraphTripleCell O e d c ≃
      ForcedColumns.FullMargins (margins e c) (fun i => d i - rowOffset e) :=
  (graphTripleMatrixEquiv O e he d c hd).trans (augmentedEquiv e d c)

theorem graph_row_eq_iff (O : SimpleGraph W) (e : ℕ) (he : e ≤ 3)
    (d : Fin 3 → ℕ) (c : W → ℕ) (hd : ∀ i, rowOffset e ≤ d i)
    (G H : GraphTripleCell O e d c) (i : Fin 3) :
    (graphEquiv O e he d c hd G).val i = (graphEquiv O e he d c hd H).val i ↔
      (graphToCell G).outside i = (graphToCell H).outside i := by
  change (augmentedEquiv e d c (encodeCell (graphToCell G))).val i =
    (augmentedEquiv e d c (encodeCell (graphToCell H))).val i ↔ _
  rw [augmented_row_eq_iff, encode_row_eq_iff]

theorem bounds_of_nonempty (O : SimpleGraph W) (e : ℕ)
    (d : Fin 3 → ℕ) (c : W → ℕ) (h : Nonempty (GraphTripleCell O e d c)) :
    e ≤ 3 ∧ ∀ i, rowOffset e ≤ d i := by
  obtain ⟨G⟩ := h
  constructor
  · rw [← G.property.2.1]
    exact internalEdgeCount_le_three _
  · exact rowOffset_le_of_nonempty ⟨graphToCell G⟩

def graphEquivOfNonempty (O : SimpleGraph W) (e : ℕ)
    (d : Fin 3 → ℕ) (c : W → ℕ) (h : Nonempty (GraphTripleCell O e d c)) :
    GraphTripleCell O e d c ≃
      ForcedColumns.FullMargins (margins e c) (fun i => d i - rowOffset e) :=
  graphEquiv O e (bounds_of_nonempty O e d c h).1 d c
    (bounds_of_nonempty O e d c h).2

end Problem315.TripleMatrixFinEquiv

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/TripleMatrixFinEquiv.lean -/
