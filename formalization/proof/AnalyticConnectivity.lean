import AnalyticTripleProjection

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/HavelInduction.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.HavelCanonical

theorem exists_top_subset {V : Type*} [DecidableEq V]
    (R : Finset V) (weight : V → Nat) (k : Nat) (hk : k ≤ R.card) :
    ∃ T : Finset V, T ⊆ R ∧ T.card = k ∧
      ∀ i ∈ R, i ∉ T → ∀ j ∈ T, weight i ≤ weight j := by
  classical
  obtain ⟨T₀, hT₀R, hT₀k⟩ := Finset.exists_subset_card_eq hk
  have hne : (R.powersetCard k).Nonempty :=
    ⟨T₀, Finset.mem_powersetCard.mpr ⟨hT₀R, hT₀k⟩⟩
  obtain ⟨T, hT, hmax⟩ :=
    Finset.exists_max_image (R.powersetCard k) (fun S => ∑ x ∈ S, weight x) hne
  obtain ⟨hTR, hTk⟩ := Finset.mem_powersetCard.mp hT
  refine ⟨T, hTR, hTk, ?_⟩
  intro i hiR hiT j hjT
  let U := insert i (T.erase j)
  have hiE : i ∉ T.erase j := fun h => hiT (Finset.mem_of_mem_erase h)
  have hUR : U ⊆ R := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · simpa [h] using hiR
    · exact hTR (Finset.mem_of_mem_erase h)
  have hUk : U.card = k := by
    simp only [U, Finset.card_insert_of_notMem hiE, Finset.card_erase_of_mem hjT]
    have hjpos : 0 < T.card := Finset.card_pos.mpr ⟨j, hjT⟩
    omega
  have hbound := hmax U (Finset.mem_powersetCard.mpr ⟨hUR, hUk⟩)
  have hsum : (∑ x ∈ T.erase j, weight x) + weight j = ∑ x ∈ T, weight x :=
    Finset.sum_erase_add T weight hjT
  simp only [U, Finset.sum_insert hiE] at hbound
  omega

def AgreeOutside {V : Type*} (R : Finset V) (G H : SimpleGraph V) : Prop :=
  ∀ v, v ∉ R → ∀ w, G.Adj v w ↔ H.Adj v w

theorem residual_degree_eq {V : Type*} [Fintype V] [DecidableEq V]
    (R : Finset V) (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hout : AgreeOutside R G H) (hdegree : ∀ v, G.degree v = H.degree v) (v : V) :
    (R.filter (G.Adj v)).card = (R.filter (H.Adj v)).card := by
  classical
  have hin (K : SimpleGraph V) [DecidableRel K.Adj] :
      (K.neighborFinset v).filter (fun w => w ∈ R) = R.filter (K.Adj v) := by
    ext w
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    exact and_comm
  have hext : (G.neighborFinset v).filter (fun w => w ∉ R) =
      (H.neighborFinset v).filter (fun w => w ∉ R) := by
    ext w
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hvw, hwR⟩
      exact ⟨((hout w hwR v).mp hvw.symm).symm, hwR⟩
    · rintro ⟨hvw, hwR⟩
      exact ⟨((hout w hwR v).mpr hvw.symm).symm, hwR⟩
  have hG := (G.neighborFinset v).card_filter_add_card_filter_not (fun w => w ∈ R)
  have hH := (H.neighborFinset v).card_filter_add_card_filter_not (fun w => w ∈ R)
  rw [hin G, hext, SimpleGraph.card_neighborFinset_eq_degree] at hG
  rw [hin H, SimpleGraph.card_neighborFinset_eq_degree] at hH
  have hd := hdegree v
  omega

theorem agreeOutside_erase {V : Type*} [DecidableEq V]
    {R : Finset V} {G H : SimpleGraph V} {v : V}
    (hout : AgreeOutside R G H) (hrow : ∀ w, G.Adj v w ↔ H.Adj v w) :
    AgreeOutside (R.erase v) G H := by
  intro u hu w
  by_cases huv : u = v
  · simpa [huv] using hrow w
  · exact hout u (fun huR => hu (Finset.mem_erase.mpr ⟨huv, huR⟩)) w

theorem connected_of_row_alignment
    {V X : Type*} [Fintype V] [DecidableEq V]
    (graph : X → SimpleGraph V) (hinj : Function.Injective graph)
    (r : X → X → Prop) (hsymm : ∀ ⦃first second⦄, r first second → r second first)
    (halign : ∀ (R : Finset V) (v : V), v ∈ R → ∀ x y : X,
      AgreeOutside R (graph x) (graph y) →
      ∃ x' y' : X,
        Relation.ReflTransGen r x x' ∧ Relation.ReflTransGen r y y' ∧
        AgreeOutside R (graph x') (graph y') ∧
        ∀ w, (graph x').Adj v w ↔ (graph y').Adj v w)
    (x y : X) : Relation.ReflTransGen r x y := by
  classical
  have hreverse {a b : X} (h : Relation.ReflTransGen r a b) :
      Relation.ReflTransGen r b a := by
    induction h with
    | refl => exact .refl
    | tail hab hbc ih => exact (Relation.ReflTransGen.single (hsymm hbc)).trans ih
  have haux : ∀ R : Finset V, ∀ a b : X,
      AgreeOutside R (graph a) (graph b) → Relation.ReflTransGen r a b := by
    intro R
    induction R using Finset.induction_on with
    | empty =>
      intro a b hab
      have hgraphs : graph a = graph b := by
        apply SimpleGraph.ext
        funext v w
        exact propext (hab v (by simp) w)
      have heq := hinj hgraphs
      subst b
      exact .refl
    | @insert v R hv ih =>
      intro a b hab
      obtain ⟨a', b', haa', hbb', hout, hrow⟩ :=
        halign (insert v R) v (Finset.mem_insert_self v R) a b hab
      have hout' : AgreeOutside R (graph a') (graph b') := by
        simpa [Finset.erase_insert hv] using agreeOutside_erase hout hrow
      exact haa'.trans ((ih a' b' hout').trans (hreverse hbb'))
  exact haux Finset.univ x y (by intro v hv; exact False.elim (hv (Finset.mem_univ v)))

theorem connected_of_neighborhood_repair
    {V X : Type*} [Fintype V] [DecidableEq V]
    (graph : X → SimpleGraph V) [∀ x, DecidableRel (graph x).Adj]
    (hinj : Function.Injective graph) (r : X → X → Prop)
    (hsymm : ∀ ⦃first second⦄, r first second → r second first)
    (hdegree : ∀ x y v, (graph x).degree v = (graph y).degree v)
    (hrepair : ∀ (R T : Finset V) (v : V) (x : X),
      v ∈ R → T ⊆ R.erase v → T.card = (R.filter ((graph x).Adj v)).card →
      (∀ i ∈ R, i ≠ v → i ∉ T → ∀ j ∈ T,
        (R.filter ((graph x).Adj i)).card ≤ (R.filter ((graph x).Adj j)).card) →
      ∃ x' : X, Relation.ReflTransGen r x x' ∧
        AgreeOutside R (graph x) (graph x') ∧ R.filter ((graph x').Adj v) = T)
    (x y : X) : Relation.ReflTransGen r x y := by
  classical
  apply connected_of_row_alignment graph hinj r hsymm _ x y
  intro R v hv a b hab
  have hcard : (R.filter ((graph a).Adj v)).card ≤ (R.erase v).card := by
    apply Finset.card_le_card
    intro w hw
    obtain ⟨hwR, hvw⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_erase.mpr ⟨hvw.ne.symm, hwR⟩
  obtain ⟨T, hTR, hTcard, htop⟩ := exists_top_subset (R.erase v)
    (fun w => (R.filter ((graph a).Adj w)).card)
    (R.filter ((graph a).Adj v)).card hcard
  have hsortedA : ∀ i ∈ R, i ≠ v → i ∉ T → ∀ j ∈ T,
      (R.filter ((graph a).Adj i)).card ≤ (R.filter ((graph a).Adj j)).card := by
    intro i hiR hiv hiT j hjT
    exact htop i (Finset.mem_erase.mpr ⟨hiv, hiR⟩) hiT j hjT
  have hres : ∀ w, (R.filter ((graph a).Adj w)).card =
      (R.filter ((graph b).Adj w)).card :=
    residual_degree_eq R (graph a) (graph b) hab (hdegree a b)
  have hsizeB : T.card = (R.filter ((graph b).Adj v)).card :=
    hTcard.trans (hres v)
  have hsortedB : ∀ i ∈ R, i ≠ v → i ∉ T → ∀ j ∈ T,
      (R.filter ((graph b).Adj i)).card ≤ (R.filter ((graph b).Adj j)).card := by
    intro i hiR hiv hiT j hjT
    rw [← hres i, ← hres j]
    exact hsortedA i hiR hiv hiT j hjT
  obtain ⟨a', haa', houtA, hrowA⟩ := hrepair R T v a hv hTR hTcard hsortedA
  obtain ⟨b', hbb', houtB, hrowB⟩ := hrepair R T v b hv hTR hsizeB hsortedB
  have hout' : AgreeOutside R (graph a') (graph b') := by
    intro u hu w
    exact (houtA u hu w).symm.trans ((hab u hu w).trans (houtB u hu w))
  refine ⟨a', b', haa', hbb', hout', ?_⟩
  intro w
  by_cases hw : w ∈ R
  · have h := Finset.ext_iff.mp (hrowA.trans hrowB.symm) w
    simpa only [Finset.mem_filter, hw, true_and] using h
  · constructor
    · intro h
      exact ((hout' w hw v).mp h.symm).symm
    · intro h
      exact ((hout' w hw v).mpr h.symm).symm

end Problem315.HavelCanonical

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/HavelInduction.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SwitchFoundations.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315

def reverseProposal {n : Nat} (p : SwitchProposal n) : SwitchProposal n :=
  ⟨p.1, ⟨(p.2.val.2, p.2.val.1), Ne.symm p.2.property⟩⟩

@[simp] theorem removedMatching_reverse {n : Nat} (p : SwitchProposal n) :
    removedMatching (reverseProposal p) = addedMatching p := rfl

@[simp] theorem addedMatching_reverse {n : Nat} (p : SwitchProposal n) :
    addedMatching (reverseProposal p) = removedMatching p := rfl

@[simp] theorem reverseProposal_reverse {n : Nat} (p : SwitchProposal n) :
    reverseProposal (reverseProposal p) = p := by
  rcases p with ⟨S, ⟨⟨M, N⟩, h⟩⟩
  rfl

theorem validSwitch_matchings_disjoint {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (h : validSwitch G p) {u v : Fin n}
    (hm : (removedMatching p).Adj u v) : ¬ (addedMatching p).Adj u v := by
  intro hn
  exact h.2 hn (h.1 hm)

theorem validSwitch_reverse_replace {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (h : validSwitch G p) :
    validSwitch (replaceEdges G (removedMatching p) (addedMatching p))
      (reverseProposal p) := by
  constructor
  · intro u v hn
    exact Or.inr hn
  · intro u v hm he
    rcases he with he | hn
    · exact he.2 hm
    · exact validSwitch_matchings_disjoint h hm hn

theorem replaceEdges_reverse {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (h : validSwitch G p) :
    replaceEdges (replaceEdges G (removedMatching p) (addedMatching p))
      (addedMatching p) (removedMatching p) = G := by
  ext u v
  change (((G.Adj u v ∧ ¬ (removedMatching p).Adj u v) ∨
    (addedMatching p).Adj u v) ∧ ¬ (addedMatching p).Adj u v) ∨
    (removedMatching p).Adj u v ↔ G.Adj u v
  constructor
  · rintro (⟨hG | hN, hn⟩ | hm)
    · exact hG.1
    · exact False.elim (hn hN)
    · exact h.1 hm
  · intro hG
    by_cases hm : (removedMatching p).Adj u v
    · exact Or.inr hm
    · exact Or.inl ⟨Or.inl ⟨hG, hm⟩, fun hn => h.2 hn hG⟩

theorem proposalResult_of_valid {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (h : validSwitch G p) :
    proposalResult G p = replaceEdges G (removedMatching p) (addedMatching p) := by
  simp [proposalResult, h]

theorem proposalResult_reverse {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (h : validSwitch G p) :
    proposalResult (proposalResult G p) (reverseProposal p) = G := by
  rw [proposalResult_of_valid h,
    proposalResult_of_valid (validSwitch_reverse_replace h)]
  exact replaceEdges_reverse h

theorem validSwitch_of_result_ne {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (h : proposalResult G p ≠ G) : validSwitch G p := by
  classical
  by_contra hn
  exact h (by simp [proposalResult, hn])

theorem proposalResult_eq_reverse_of_ne {n : Nat} {G H : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (hne : G ≠ H) (h : proposalResult G p = H) :
    proposalResult H (reverseProposal p) = G := by
  have hv : validSwitch G p := validSwitch_of_result_ne (by
    rw [h]
    exact Ne.symm hne)
  rw [← h]
  exact proposalResult_reverse hv

theorem switchStep_symm {n : Nat} {d : Fin n → Nat}
    {G H : GraphState n d} (h : SwitchStep n d G H) : SwitchStep n d H G := by
  rcases h with ⟨p, hp, hresult⟩
  refine ⟨reverseProposal p, ?_, ?_⟩
  · rw [← hresult, proposalResult_of_valid hp]
    exact validSwitch_reverse_replace hp
  · rw [← hresult]
    exact proposalResult_reverse hp

theorem perfectMatching_degree {n : Nat} {S : FourSet n}
    (M : PerfectMatching S) (v : Fin n) :
    graphDegree M.val v = if v ∈ S.val then 1 else 0 := by
  classical
  by_cases hv : v ∈ S.val
  · obtain ⟨w, hw, hu⟩ := (M.property v).1 hv
    have hs : Finset.univ.filter (fun x => M.val.Adj v x) = {w} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun hx => hu x hx, fun hx => hx ▸ hw⟩
    simp [graphDegree, hs, hv]
  · have hs : Finset.univ.filter (fun x => M.val.Adj v x) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      exact (M.property v).2 hv x
    simp [graphDegree, hs, hv]

theorem matchings_degree_eq {n : Nat} (p : SwitchProposal n) (v : Fin n) :
    graphDegree (removedMatching p) v = graphDegree (addedMatching p) v := by
  exact (perfectMatching_degree p.2.val.1 v).trans
    (perfectMatching_degree p.2.val.2 v).symm

theorem replaceEdges_degree_add {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (h : validSwitch G p) (v : Fin n) :
    graphDegree (replaceEdges G (removedMatching p) (addedMatching p)) v +
      graphDegree (removedMatching p) v =
    graphDegree G v + graphDegree (addedMatching p) v := by
  classical
  simp only [graphDegree, Finset.card_eq_sum_ones, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hg : G.Adj v w <;>
    by_cases hm : (removedMatching p).Adj v w <;>
    by_cases hn : (addedMatching p).Adj v w
  all_goals simp_all [replaceEdges, h.1, h.2]

theorem proposalResult_degree {n : Nat} (G : SimpleGraph (Fin n))
    (p : SwitchProposal n) (v : Fin n) :
    graphDegree (proposalResult G p) v = graphDegree G v := by
  classical
  by_cases h : validSwitch G p
  · rw [proposalResult_of_valid h]
    have ha := replaceEdges_degree_add h v
    rw [matchings_degree_eq p v] at ha
    exact Nat.add_right_cancel ha
  · simp [proposalResult, h]

theorem proposalResult_realizes {n : Nat} {d : Fin n → Nat}
    {G : SimpleGraph (Fin n)} (hG : Realizes n d G) (p : SwitchProposal n) :
    Realizes n d (proposalResult G p) := by
  intro v
  rw [proposalResult_degree]
  exact hG v

theorem switchKernel_symm {n : Nat} {d : Fin n → Nat} (G H : GraphState n d) :
    switchKernel n d G H = switchKernel n d H G := by
  classical
  by_cases hGH : G = H
  · subst H
    rfl
  have hvGH : G.val ≠ H.val := fun h => hGH (Subtype.ext h)
  have hc : ((allProposals n).filter (fun p => proposalResult G.val p = H.val)).card =
      ((allProposals n).filter (fun p => proposalResult H.val p = G.val)).card := by
    apply Finset.card_bij (fun p _ => reverseProposal p)
    · intro p hp
      simp only [Finset.mem_filter, allProposals, Finset.mem_univ, true_and] at hp ⊢
      exact proposalResult_eq_reverse_of_ne hvGH hp
    · intro p hp q hq heq
      have heq' := congrArg reverseProposal heq
      simpa using heq'
    · intro p hp
      refine ⟨reverseProposal p, ?_, reverseProposal_reverse p⟩
      simp only [Finset.mem_filter, allProposals, Finset.mem_univ, true_and] at hp ⊢
      exact proposalResult_eq_reverse_of_ne (Ne.symm hvGH) hp
  simp only [switchKernel, hGH, Ne.symm hGH, ↓reduceIte, zero_add, hc]

theorem switchKernel_nonneg {n : Nat} {d : Fin n → Nat} (G H : GraphState n d) :
    0 ≤ switchKernel n d G H := by
  classical
  unfold switchKernel
  positivity

theorem switchKernel_self_ge_half {n : Nat} {d : Fin n → Nat} (G : GraphState n d) :
    (1 : ℝ) / 2 ≤ switchKernel n d G G := by
  classical
  simp only [switchKernel, ↓reduceIte]
  exact le_add_of_nonneg_right (by positivity)

end Problem315

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SwitchFoundations.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/FourVertexSwitch.lean -/
section

namespace OAI

noncomputable section

namespace Problem315

def FourDistinct {α : Type*} (a b c d : α) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

private def twoEdgeGraph {n : Nat} (a b c d : Fin n)
    (hab : a ≠ b) (hcd : c ≠ d) : SimpleGraph (Fin n) where
  Adj u v := (u = a ∧ v = b) ∨ (u = b ∧ v = a) ∨
    (u = c ∧ v = d) ∨ (u = d ∧ v = c)
  symm := by
    constructor
    intro u v huv
    tauto
  loopless := by
    constructor
    intro v hv
    rcases hv with h | h | h | h
    · exact hab (h.1.symm.trans h.2)
    · exact hab (h.2.symm.trans h.1)
    · exact hcd (h.1.symm.trans h.2)
    · exact hcd (h.2.symm.trans h.1)

private theorem twoEdgeGraph_matching {n : Nat} (a b c d : Fin n)
    (h : FourDistinct a b c d) :
    IsPerfectMatchingOn {a, b, c, d}
      (twoEdgeGraph a b c d h.1 h.2.2.2.2.2) := by
  rcases h with ⟨hab, hac, had, hbc, hbd, hcd⟩
  intro v
  constructor
  · intro hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · refine ⟨b, ?_, ?_⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · intro y hy
        simp_all [twoEdgeGraph]
    · refine ⟨a, ?_, ?_⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · intro y hy
        simp_all [twoEdgeGraph]
        aesop
    · refine ⟨d, ?_, ?_⟩
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · intro y hy
        simp_all [twoEdgeGraph]
        aesop
    · refine ⟨c, ?_, ?_⟩
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
      · intro y hy
        simp_all [twoEdgeGraph]
        aesop
  · intro hv w hw
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    change (v = a ∧ w = b) ∨ (v = b ∧ w = a) ∨
      (v = c ∧ w = d) ∨ (v = d ∧ w = c) at hw
    tauto

def fourVertexProposal {n : Nat} (a b c d : Fin n)
    (h : FourDistinct a b c d) : SwitchProposal n := by
  classical
  rcases h with ⟨hab, hac, had, hbc, hbd, hcd⟩
  let S : FourSet n := ⟨{a, b, c, d}, by
    simp [hab, hac, had, hbc, hbd, hcd]⟩
  have hfirst : IsPerfectMatchingOn S.val (twoEdgeGraph a b c d hab hcd) :=
    twoEdgeGraph_matching a b c d ⟨hab, hac, had, hbc, hbd, hcd⟩
  have hsecond : IsPerfectMatchingOn S.val (twoEdgeGraph a c b d hac hbd) := by
    have hm := twoEdgeGraph_matching a c b d ⟨hac, hab, had, hbc.symm, hcd, hbd⟩
    convert hm using 1
    ext x
    simp [S, or_left_comm]
  refine ⟨S, ⟨(⟨twoEdgeGraph a b c d hab hcd, hfirst⟩,
    ⟨twoEdgeGraph a c b d hac hbd, hsecond⟩), ?_⟩⟩
  intro heq
  have he := congrArg (fun M : PerfectMatching S => M.val.Adj a b) heq
  simp [twoEdgeGraph, hab, hac, had, hbc, hbd, Ne.symm hab] at he

@[simp] theorem removedMatching_fourVertexProposal {n : Nat} (a b c d : Fin n)
    (h : FourDistinct a b c d) (u v : Fin n) :
    (removedMatching (fourVertexProposal a b c d h)).Adj u v ↔
      (u = a ∧ v = b) ∨ (u = b ∧ v = a) ∨
      (u = c ∧ v = d) ∨ (u = d ∧ v = c) := by
  rcases h with ⟨hab, hac, had, hbc, hbd, hcd⟩
  rfl

@[simp] theorem addedMatching_fourVertexProposal {n : Nat} (a b c d : Fin n)
    (h : FourDistinct a b c d) (u v : Fin n) :
    (addedMatching (fourVertexProposal a b c d h)).Adj u v ↔
      (u = a ∧ v = c) ∨ (u = c ∧ v = a) ∨
      (u = b ∧ v = d) ∨ (u = d ∧ v = b) := by
  rcases h with ⟨hab, hac, had, hbc, hbd, hcd⟩
  rfl

theorem validSwitch_fourVertexProposal_iff {n : Nat} (G : SimpleGraph (Fin n))
    (a b c d : Fin n) (h : FourDistinct a b c d) :
    validSwitch G (fourVertexProposal a b c d h) ↔
      G.Adj a b ∧ G.Adj c d ∧ ¬ G.Adj a c ∧ ¬ G.Adj b d := by
  constructor
  · intro hv
    refine ⟨hv.1 ?_, hv.1 ?_, hv.2 ?_, hv.2 ?_⟩ <;> simp
  · rintro ⟨hab, hcd, hac, hbd⟩
    constructor
    · intro u v huv
      rw [removedMatching_fourVertexProposal] at huv
      rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab
      · exact G.symm.symm _ _ hab
      · exact hcd
      · exact G.symm.symm _ _ hcd
    · intro u v huv
      rw [addedMatching_fourVertexProposal] at huv
      rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hac
      · exact fun he => hac (G.symm.symm _ _ he)
      · exact hbd
      · exact fun he => hbd (G.symm.symm _ _ he)

theorem proposalResult_fourVertex_adj {n : Nat} (G : SimpleGraph (Fin n))
    (a b c d : Fin n) (h : FourDistinct a b c d)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : ¬ G.Adj a c) (hbd : ¬ G.Adj b d) (u v : Fin n) :
    (proposalResult G (fourVertexProposal a b c d h)).Adj u v ↔
      (G.Adj u v ∧ ¬ ((u = a ∧ v = b) ∨ (u = b ∧ v = a) ∨
        (u = c ∧ v = d) ∨ (u = d ∧ v = c))) ∨
      (u = a ∧ v = c) ∨ (u = c ∧ v = a) ∨
      (u = b ∧ v = d) ∨ (u = d ∧ v = b) := by
  classical
  have hv : validSwitch G (fourVertexProposal a b c d h) :=
    (validSwitch_fourVertexProposal_iff G a b c d h).2 ⟨hab, hcd, hac, hbd⟩
  simp only [proposalResult, ite_eq_left hv, replaceEdges,
    removedMatching_fourVertexProposal, addedMatching_fourVertexProposal]

theorem switchStep_of_fourVertex_result {n : Nat} {d : Fin n → Nat}
    (G H : GraphState n d) (a b c e : Fin n) (h : FourDistinct a b c e)
    (hab : G.val.Adj a b) (hce : G.val.Adj c e)
    (hac : ¬ G.val.Adj a c) (hbe : ¬ G.val.Adj b e)
    (heq : proposalResult G.val (fourVertexProposal a b c e h) = H.val) :
    SwitchStep n d G H := by
  exact ⟨fourVertexProposal a b c e h,
    (validSwitch_fourVertexProposal_iff G.val a b c e h).2 ⟨hab, hce, hac, hbe⟩, heq⟩

theorem proposalResult_fourVertex_adj_first {n : Nat} (G : SimpleGraph (Fin n))
    (a b c d : Fin n) (h : FourDistinct a b c d)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : ¬ G.Adj a c) (hbd : ¬ G.Adj b d) (v : Fin n) :
    (proposalResult G (fourVertexProposal a b c d h)).Adj a v ↔
      (G.Adj a v ∧ v ≠ b) ∨ v = c := by
  simpa [h.1, h.2.1, h.2.2.1] using
    proposalResult_fourVertex_adj G a b c d h hab hcd hac hbd a v

theorem proposalResult_fourVertex_adj_outside {n : Nat} (G : SimpleGraph (Fin n))
    (a b c d : Fin n) (h : FourDistinct a b c d)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : ¬ G.Adj a c) (hbd : ¬ G.Adj b d)
    (u v : Fin n) (hua : u ≠ a) (hub : u ≠ b) (huc : u ≠ c) (hud : u ≠ d) :
    (proposalResult G (fourVertexProposal a b c d h)).Adj u v ↔ G.Adj u v := by
  simpa [hua, hub, huc, hud] using
    proposalResult_fourVertex_adj G a b c d h hab hcd hac hbd u v

def fourVertexState {n : Nat} {d : Fin n → Nat} (G : GraphState n d)
    (a b c e : Fin n) (h : FourDistinct a b c e) : GraphState n d :=
  ⟨proposalResult G.val (fourVertexProposal a b c e h),
    proposalResult_realizes G.property (fourVertexProposal a b c e h)⟩

theorem switchStep_fourVertexState {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (a b c e : Fin n) (h : FourDistinct a b c e)
    (hab : G.val.Adj a b) (hce : G.val.Adj c e)
    (hac : ¬ G.val.Adj a c) (hbe : ¬ G.val.Adj b e) :
    SwitchStep n d G (fourVertexState G a b c e h) := by
  exact switchStep_of_fourVertex_result G _ a b c e h hab hce hac hbe rfl

theorem fourVertexState_agrees_outside {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (R : Finset (Fin n))
    (a b c e : Fin n) (h : FourDistinct a b c e)
    (ha : a ∈ R) (hb : b ∈ R) (hc : c ∈ R) (he : e ∈ R)
    (hab : G.val.Adj a b) (hce : G.val.Adj c e)
    (hac : ¬ G.val.Adj a c) (hbe : ¬ G.val.Adj b e)
    (u v : Fin n) (hu : u ∉ R) :
    (fourVertexState G a b c e h).val.Adj u v ↔ G.val.Adj u v := by
  apply proposalResult_fourVertex_adj_outside G.val a b c e h hab hce hac hbe u v
  · exact fun heq => hu (heq ▸ ha)
  · exact fun heq => hu (heq ▸ hb)
  · exact fun heq => hu (heq ▸ hc)
  · exact fun heq => hu (heq ▸ he)

end Problem315

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/FourVertexSwitch.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/FrozenRows.lean -/
section

namespace OAI

noncomputable section

namespace Problem315

def FrozenRowsAgree {n : Nat} (G H : SimpleGraph (Fin n))
    (R : Finset (Fin n)) : Prop :=
  ∀ u, u ∉ R → ∀ v, G.Adj u v ↔ H.Adj u v

theorem FrozenRowsAgree.refl {n : Nat} (G : SimpleGraph (Fin n))
    (R : Finset (Fin n)) : FrozenRowsAgree G G R := by
  intro u hu v
  rfl

theorem FrozenRowsAgree.symm {n : Nat} {G H : SimpleGraph (Fin n)}
    {R : Finset (Fin n)} (h : FrozenRowsAgree G H R) : FrozenRowsAgree H G R := by
  intro u hu v
  exact (h u hu v).symm

theorem FrozenRowsAgree.trans {n : Nat} {G H K : SimpleGraph (Fin n)}
    {R : Finset (Fin n)} (hGH : FrozenRowsAgree G H R)
    (hHK : FrozenRowsAgree H K R) : FrozenRowsAgree G K R := by
  intro u hu v
  exact (hGH u hu v).trans (hHK u hu v)

theorem graphDegree_split_residual {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (R : Finset (Fin n)) (v : Fin n) :
    (R.filter (G.Adj v)).card + ((Finset.univ \ R).filter (G.Adj v)).card =
      graphDegree G v := by
  classical
  have hin : (Finset.univ.filter (G.Adj v)).filter (fun w => w ∈ R) =
      R.filter (G.Adj v) := by
    ext w
    simp [and_comm]
  have hout : (Finset.univ.filter (G.Adj v)).filter (fun w => w ∉ R) =
      (Finset.univ \ R).filter (G.Adj v) := by
    ext w
    simp [and_comm]
  have hs := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (G.Adj v)) (fun w => w ∈ R)
  rw [hin, hout] at hs
  calc
    _ = (Finset.univ.filter (G.Adj v)).card := hs
    _ = graphDegree G v := by
      unfold graphDegree
      congr 1
      ext w
      simp

theorem residualDegree_eq_of_frozenRows {n : Nat} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (R : Finset (Fin n))
    (hdeg : ∀ v, graphDegree G v = graphDegree H v)
    (hfreeze : FrozenRowsAgree G H R) (v : Fin n) :
    (R.filter (G.Adj v)).card = (R.filter (H.Adj v)).card := by
  classical
  have hout : (Finset.univ \ R).filter (G.Adj v) =
      (Finset.univ \ R).filter (H.Adj v) := by
    apply Finset.filter_congr
    intro w hw
    have hwR : w ∉ R := (Finset.mem_sdiff.mp hw).2
    constructor
    · intro hvw
      exact ((hfreeze w hwR v).1 hvw.symm).symm
    · intro hvw
      exact ((hfreeze w hwR v).2 hvw.symm).symm
  have hg := graphDegree_split_residual G R v
  have hh := graphDegree_split_residual H R v
  rw [hout, hdeg v] at hg
  omega

theorem graphState_residualDegree_eq {n : Nat} {d : Fin n → Nat}
    (G H : GraphState n d) [DecidableRel G.val.Adj] [DecidableRel H.val.Adj]
    (R : Finset (Fin n)) (hfreeze : FrozenRowsAgree G.val H.val R) (v : Fin n) :
    (R.filter (G.val.Adj v)).card = (R.filter (H.val.Adj v)).card := by
  apply residualDegree_eq_of_frozenRows G.val H.val R _ hfreeze v
  intro u
  exact (G.property u).trans (H.property u).symm

theorem fourVertexState_residual_neighbors {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (R : Finset (Fin n))
    (a b c e : Fin n) (h : FourDistinct a b c e)
    [DecidableRel G.val.Adj] [DecidableRel (fourVertexState G a b c e h).val.Adj]
    (hc : c ∈ R) (hab : G.val.Adj a b) (hce : G.val.Adj c e)
    (hac : ¬ G.val.Adj a c) (hbe : ¬ G.val.Adj b e) :
    R.filter ((fourVertexState G a b c e h).val.Adj a) =
      insert c ((R.filter (G.val.Adj a)).erase b) := by
  classical
  ext w
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
  change (w ∈ R ∧ (proposalResult G.val (fourVertexProposal a b c e h)).Adj a w) ↔ _
  rw [proposalResult_fourVertex_adj_first G.val a b c e h hab hce hac hbe]
  constructor
  · rintro ⟨hwR, ⟨hadj, hwb⟩ | rfl⟩
    · exact Or.inr ⟨hwb, hwR, hadj⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨hwb, hwR, hadj⟩)
    · exact ⟨hc, Or.inr rfl⟩
    · exact ⟨hwR, Or.inl ⟨hadj, hwb⟩⟩

theorem fourVertexState_frozenRows {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (R : Finset (Fin n))
    (a b c e : Fin n) (h : FourDistinct a b c e)
    (ha : a ∈ R) (hb : b ∈ R) (hc : c ∈ R) (he : e ∈ R)
    (hab : G.val.Adj a b) (hce : G.val.Adj c e)
    (hac : ¬ G.val.Adj a c) (hbe : ¬ G.val.Adj b e) :
    FrozenRowsAgree (fourVertexState G a b c e h).val G.val R := by
  intro u hu v
  exact fourVertexState_agrees_outside G R a b c e h ha hb hc he hab hce hac hbe u v hu

end Problem315

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/FrozenRows.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SwitchWitness.lean -/
section

namespace OAI

open scoped BigOperators

namespace Problem315

namespace Havel

section FinsetWitness

variable {V : Type*} [DecidableEq V]

theorem exists_top_subset (R : Finset V) (w : V → Nat) (q : Nat)
    (hq : q ≤ R.card) :
    ∃ T ⊆ R, T.card = q ∧ ∀ i ∈ R, i ∉ T → ∀ j ∈ T, w i ≤ w j := by
  classical
  obtain ⟨T₀, hT₀R, hT₀q⟩ := Finset.exists_subset_card_eq hq
  have hnonempty : (R.powersetCard q).Nonempty :=
    ⟨T₀, Finset.mem_powersetCard.mpr ⟨hT₀R, hT₀q⟩⟩
  obtain ⟨T, hT, hmax⟩ :=
    Finset.exists_max_image (R.powersetCard q) (fun S => ∑ i ∈ S, w i) hnonempty
  obtain ⟨hTR, hTq⟩ := Finset.mem_powersetCard.mp hT
  refine ⟨T, hTR, hTq, ?_⟩
  intro i hiR hiT j hjT
  have hiErase : i ∉ T.erase j := fun h => hiT (Finset.mem_of_mem_erase h)
  have hswap : insert i (T.erase j) ∈ R.powersetCard q := by
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hiR
      · exact hTR (Finset.mem_of_mem_erase hx)
    · rw [Finset.card_insert_of_notMem hiErase, Finset.card_erase_of_mem hjT]
      have hpos := Finset.card_pos.mpr ⟨j, hjT⟩
      omega
  have hbound := hmax _ hswap
  rw [Finset.sum_insert hiErase] at hbound
  have hsum := Finset.sum_erase_add T w hjT
  omega

theorem exists_prescribed_neighborhood (R : Finset V) (d : V → Nat) (v : V)
    (hq : d v ≤ (R.erase v).card) :
    ∃ T ⊆ R, v ∉ T ∧ T.card = d v ∧
      ∀ i ∈ R, i ≠ v → i ∉ T → ∀ j ∈ T, d i ≤ d j := by
  classical
  obtain ⟨T, hTR, hTq, hsort⟩ := exists_top_subset (R.erase v) d (d v) hq
  refine ⟨T, fun x hx => Finset.mem_of_mem_erase (hTR hx), ?_, hTq, ?_⟩
  · intro hv
    exact Finset.notMem_erase v R (hTR hv)
  · intro i hiR hiv hiT j hjT
    exact hsort i (Finset.mem_erase.mpr ⟨hiv, hiR⟩) hiT j hjT

theorem exists_switch_witness_in (G : SimpleGraph V) [DecidableRel G.Adj] (R : Finset V)
    {v i j : V} (hvR : v ∈ R) (hiR : i ∈ R) (hjR : j ∈ R)
    (hvi : G.Adj v i) (hvj : ¬ G.Adj v j) (hvj_ne : v ≠ j)
    (hdeg : (R.filter (G.Adj i)).card ≤ (R.filter (G.Adj j)).card) :
    ∃ k ∈ R, k ≠ v ∧ k ≠ i ∧ k ≠ j ∧ G.Adj j k ∧ ¬ G.Adj i k := by
  classical
  let A := (R.filter (G.Adj i)).erase j
  let B := (R.filter (G.Adj j)).erase i
  have hcard : A.card ≤ B.card := by
    dsimp [A, B]
    simp only [Finset.card_erase_eq_ite, Finset.mem_filter, hiR, hjR, true_and]
    by_cases hij : G.Adj i j
    · have hji := hij.symm
      simp only [hij, hji, ite_true]
      omega
    · have hji : ¬ G.Adj j i := fun h => hij h.symm
      simpa only [hij, hji, ite_false] using hdeg
  have hvA : v ∈ A := by
    exact Finset.mem_erase.mpr ⟨hvj_ne, Finset.mem_filter.mpr ⟨hvR, hvi.symm⟩⟩
  have hvB : v ∉ B := by
    intro h
    exact hvj (Finset.mem_filter.mp (Finset.mem_of_mem_erase h)).2.symm
  have hcard' : (A.erase v).card < B.card :=
    lt_of_lt_of_le (Finset.card_erase_lt_of_mem hvA) hcard
  obtain ⟨k, hkB, hkA⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard'
  have hkv : k ≠ v := by
    intro h
    exact hvB (h ▸ hkB)
  have hkA' : k ∉ A := by
    intro h
    exact hkA (Finset.mem_erase.mpr ⟨hkv, h⟩)
  have hki : k ≠ i := (Finset.mem_erase.mp hkB).1
  have hkR : k ∈ R := (Finset.mem_filter.mp (Finset.mem_erase.mp hkB).2).1
  have hjk : G.Adj j k := (Finset.mem_filter.mp (Finset.mem_erase.mp hkB).2).2
  have hkj : k ≠ j := hjk.ne.symm
  refine ⟨k, hkR, hkv, hki, hkj, hjk, ?_⟩
  intro hik
  exact hkA' (Finset.mem_erase.mpr ⟨hkj, Finset.mem_filter.mpr ⟨hkR, hik⟩⟩)

theorem exists_improving_switch (G : SimpleGraph V) [DecidableRel G.Adj]
    (R T : Finset V) {v : V} (hvR : v ∈ R) (hTR : T ⊆ R) (hvT : v ∉ T)
    (hsize : T.card = (R.filter (G.Adj v)).card)
    (hsorted : ∀ i ∈ R, i ≠ v → i ∉ T → ∀ j ∈ T,
      (R.filter (G.Adj i)).card ≤ (R.filter (G.Adj j)).card)
    (hne : R.filter (G.Adj v) ≠ T) :
    ∃ i ∈ R, ∃ j ∈ T, ∃ k ∈ R,
      i ∉ T ∧ ¬ G.Adj v j ∧ G.Adj v i ∧ G.Adj j k ∧ ¬ G.Adj i k ∧
      v ≠ j ∧ k ≠ v ∧ k ≠ i ∧ k ≠ j := by
  classical
  have hnot_sub : ¬ R.filter (G.Adj v) ⊆ T := by
    intro h
    exact hne (Finset.eq_of_subset_of_card_le h hsize.le)
  obtain ⟨i, hiN, hiT⟩ := Finset.not_subset.mp hnot_sub
  have hnot_sub' : ¬ T ⊆ R.filter (G.Adj v) := by
    intro h
    exact hne (Finset.eq_of_subset_of_card_le h hsize.ge).symm
  obtain ⟨j, hjT, hjN⟩ := Finset.not_subset.mp hnot_sub'
  obtain ⟨hiR, hvi⟩ := Finset.mem_filter.mp hiN
  have hjR := hTR hjT
  have hvj : ¬ G.Adj v j := by
    intro h
    exact hjN (Finset.mem_filter.mpr ⟨hjR, h⟩)
  have hvj_ne : v ≠ j := by
    intro h
    exact hvT (h ▸ hjT)
  have hdeg := hsorted i hiR hvi.ne.symm hiT j hjT
  obtain ⟨k, hkR, hkv, hki, hkj, hjk, hik⟩ :=
    exists_switch_witness_in G R hvR hiR hjR hvi hvj hvj_ne hdeg
  exact ⟨i, hiR, j, hjT, k, hkR, hiT, hvj, hvi, hjk, hik,
    hvj_ne, hkv, hki, hkj⟩

end FinsetWitness

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_switch_witness (G : SimpleGraph V) [DecidableRel G.Adj]
    {v i j : V} (hvi : G.Adj v i) (hvj : ¬ G.Adj v j)
    (hvj_ne : v ≠ j) (hdeg : G.degree i ≤ G.degree j) :
    ∃ k : V, k ≠ v ∧ k ≠ i ∧ k ≠ j ∧ G.Adj j k ∧ ¬ G.Adj i k := by
  classical
  let A := (G.neighborFinset i).erase j
  let B := (G.neighborFinset j).erase i
  have hcard : A.card ≤ B.card := by
    dsimp [A, B]
    simp only [Finset.card_erase_eq_ite, G.mem_neighborFinset,
      G.card_neighborFinset_eq_degree]
    by_cases hij : G.Adj i j
    · have hji := hij.symm
      simp only [hij, hji, ite_true]
      omega
    · have hji : ¬ G.Adj j i := fun h => hij h.symm
      simpa only [hij, hji, ite_false] using hdeg
  have hvA : v ∈ A := by
    simp only [A, Finset.mem_erase, G.mem_neighborFinset]
    exact ⟨hvj_ne, hvi.symm⟩
  have hvB : v ∉ B := by
    intro h
    exact hvj ((G.mem_neighborFinset j v).mp (Finset.mem_of_mem_erase h)).symm
  have hcard' : (A.erase v).card < B.card :=
    lt_of_lt_of_le (Finset.card_erase_lt_of_mem hvA) hcard
  obtain ⟨k, hkB, hkA⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard'
  have hkv : k ≠ v := by
    intro h
    exact hvB (h ▸ hkB)
  have hkA' : k ∉ A := by
    intro h
    exact hkA (Finset.mem_erase.mpr ⟨hkv, h⟩)
  have hki : k ≠ i := (Finset.mem_erase.mp hkB).1
  have hjk : G.Adj j k :=
    (G.mem_neighborFinset j k).mp (Finset.mem_erase.mp hkB).2
  have hkj : k ≠ j := hjk.ne.symm
  refine ⟨k, hkv, hki, hkj, hjk, ?_⟩
  intro hik
  exact hkA' (Finset.mem_erase.mpr ⟨hkj, (G.mem_neighborFinset i k).mpr hik⟩)

end Havel

end Problem315

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SwitchWitness.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/NeighborAlignment.lean -/
section

namespace OAI

noncomputable section

namespace Problem315

theorem reach_target_by_neighbor_swaps
    {α β : Type*} [DecidableEq β]
    (r : α → α → Prop) (N : α → Finset β) (S : Finset β)
    (hcard : ∀ x, (N x).card = S.card)
    (hstep : ∀ x i j, i ∈ N x → i ∉ S → j ∈ S → j ∉ N x →
      ∃ y, r x y ∧ N y = insert j ((N x).erase i)) :
    ∀ x, ∃ y, Relation.ReflTransGen r x y ∧ N y = S := by
  classical
  have aux : ∀ k : ℕ, ∀ x, (S \ N x).card = k →
      ∃ y, Relation.ReflTransGen r x y ∧ N y = S := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x hk
      by_cases heq : N x = S
      · exact ⟨x, Relation.ReflTransGen.refl, heq⟩
      have hnotSN : ¬S ⊆ N x := by
        intro hsub
        exact heq (Finset.eq_of_subset_of_card_le hsub (hcard x).le).symm
      have hnotNS : ¬N x ⊆ S := by
        intro hsub
        exact heq (Finset.eq_of_subset_of_card_le hsub (hcard x).ge)
      obtain ⟨j, hjS, hjN⟩ := Finset.not_subset.mp hnotSN
      obtain ⟨i, hiN, hiS⟩ := Finset.not_subset.mp hnotNS
      obtain ⟨y, hxy, hNy⟩ := hstep x i j hiN hiS hjS hjN
      have hdiff : S \ N y = (S \ N x).erase j := by
        rw [hNy]
        ext z
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        aesop
      have hj : j ∈ S \ N x := Finset.mem_sdiff.mpr ⟨hjS, hjN⟩
      have hlt : (S \ N y).card < k := by
        rw [hdiff, ← hk]
        exact Finset.card_erase_lt_of_mem hj
      obtain ⟨z, hyz, hz⟩ := ih (S \ N y).card hlt y rfl
      exact ⟨z, (Relation.ReflTransGen.single hxy).trans hyz, hz⟩
  intro x
  exact aux (S \ N x).card x rfl

end Problem315

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/NeighborAlignment.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/HavelConnectivity.lean -/
section

namespace OAI

noncomputable section

namespace Problem315
attribute [local instance] Classical.propDecidable

theorem havel_neighborhood_repair_of_moves {n : Nat} {d : Fin n → Nat}
    (r : GraphState n d → GraphState n d → Prop)
    (hmoves : ∀ (G : GraphState n d) (a b c e : Fin n) (h : FourDistinct a b c e),
      G.val.Adj a b → G.val.Adj c e → ¬ G.val.Adj a c → ¬ G.val.Adj b e →
      r G (fourVertexState G a b c e h))
    (R T : Finset (Fin n)) (v : Fin n) (G : GraphState n d)
    (hv : v ∈ R) (hTR : T ⊆ R.erase v)
    (hsize : T.card = (R.filter (G.val.Adj v)).card)
    (hsorted : ∀ i ∈ R, i ≠ v → i ∉ T → ∀ j ∈ T,
      (R.filter (G.val.Adj i)).card ≤ (R.filter (G.val.Adj j)).card) :
    ∃ H : GraphState n d, Relation.ReflTransGen r G H ∧
      HavelCanonical.AgreeOutside R G.val H.val ∧ R.filter (H.val.Adj v) = T := by
  classical
  let A := {H : GraphState n d // FrozenRowsAgree H.val G.val R}
  let rA : A → A → Prop := fun H K => r H.val K.val
  let N : A → Finset (Fin n) := fun H => R.filter (H.val.val.Adj v)
  have hres (H : A) (w : Fin n) :
      (R.filter (H.val.val.Adj w)).card = (R.filter (G.val.Adj w)).card :=
    graphState_residualDegree_eq H.val G R H.property w
  have hcard (H : A) : (N H).card = T.card := (hres H v).trans hsize.symm
  have hstep : ∀ H i j, i ∈ N H → i ∉ T → j ∈ T → j ∉ N H →
      ∃ K, rA H K ∧ N K = insert j ((N H).erase i) := by
    intro H i j hi hiT hjT hj
    obtain ⟨hiR, hvi⟩ := Finset.mem_filter.mp hi
    have hjR : j ∈ R := Finset.mem_of_mem_erase (hTR hjT)
    have hvj_ne : v ≠ j := (Finset.mem_erase.mp (hTR hjT)).1.symm
    have hvj : ¬ H.val.val.Adj v j := by
      intro h
      exact hj (Finset.mem_filter.mpr ⟨hjR, h⟩)
    have hdeg : (R.filter (H.val.val.Adj i)).card ≤
        (R.filter (H.val.val.Adj j)).card := by
      rw [hres H i, hres H j]
      exact hsorted i hiR hvi.ne.symm hiT j hjT
    obtain ⟨k, hkR, hkv, hki, hkj, hjk, hik⟩ :=
      Havel.exists_switch_witness_in H.val.val R hv hiR hjR hvi hvj hvj_ne hdeg
    have hij : i ≠ j := by
      intro heq
      exact hiT (heq ▸ hjT)
    have hdist : FourDistinct v i j k :=
      ⟨hvi.ne, hvj_ne, hkv.symm, hij, hki.symm, hkj.symm⟩
    let K := fourVertexState H.val v i j k hdist
    have hfreeze : FrozenRowsAgree K.val H.val.val R :=
      fourVertexState_frozenRows H.val R v i j k hdist hv hiR hjR hkR hvi hjk hvj hik
    let KA : A := ⟨K, hfreeze.trans H.property⟩
    refine ⟨KA, hmoves H.val v i j k hdist hvi hjk hvj hik, ?_⟩
    exact fourVertexState_residual_neighbors H.val R v i j k hdist hjR hvi hjk hvj hik
  let GA : A := ⟨G, FrozenRowsAgree.refl G.val R⟩
  obtain ⟨H, hpath, hneigh⟩ := reach_target_by_neighbor_swaps rA N T hcard hstep GA
  refine ⟨H.val, ?_, ?_, hneigh⟩
  · exact Relation.ReflTransGen.lift (fun K : A => K.val) (fun _ _ h => h) _ _ hpath
  · intro u hu w
    exact (H.property u hu w).symm

theorem havel_neighborhood_repair {n : Nat} {d : Fin n → Nat}
    (R T : Finset (Fin n)) (v : Fin n) (G : GraphState n d)
    (hv : v ∈ R) (hTR : T ⊆ R.erase v)
    (hsize : T.card = (R.filter (G.val.Adj v)).card)
    (hsorted : ∀ i ∈ R, i ≠ v → i ∉ T → ∀ j ∈ T,
      (R.filter (G.val.Adj i)).card ≤ (R.filter (G.val.Adj j)).card) :
    ∃ H : GraphState n d, Relation.ReflTransGen (SwitchStep n d) G H ∧
      HavelCanonical.AgreeOutside R G.val H.val ∧ R.filter (H.val.Adj v) = T :=
  havel_neighborhood_repair_of_moves (SwitchStep n d) switchStep_fourVertexState
    R T v G hv hTR hsize hsorted

private theorem graphDegree_eq_degree {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (v : Fin n) : graphDegree G v = G.degree v := by
  classical
  unfold graphDegree SimpleGraph.degree
  congr 1
  ext w
  simp

theorem connectivity_of_fourVertex_moves (n : Nat) (d : Fin n → Nat)
    (r : GraphState n d → GraphState n d → Prop)
    (hsymm : ∀ ⦃first second⦄, r first second → r second first)
    (hmoves : ∀ (G : GraphState n d) (a b c e : Fin n) (h : FourDistinct a b c e),
      G.val.Adj a b → G.val.Adj c e → ¬ G.val.Adj a c → ¬ G.val.Adj b e →
      r G (fourVertexState G a b c e h))
    (G H : GraphState n d) : Relation.ReflTransGen r G H := by
  classical
  apply HavelCanonical.connected_of_neighborhood_repair
    (fun K : GraphState n d => K.val) Subtype.val_injective r hsymm _ _ G H
  · intro K L v
    rw [← graphDegree_eq_degree, ← graphDegree_eq_degree]
    exact (K.property v).trans (L.property v).symm
  · intro R T v K hv hTR hsize hsorted
    exact havel_neighborhood_repair_of_moves r hmoves R T v K hv hTR hsize hsorted

theorem switch_connectivity_direct (n : Nat) (d : Fin n → Nat)
    (G H : GraphState n d) : Relation.ReflTransGen (SwitchStep n d) G H :=
  connectivity_of_fourVertex_moves n d (SwitchStep n d) (fun _ _ h => switchStep_symm h)
    switchStep_fourVertexState G H

end Problem315

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/HavelConnectivity.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairFiberRedundancy.lean -/
section

namespace OAI

noncomputable section

namespace Problem315.PairResampling

attribute [local instance] Classical.propDecidable

theorem degree_eq_inside_add_outside {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Finset (Fin n)) (w : Fin n) :
    graphDegree G w = (a.filter (G.Adj w)).card +
      ((Finset.univ.filter (G.Adj w)).filter (fun v => v ∉ a)).card := by
  have h := (Finset.univ.filter (G.Adj w)).card_filter_add_card_filter_not
    (fun v => v ∈ a)
  have hin : (Finset.univ.filter (G.Adj w)).filter (fun v => v ∈ a) =
      a.filter (G.Adj w) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hin] at h
  exact h.symm

theorem inside_count_eq_of_degrees_outside {n : ℕ}
    {G H : SimpleGraph (Fin n)} (a : Finset (Fin n))
    (hdegree : ∀ w, graphDegree G w = graphDegree H w)
    (hout : ∀ u ∉ a, ∀ v ∉ a, G.Adj u v ↔ H.Adj u v)
    (w : Fin n) (hw : w ∉ a) :
    (a.filter (G.Adj w)).card = (a.filter (H.Adj w)).card := by
  have hs : (Finset.univ.filter (G.Adj w)).filter (fun v => v ∉ a) =
      (Finset.univ.filter (H.Adj w)).filter (fun v => v ∉ a) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hG, hv⟩
      exact ⟨(hout w hw v hv).mp hG, hv⟩
    · rintro ⟨hH, hv⟩
      exact ⟨(hout w hw v hv).mpr hH, hv⟩
  have h := hdegree w
  rw [degree_eq_inside_add_outside G a w, degree_eq_inside_add_outside H a w,
    hs] at h
  exact Nat.add_right_cancel h

theorem sameFiber_iff_outside_inside {n : ℕ} {d : Fin n → ℕ}
    (a : Finset (Fin n)) (G H : GraphState n d) :
    SameFiber a G.val H.val ↔
      (∀ u ∉ a, ∀ v ∉ a, G.val.Adj u v ↔ H.val.Adj u v) ∧
      (∀ u ∈ a, ∀ v ∈ a, G.val.Adj u v ↔ H.val.Adj u v) := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1⟩
  · rintro ⟨hout, hin⟩
    refine ⟨hout, hin, ?_⟩
    exact inside_count_eq_of_degrees_outside a
      (fun w => (G.property w).trans (H.property w).symm) hout

end Problem315.PairResampling

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairFiberRedundancy.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairFiberConnectivity.lean -/
section

namespace OAI

noncomputable section

namespace Problem315.PairResampling

attribute [local instance] Classical.propDecidable

theorem fourVertexState_sameFiber {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (a b c e : Fin n) (h : FourDistinct a b c e)
    (hab : G.val.Adj a b) (hce : G.val.Adj c e)
    (hac : ¬ G.val.Adj a c) (hbe : ¬ G.val.Adj b e) :
    SameFiber {a, e} G.val (fourVertexState G a b c e h).val := by
  apply (sameFiber_iff_outside_inside {a, e} G _).mpr
  constructor
  · intro u hu v hv
    have hua : u ≠ a := fun h' => hu (by simp [h'])
    have hue : u ≠ e := fun h' => hu (by simp [h'])
    have hva : v ≠ a := fun h' => hv (by simp [h'])
    have hve : v ≠ e := fun h' => hv (by simp [h'])
    change G.val.Adj u v ↔
      (proposalResult G.val (fourVertexProposal a b c e h)).Adj u v
    rw [proposalResult_fourVertex_adj G.val a b c e h hab hce hac hbe]
    simp [hua, hue, hva, hve]
  · intro u hu v hv
    have hub : u ≠ b := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact h.1
      · exact h.2.2.2.2.1.symm
    have huc : u ≠ c := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact h.2.1
      · exact h.2.2.2.2.2.symm
    have hvb : v ≠ b := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact h.1
      · exact h.2.2.2.2.1.symm
    have hvc : v ≠ c := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact h.2.1
      · exact h.2.2.2.2.2.symm
    change G.val.Adj u v ↔
      (proposalResult G.val (fourVertexProposal a b c e h)).Adj u v
    rw [proposalResult_fourVertex_adj G.val a b c e h hab hce hac hbe]
    simp [hub, huc, hvb, hvc]

def FiberMove (n : Nat) (d : Fin n → Nat) (G H : GraphState n d) : Prop :=
  ∃ a ∈ pairs n, SameFiber a G.val H.val

theorem fiberMove_connectivity (n : Nat) (d : Fin n → Nat) (G H : GraphState n d) :
    Relation.ReflTransGen (FiberMove n d) G H := by
  apply connectivity_of_fourVertex_moves n d (FiberMove n d) _ _ G H
  · intro K L h
    obtain ⟨a, ha, hfiber⟩ := h
    exact ⟨a, ha, hfiber.symm⟩
  · intro K a b c e h hab hce hac hbe
    refine ⟨{a, e}, ?_, fourVertexState_sameFiber K a b c e h hab hce hac hbe⟩
    simp [pairs, Finset.mem_powersetCard, h.2.2.1]

theorem generator_eq_zero_iff_constant {n : Nat} {d : Fin n → Nat}
    (f : StateSpace n d) :
    generator n d f = 0 ↔ ∀ G H : GraphState n d, f G = f H := by
  constructor
  · intro hf G H
    have hconst := (generator_eq_zero_iff f).mp hf
    have hpath := fiberMove_connectivity n d G H
    induction hpath with
    | refl => rfl
    | @tail K L hGK hKL ih =>
      obtain ⟨a, ha, hsame⟩ := hKL
      exact ih.trans (hconst a ha K L hsame)
  · intro hf
    apply (generator_eq_zero_iff f).mpr
    intro a ha G H _
    exact hf G H

end Problem315.PairResampling

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairFiberConnectivity.lean -/
