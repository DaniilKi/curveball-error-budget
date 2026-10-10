import ConfigurationPermutation
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Logic.Equiv.Fin.Basic

/- Whole-candidate ideal graph oracle. Runtime/RNG/censoring are outside scope. -/
namespace ConfigurationPairing
noncomputable section
open CurveballVerified
open scoped BigOperators Classical

variable {n : Nat}

instance adjacencyNeighborFintype (G : SimpleGraph (Fin n)) (v : Fin n) :
    Fintype {w : Fin n // G.Adj v w} := Fintype.ofFinite _

def labeledDegree (G : SimpleGraph (Fin n)) (v : Fin n) : Nat :=
  Fintype.card {w : Fin n // G.Adj v w}

def residualDegree (F : SimpleGraph (Fin n)) (d : Fin n → Nat) (v : Fin n) : Nat :=
  d v - labeledDegree F v

def neighborSplit (G F : SimpleGraph (Fin n)) (hFG : F ≤ G) (v : Fin n) :
    {w : Fin n // G.Adj v w} ≃
      ({w : Fin n // F.Adj v w} ⊕ ResidualNeighbor G F v) where
  toFun x := if h : F.Adj v x.val then Sum.inl ⟨x.val,h⟩
    else Sum.inr ⟨x.val,x.property,h⟩
  invFun x := match x with
    | Sum.inl w => ⟨w.val,hFG w.property⟩
    | Sum.inr w => ⟨w.val,w.property.1⟩
  left_inv := by
    rintro ⟨w,hw⟩
    by_cases h : F.Adj v w <;> simp [h]
  right_inv := by
    rintro (⟨w,hw⟩ | ⟨w,hw⟩) <;> simp [hw]

theorem degree_split (G F : SimpleGraph (Fin n)) (hFG : F ≤ G) (v : Fin n) :
    labeledDegree G v = labeledDegree F v + Fintype.card (ResidualNeighbor G F v) := by
  have h := Fintype.card_congr (neighborSplit G F hFG v)
  simpa only [labeledDegree,Fintype.card_sum] using h

theorem residual_card_from_labeled_degrees (G F : SimpleGraph (Fin n))
    (d : Fin n → Nat) (hFG : F ≤ G) (hd : ∀ v, labeledDegree G v = d v) (v : Fin n) :
    Fintype.card (ResidualNeighbor G F v) = residualDegree F d v := by
  have h := degree_split G F hFG v
  rw [hd v] at h
  unfold residualDegree
  omega

def TargetGraph (F : SimpleGraph (Fin n)) (d : Fin n → Nat) :=
  {G : SimpleGraph (Fin n) // F ≤ G ∧ ∀ v, labeledDegree G v = d v}

instance targetGraphFintype (F : SimpleGraph (Fin n)) (d : Fin n → Nat) :
    Fintype (TargetGraph F d) := by
  unfold TargetGraph
  exact Fintype.ofFinite _

def GoodMatching (F : SimpleGraph (Fin n)) (s : Fin n → Nat) (p : StubMatching s) : Prop :=
  (∀ x, (p.partner x).1 ≠ x.1) ∧
  (∀ v (i j : Fin (s v)), (p.partner ⟨v,i⟩).1 = (p.partner ⟨v,j⟩).1 → i = j) ∧
  (∀ x, ¬ F.Adj x.1 (p.partner x).1)

def projectedGraph (s : Fin n → Nat) (p : StubMatching s) : SimpleGraph (Fin n) where
  Adj v w := v ≠ w ∧ ∃ i : Fin (s v), (p.partner ⟨v,i⟩).1 = w
  symm := ⟨by
    intro v w h
    rcases h with ⟨hne,i,hi⟩
    subst w
    refine ⟨hne.symm,(p.partner ⟨v,i⟩).2,?_⟩
    exact congrArg (fun x : Stub s => x.1) (p.involutive ⟨v,i⟩)⟩
  loopless := ⟨by
    intro v h
    exact h.1 rfl⟩

def decodedGraph (F : SimpleGraph (Fin n)) (s : Fin n → Nat) (p : StubMatching s) :
    SimpleGraph (Fin n) := F ⊔ projectedGraph s p

theorem good_projectsTo (F : SimpleGraph (Fin n)) (s : Fin n → Nat)
    (p : StubMatching s) (hg : GoodMatching F s p) :
    ProjectsTo (decodedGraph F s p) F s p := by
  refine ⟨hg.1,hg.2.1,?_⟩
  intro v w
  constructor
  · rintro ⟨hAdj,hnotF⟩
    change F.Adj v w ∨ (v ≠ w ∧ ∃ i : Fin (s v), (p.partner ⟨v,i⟩).1 = w) at hAdj
    rcases hAdj with hF | hp
    · exact False.elim (hnotF hF)
    · exact hp.2
  · rintro ⟨i,hi⟩
    have hne : v ≠ w := by
      intro he
      apply hg.1 ⟨v,i⟩
      exact hi.trans he.symm
    refine ⟨Or.inr ⟨hne,i,hi⟩,?_⟩
    simpa only [hi] using hg.2.2 ⟨v,i⟩

theorem projectsTo_good (G F : SimpleGraph (Fin n)) (s : Fin n → Nat)
    (p : StubMatching s) (hp : ProjectsTo G F s p) : GoodMatching F s p := by
  refine ⟨hp.1,hp.2.1,?_⟩
  intro x
  exact ((hp.2.2 x.1 (p.partner x).1).mpr ⟨x.2,rfl⟩).2

theorem decodedGraph_eq_of_projectsTo (G F : SimpleGraph (Fin n)) (s : Fin n → Nat)
    (p : StubMatching s) (hFG : F ≤ G) (hp : ProjectsTo G F s p) :
    decodedGraph F s p = G := by
  ext v w
  change (F.Adj v w ∨ (v ≠ w ∧ ∃ i : Fin (s v), (p.partner ⟨v,i⟩).1 = w)) ↔ G.Adj v w
  constructor
  · rintro (hF | ⟨_,hi⟩)
    · exact hFG hF
    · exact ((hp.2.2 v w).mpr hi).1
  · intro hG
    by_cases hF : F.Adj v w
    · exact Or.inl hF
    · refine Or.inr ⟨?_,(hp.2.2 v w).mp ⟨hG,hF⟩⟩
      intro he
      subst w
      exact G.irrefl hG

def Accepts (F : SimpleGraph (Fin n)) (d : Fin n → Nat)
    (p : StubMatching (residualDegree F d)) : Prop :=
  GoodMatching F (residualDegree F d) p ∧
    ∀ v, labeledDegree (decodedGraph F (residualDegree F d) p) v = d v

def graphDecoder (F : SimpleGraph (Fin n)) (d : Fin n → Nat)
    (p : StubMatching (residualDegree F d)) : Option (TargetGraph F d) :=
  if ha : Accepts F d p then
    some ⟨decodedGraph F (residualDegree F d) p,le_sup_left,ha.2⟩ else none

theorem graphDecoder_some_iff (F : SimpleGraph (Fin n)) (d : Fin n → Nat)
    (p : StubMatching (residualDegree F d)) (g : TargetGraph F d) :
    graphDecoder F d p = some g ↔ ProjectsTo g.val F (residualDegree F d) p := by
  constructor
  · intro hdec
    by_cases ha : Accepts F d p
    · simp only [graphDecoder,dif_pos ha] at hdec
      have he : (⟨decodedGraph F (residualDegree F d) p,le_sup_left,ha.2⟩ :
          TargetGraph F d) = g := Option.some.inj hdec
      have hv : decodedGraph F (residualDegree F d) p = g.val := congrArg Subtype.val he
      have hp := good_projectsTo F (residualDegree F d) p ha.1
      rw [hv] at hp
      exact hp
    · simp only [graphDecoder,dif_neg ha] at hdec
      cases hdec
  · intro hp
    have he := decodedGraph_eq_of_projectsTo g.val F (residualDegree F d) p g.property.1 hp
    have ha : Accepts F d p := by
      refine ⟨projectsTo_good g.val F (residualDegree F d) p hp,?_⟩
      intro v
      rw [he]
      exact g.property.2 v
    simp only [graphDecoder,dif_pos ha]
    exact congrArg Option.some (Subtype.ext he)

def decoderFiberEquiv (F : SimpleGraph (Fin n)) (d : Fin n → Nat) (g : TargetGraph F d) :
    {p : StubMatching (residualDegree F d) // graphDecoder F d p = some g} ≃
      GraphFiber g.val F (residualDegree F d) where
  toFun p := ⟨p.val,(graphDecoder_some_iff F d p.val g).mp p.property⟩
  invFun p := ⟨p.val,(graphDecoder_some_iff F d p.val g).mpr p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def graphFiberFactor (F : SimpleGraph (Fin n)) (d : Fin n → Nat) : Nat :=
  ∏ v : Fin n, Nat.factorial (residualDegree F d v)

theorem graphDecoder_equal_fibers (F : SimpleGraph (Fin n)) (d : Fin n → Nat)
    (g : TargetGraph F d) :
    (Finset.univ.filter (fun p : StubMatching (residualDegree F d) =>
      graphDecoder F d p = some g)).card = graphFiberFactor F d := by
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (decoderFiberEquiv F d g)]
  exact graphFiber_card_factorial g.val F (residualDegree F d)
    (residual_card_from_labeled_degrees g.val F d g.property.1 g.property.2)

theorem graphFiberFactor_pos (F : SimpleGraph (Fin n)) (d : Fin n → Nat) :
    0 < graphFiberFactor F d := by
  apply Finset.prod_pos
  intro v _
  exact Nat.factorial_pos _

def graphWitnessMatching (F : SimpleGraph (Fin n)) (d : Fin n → Nat)
    (g0 : TargetGraph F d) : StubMatching (residualDegree F d) :=
  (Classical.choice (graphFiber_nonempty g0.val F (residualDegree F d)
    (residual_card_from_labeled_degrees g0.val F d g0.property.1 g0.property.2))).val

def graphCappedLaw (F : SimpleGraph (Fin n)) (d : Fin n → Nat)
    (g0 : TargetGraph F d) (cap : Nat) : FiniteLaw (Option (TargetGraph F d)) := by
  letI : Nonempty (StubMatching (residualDegree F d)) := ⟨graphWitnessMatching F d g0⟩
  exact cappedLaw (graphDecoder F d) cap

def graphFailureRate (F : SimpleGraph (Fin n)) (d : Fin n → Nat) : ℝ :=
  1 - (Fintype.card (TargetGraph F d) : ℝ) *
    ((graphFiberFactor F d : ℝ) / Fintype.card (StubMatching (residualDegree F d)))

theorem graphCapped_contract (F : SimpleGraph (Fin n)) (d : Fin n → Nat)
    (g0 : TargetGraph F d) (cap : Nat) :
    0 ≤ graphFailureRate F d ∧ graphFailureRate F d < 1 ∧
    (graphCappedLaw F d g0 cap).mass none = graphFailureRate F d ^ cap ∧
    ∀ g, (graphCappedLaw F d g0 cap).mass (some g) =
      (1 - graphFailureRate F d ^ cap) / Fintype.card (TargetGraph F d) := by
  letI : Nonempty (TargetGraph F d) := ⟨g0⟩
  letI : Nonempty (StubMatching (residualDegree F d)) := ⟨graphWitnessMatching F d g0⟩
  simpa only [graphCappedLaw,graphFailureRate,failureRate] using
    equal_fiber_capped_law (graphDecoder F d) (graphFiberFactor F d)
      (graphFiberFactor_pos F d) (graphDecoder_equal_fibers F d) cap

theorem firstCandidateLaw_comp_uniformMap {Ω A H : Type}
    [Fintype Ω] [Nonempty Ω] [Fintype A] [Nonempty A] [Fintype H]
    (g : Ω → A) (f : A → Option H) (tail : FiniteLaw (Option H))
    (hmap : mapLaw (uniformLaw Ω) g = uniformLaw A) :
    firstCandidateLaw (f ∘ g) tail = firstCandidateLaw f tail := by
  have hprod := mapLaw_product (uniformLaw Ω) tail g id
  rw [mapLaw_id] at hprod
  unfold firstCandidateLaw
  rw [← hmap,← hprod,mapLaw_comp]
  rfl

theorem cappedLaw_comp_uniformMap {Ω A H : Type}
    [Fintype Ω] [Nonempty Ω] [Fintype A] [Nonempty A] [Fintype H]
    (g : Ω → A) (f : A → Option H)
    (hmap : mapLaw (uniformLaw Ω) g = uniformLaw A) (cap : Nat) :
    cappedLaw (f ∘ g) cap = cappedLaw f cap := by
  induction cap with
  | zero => rfl
  | succ cap ih =>
    rw [cappedLaw_step,cappedLaw_step,ih]
    exact firstCandidateLaw_comp_uniformMap g f _ hmap

def permutationGraphLaw (F : SimpleGraph (Fin n)) (d : Fin n → Nat)
    (g0 : TargetGraph F d) (cap : Nat) : FiniteLaw (Option (TargetGraph F d)) :=
  cappedLaw (graphDecoder F d ∘
    (fun e => relabelMatching (residualDegree F d) e (graphWitnessMatching F d g0))) cap

theorem permutationGraphLaw_eq_capped (F : SimpleGraph (Fin n)) (d : Fin n → Nat)
    (g0 : TargetGraph F d) (cap : Nat) :
    permutationGraphLaw F d g0 cap = graphCappedLaw F d g0 cap := by
  letI : Nonempty (StubMatching (residualDegree F d)) := ⟨graphWitnessMatching F d g0⟩
  have hm := idealMatchingLaw_uniform (residualDegree F d) (graphWitnessMatching F d g0)
  change mapLaw (uniformLaw (Equiv.Perm (Stub (residualDegree F d))))
    (fun e => relabelMatching (residualDegree F d) e (graphWitnessMatching F d g0)) =
      uniformLaw (StubMatching (residualDegree F d)) at hm
  exact cappedLaw_comp_uniformMap _ (graphDecoder F d) hm cap

def adjacentPermutationGraphLaw (F : SimpleGraph (Fin n)) (d : Fin n → Nat)
    (m : Nat) (slots : Fin m × Bool ≃ Stub (residualDegree F d)) (cap : Nat) :
    FiniteLaw (Option (TargetGraph F d)) :=
  cappedLaw (graphDecoder F d ∘
    (fun e => adjacentPairing (residualDegree F d) m (slots.trans e))) cap

theorem adjacentPermutationGraphLaw_eq_capped (F : SimpleGraph (Fin n)) (d : Fin n → Nat)
    (g0 : TargetGraph F d) (m : Nat) (slots : Fin m × Bool ≃ Stub (residualDegree F d))
    (cap : Nat) : adjacentPermutationGraphLaw F d m slots cap = graphCappedLaw F d g0 cap := by
  letI : Nonempty (StubMatching (residualDegree F d)) := ⟨graphWitnessMatching F d g0⟩
  have hm := idealAdjacentLaw_uniform (residualDegree F d) m slots
  change mapLaw (uniformLaw (Equiv.Perm (Stub (residualDegree F d))))
    (fun e => adjacentPairing (residualDegree F d) m (slots.trans e)) =
      uniformLaw (StubMatching (residualDegree F d)) at hm
  exact cappedLaw_comp_uniformMap _ (graphDecoder F d) hm cap

theorem ideal_adjacent_graph_oracle_contract (F : SimpleGraph (Fin n)) (d : Fin n → Nat)
    (g0 : TargetGraph F d) (m : Nat) (slots : Fin m × Bool ≃ Stub (residualDegree F d))
    (cap : Nat) :
    0 ≤ graphFailureRate F d ∧ graphFailureRate F d < 1 ∧
    (adjacentPermutationGraphLaw F d m slots cap).mass none = graphFailureRate F d ^ cap ∧
    ∀ g, (adjacentPermutationGraphLaw F d m slots cap).mass (some g) =
      (1 - graphFailureRate F d ^ cap) / Fintype.card (TargetGraph F d) := by
  rw [adjacentPermutationGraphLaw_eq_capped F d g0]
  exact graphCapped_contract F d g0 cap

def boolFinTwo : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := decide (i.val = 1)
  left_inv := by
    intro b
    cases b <;> rfl
  right_inv := by
    intro i
    apply Fin.ext
    by_cases h : i.val = 1
    · simp [h]
    · have hz : i.val = 0 := by
        have hi := i.isLt
        omega
      simp [hz]

def pairIndex (m : Nat) : Fin m × Bool ≃ Fin (m * 2) :=
  (Equiv.prodCongr (Equiv.refl (Fin m)) boolFinTwo).trans finProdFinEquiv

theorem pairIndex_false (m : Nat) (i : Fin m) :
    (pairIndex m (i,false)).val = 2 * i.val := by
  change 0 + 2 * i.val = 2 * i.val
  omega

theorem pairIndex_true (m : Nat) (i : Fin m) :
    (pairIndex m (i,true)).val = 2 * i.val + 1 := by
  change 1 + 2 * i.val = 2 * i.val + 1
  omega

def flatPermutationGraphLaw (F : SimpleGraph (Fin n)) (d : Fin n → Nat)
    (m : Nat) (array : Fin (m * 2) ≃ Stub (residualDegree F d)) (cap : Nat) :
    FiniteLaw (Option (TargetGraph F d)) :=
  adjacentPermutationGraphLaw F d m ((pairIndex m).trans array) cap

theorem ideal_flat_graph_oracle_contract (F : SimpleGraph (Fin n)) (d : Fin n → Nat)
    (g0 : TargetGraph F d) (m : Nat) (array : Fin (m * 2) ≃ Stub (residualDegree F d))
    (cap : Nat) :
    0 ≤ graphFailureRate F d ∧ graphFailureRate F d < 1 ∧
    (flatPermutationGraphLaw F d m array cap).mass none = graphFailureRate F d ^ cap ∧
    ∀ g, (flatPermutationGraphLaw F d m array cap).mass (some g) =
      (1 - graphFailureRate F d ^ cap) / Fintype.card (TargetGraph F d) :=
  ideal_adjacent_graph_oracle_contract F d g0 m ((pairIndex m).trans array) cap

set_option pp.all true in
#check @graphDecoder_some_iff
set_option pp.all true in
#check @residual_card_from_labeled_degrees
set_option pp.all true in
#check @graphCapped_contract
set_option pp.all true in
#check @ideal_adjacent_graph_oracle_contract
set_option pp.all true in
#check @ideal_flat_graph_oracle_contract
#print axioms graphDecoder_some_iff
#print axioms residual_card_from_labeled_degrees
#print axioms graphDecoder_equal_fibers
#print axioms graphCapped_contract
#print axioms ideal_adjacent_graph_oracle_contract
#print axioms pairIndex_false
#print axioms pairIndex_true
#print axioms ideal_flat_graph_oracle_contract
#print graphDecoder
#print adjacentPermutationGraphLaw
end
end ConfigurationPairing
