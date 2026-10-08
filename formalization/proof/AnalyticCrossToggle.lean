import AnalyticSwitchEnergy

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SwitchFlip.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
attribute [local instance] Classical.propDecidable

namespace Problem315.SwitchFlip

variable {n : ℕ} {d : Fin n → ℕ}

lemma not_valid_reverse {G : SimpleGraph (Fin n)} {p : SwitchProposal n}
    (h : validSwitch G p) : ¬ validSwitch G (reverseProposal p) := by
  intro hr
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < p.1.val.card by rw [p.1.property]; omega)
  obtain ⟨v, hv, _⟩ := (p.2.val.1.property u).1 hu
  exact hr.2 hv (h.1 hv)

lemma valid_reverse_result {G : GraphState n d} {p : SwitchProposal n}
    (h : validSwitch G.val p) :
    validSwitch (proposalState G p).val (reverseProposal p) := by
  change validSwitch (proposalResult G.val p) (reverseProposal p)
  rw [proposalResult_of_valid h]
  exact validSwitch_reverse_replace h

lemma state_reverse {G : GraphState n d} {p : SwitchProposal n}
    (h : validSwitch G.val p) :
    proposalState (proposalState G p) (reverseProposal p) = G := by
  apply Subtype.ext
  exact proposalResult_reverse h

def flip (p : SwitchProposal n) (G : GraphState n d) : GraphState n d :=
  if validSwitch G.val p then proposalState G p
  else if validSwitch G.val (reverseProposal p) then proposalState G (reverseProposal p)
  else G

@[simp] theorem flip_of_valid (p : SwitchProposal n) (G : GraphState n d)
    (h : validSwitch G.val p) : flip p G = proposalState G p := by
  simp [flip, h]

@[simp] theorem flip_of_reverse_valid (p : SwitchProposal n) (G : GraphState n d)
    (h : validSwitch G.val (reverseProposal p)) :
    flip p G = proposalState G (reverseProposal p) := by
  have hn : ¬ validSwitch G.val p := by simpa using not_valid_reverse h
  simp [flip, hn, h]

@[simp] theorem flip_reverse (p : SwitchProposal n) (G : GraphState n d) :
    flip (reverseProposal p) G = flip p G := by
  by_cases h : validSwitch G.val p
  · simp [flip, h, not_valid_reverse h]
  · by_cases hr : validSwitch G.val (reverseProposal p) <;> simp [flip, h, hr]

 theorem flip_involutive (p : SwitchProposal n) :
    Function.Involutive (flip (d := d) p) := by
  intro G
  by_cases h : validSwitch G.val p
  · rw [flip_of_valid p G h,
      flip_of_reverse_valid p _ (valid_reverse_result h), state_reverse h]
  · by_cases hr : validSwitch G.val (reverseProposal p)
    · rw [flip_of_reverse_valid p G hr]
      have hv : validSwitch (proposalState G (reverseProposal p)).val p := by
        simpa using valid_reverse_result hr
      rw [flip_of_valid p _ hv]
      simpa using state_reverse hr
    · simp [flip, h, hr]

def equiv (p : SwitchProposal n) : Equiv.Perm (GraphState n d) :=
  ⟨flip p, flip p, flip_involutive p, flip_involutive p⟩

@[simp] theorem equiv_apply (p : SwitchProposal n) (G : GraphState n d) :
    equiv p G = flip p G := rfl

def isometry (p : SwitchProposal n) :
    PairResampling.StateSpace n d ≃ₗᵢ[ℝ] PairResampling.StateSpace n d :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (equiv p)

@[simp] theorem isometry_apply (p : SwitchProposal n)
    (f : PairResampling.StateSpace n d) (G : GraphState n d) :
    isometry p f G = f (flip p G) := rfl

def operator (p : SwitchProposal n) :
    PairResampling.StateSpace n d →L[ℝ] PairResampling.StateSpace n d :=
  (isometry p).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem operator_apply (p : SwitchProposal n)
    (f : PairResampling.StateSpace n d) (G : GraphState n d) :
    operator p f G = f (flip p G) := rfl

@[simp] theorem operator_involutive (p : SwitchProposal n)
    (f : PairResampling.StateSpace n d) : operator p (operator p f) = f := by
  ext G
  simp only [operator_apply, flip_involutive p G]

 theorem operator_symmetric (p : SwitchProposal n) :
    (operator (d := d) p).toLinearMap.IsSymmetric := by
  intro f g
  change ⟪operator p f, g⟫ = ⟪f, operator p g⟫
  have h := (isometry (d := d) p).inner_map_map f (operator p g)
  change ⟪operator p f, operator p (operator p g)⟫ = ⟪f, operator p g⟫ at h
  simpa only [operator_involutive] using h

def projection (p : SwitchProposal n) :
    PairResampling.StateSpace n d →L[ℝ] PairResampling.StateSpace n d :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ _ - operator p)

@[simp] theorem projection_apply (p : SwitchProposal n)
    (f : PairResampling.StateSpace n d) (G : GraphState n d) :
    projection p f G = (f G - f (flip p G)) / 2 := by
  simp [projection, div_eq_mul_inv, mul_comm]

 theorem projection_idempotent (p : SwitchProposal n)
    (f : PairResampling.StateSpace n d) : projection p (projection p f) = projection p f := by
  ext G
  simp only [projection_apply, flip_involutive p G]
  ring

 theorem projection_symmetric (p : SwitchProposal n) :
    (projection (d := d) p).toLinearMap.IsSymmetric := by
  intro f g
  change ⟪(1 / 2 : ℝ) • (f - operator p f), g⟫ =
    ⟪f, (1 / 2 : ℝ) • (g - operator p g)⟫
  simp only [real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_sub_right]
  have h := operator_symmetric p f g
  change ⟪operator p f, g⟫ = ⟪f, operator p g⟫ at h
  rw [h]

 theorem inner_projection (p : SwitchProposal n)
    (f : PairResampling.StateSpace n d) :
    ⟪f, projection p f⟫ = ‖projection p f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  have h := projection_symmetric p f (projection p f)
  change ⟪projection p f, projection p f⟫ = ⟪f, projection p (projection p f)⟫ at h
  simpa only [projection_idempotent] using h.symm

@[simp] theorem projection_reverse (p : SwitchProposal n) :
    projection (d := d) (reverseProposal p) = projection p := by
  ext f G
  simp only [projection_apply, flip_reverse]

theorem norm_projection_sq (p : SwitchProposal n)
    (f : PairResampling.StateSpace n d) :
    ‖projection p f‖ ^ 2 =
      (1 / 4 : ℝ) * ∑ G : GraphState n d, (f G - f (flip p G)) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PairResampling.state_inner, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro G _
  rw [projection_apply]
  ring

theorem proposal_sameFiber (p : SwitchProposal n) (a : Finset (Fin n))
    (hcross : SwitchPairFiber.Crosses p a) (G : GraphState n d) :
    PairResampling.SameFiber a G.val (proposalState G p).val := by
  apply sameFiber_of_same_side a G (proposalState G p)
  intro u v hside
  have hm : ¬ (removedMatching p).Adj u v := by
    intro h
    have hc := hcross u v (Or.inl h)
    tauto
  have hn : ¬ (addedMatching p).Adj u v := by
    intro h
    have hc := hcross u v (Or.inr h)
    tauto
  by_cases hv : validSwitch G.val p
  · change G.val.Adj u v ↔ (proposalResult G.val p).Adj u v
    rw [proposalResult_of_valid hv]
    change G.val.Adj u v ↔ (G.val.Adj u v ∧ ¬ (removedMatching p).Adj u v) ∨
      (addedMatching p).Adj u v
    simp [hm, hn]
  · change G.val.Adj u v ↔ (proposalResult G.val p).Adj u v
    simp [proposalResult, hv]

theorem flip_sameFiber (p : SwitchProposal n) (a : Finset (Fin n))
    (hcross : SwitchPairFiber.Crosses p a) (G : GraphState n d) :
    PairResampling.SameFiber a G.val (flip p G).val := by
  have hr : SwitchPairFiber.Crosses (reverseProposal p) a := by
    intro u v h
    apply hcross u v
    simpa only [removedMatching_reverse, addedMatching_reverse, or_comm] using h
  by_cases hv : validSwitch G.val p
  · rw [flip_of_valid p G hv]
    exact proposal_sameFiber p a hcross G
  · by_cases hv' : validSwitch G.val (reverseProposal p)
    · rw [flip_of_reverse_valid p G hv']
      exact proposal_sameFiber (reverseProposal p) a hr G
    · simp only [flip, ite_eq_right hv, ite_eq_right hv']
      exact PairResampling.SameFiber.refl a G.val

theorem projection_eq_zero_of_fiber (p : SwitchProposal n) (a : Finset (Fin n))
    (hcross : SwitchPairFiber.Crosses p a) (f : PairResampling.StateSpace n d)
    (hf : f ∈ PairResampling.fiberSpace n d a) : projection p f = 0 := by
  ext G
  change projection p f G = 0
  rw [projection_apply, hf G (flip p G) (flip_sameFiber p a hcross G)]
  ring

theorem projection_mem_orthogonal (p : SwitchProposal n) (a : Finset (Fin n))
    (hcross : SwitchPairFiber.Crosses p a) (f : PairResampling.StateSpace n d) :
    projection p f ∈ (PairResampling.fiberSpace n d a)ᗮ := by
  apply (Submodule.mem_orthogonal _ _).mpr
  intro g hg
  have h := projection_symmetric p g f
  change ⟪projection p g, f⟫ = ⟪g, projection p f⟫ at h
  rw [projection_eq_zero_of_fiber p a hcross g hg, inner_zero_left] at h
  exact h.symm

@[simp] theorem projection_expectation (p : SwitchProposal n) (a : Finset (Fin n))
    (hcross : SwitchPairFiber.Crosses p a) (f : PairResampling.StateSpace n d) :
    projection p (PairResampling.expectation n d a f) = 0 :=
  projection_eq_zero_of_fiber p a hcross _ (PairResampling.expectation_mem a f)

 theorem fluctuation_projection (p : SwitchProposal n) (a : Finset (Fin n))
    (hcross : SwitchPairFiber.Crosses p a) (f : PairResampling.StateSpace n d) :
    PairResampling.fluctuation n d a (projection p f) = projection p f := by
  exact (Submodule.starProjection_eq_self_iff).mpr
    (projection_mem_orthogonal p a hcross f)

 theorem projection_fluctuation (p : SwitchProposal n) (a : Finset (Fin n))
    (hcross : SwitchPairFiber.Crosses p a) (f : PairResampling.StateSpace n d) :
    projection p (PairResampling.fluctuation n d a f) = projection p f := by
  rw [PairResampling.fluctuation_eq_sub, map_sub,
    projection_expectation p a hcross, sub_zero]

theorem isSymmetricProjection (p : SwitchProposal n) :
    (projection (d := d) p).toLinearMap.IsSymmetricProjection := by
  refine ⟨?_, projection_symmetric p⟩
  apply LinearMap.ext
  intro f
  change projection p (projection p f) = projection p f
  exact projection_idempotent p f

theorem norm_projection_le_of_mem (p : SwitchProposal n)
    (J : Submodule ℝ (PairResampling.StateSpace n d))
    (hJ : ∀ f, projection p f ∈ J) (f : PairResampling.StateSpace n d) :
    ‖projection p f‖ ≤ ‖J.starProjection f‖ := by
  have hz := Submodule.starProjection_inner_eq_zero (K := J) f
    (projection p f) (hJ f)
  rw [inner_sub_left, inner_projection] at hz
  have hc := real_inner_le_norm (J.starProjection f) (projection p f)
  have hp := norm_nonneg (projection p f)
  have hj := norm_nonneg (J.starProjection f)
  by_cases he : ‖projection p f‖ = 0
  · rw [he]
    exact hj
  · have hp' : 0 < ‖projection p f‖ := lt_of_le_of_ne hp (Ne.symm he)
    nlinarith

theorem projection_mem_jointOrthogonal (p : SwitchProposal n)
    (a b : Finset (Fin n)) (ha : SwitchPairFiber.Crosses p a)
    (hb : SwitchPairFiber.Crosses p b) (f : PairResampling.StateSpace n d) :
    projection p f ∈ (PairResampling.fiberSpace n d a ⊔
      PairResampling.fiberSpace n d b)ᗮ := by
  rw [← Submodule.inf_orthogonal]
  exact ⟨projection_mem_orthogonal p a ha f, projection_mem_orthogonal p b hb f⟩

theorem norm_projection_le_jointOrthogonal (p : SwitchProposal n)
    (a b : Finset (Fin n)) (ha : SwitchPairFiber.Crosses p a)
    (hb : SwitchPairFiber.Crosses p b) (f : PairResampling.StateSpace n d) :
    ‖projection p f‖ ≤ ‖(PairResampling.fiberSpace n d a ⊔
      PairResampling.fiberSpace n d b)ᗮ.starProjection f‖ := by
  exact norm_projection_le_of_mem p _ (projection_mem_jointOrthogonal p a b ha hb) f

end Problem315.SwitchFlip

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SwitchFlip.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/CrossTogglePairs.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.CrossToggle

open SwitchFlip

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {d : Fin n → ℕ}

def crossProposal (i j k l : Fin n) (h : FourDistinct i j k l) : SwitchProposal n :=
  fourVertexProposal i k l j
    (show FourDistinct i k l j from
      ⟨h.2.1, h.2.2.1, h.1, h.2.2.2.2.2, h.2.2.2.1.symm, h.2.2.2.2.1.symm⟩)

theorem crossProposal_left (i j k l : Fin n) (h : FourDistinct i j k l) :
    SwitchPairFiber.Crosses (crossProposal i j k l h) {i, j} := by
  rcases h with ⟨hij, hik, hil, hjk, hjl, hkl⟩
  intro u v huv
  simp only [crossProposal, removedMatching_fourVertexProposal,
    addedMatching_fourVertexProposal] at huv
  rcases huv with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
    (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  all_goals simp_all [Ne.symm]

theorem crossProposal_right (i j k l : Fin n) (h : FourDistinct i j k l) :
    SwitchPairFiber.Crosses (crossProposal i j k l h) {k, l} := by
  rcases h with ⟨hij, hik, hil, hjk, hjl, hkl⟩
  intro u v huv
  simp only [crossProposal, removedMatching_fourVertexProposal,
    addedMatching_fourVertexProposal] at huv
  rcases huv with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
    (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  all_goals simp_all [Ne.symm]

theorem crossProposal_swap_pairs (i j k l : Fin n)
    (h : FourDistinct i j k l) (h' : FourDistinct k l i j) :
    crossProposal i j k l h = crossProposal k l i j h' := by
  apply SwitchProposal.ext_matchings
  · ext u v
    simp only [crossProposal, removedMatching_fourVertexProposal]
    tauto
  · ext u v
    simp only [crossProposal, addedMatching_fourVertexProposal]
    tauto

theorem crossProposal_swap_left (i j k l : Fin n)
    (h : FourDistinct i j k l) (h' : FourDistinct j i k l) :
    crossProposal j i k l h' = reverseProposal (crossProposal i j k l h) := by
  apply SwitchProposal.ext_matchings
  · ext u v
    simp only [crossProposal, removedMatching_reverse,
      removedMatching_fourVertexProposal, addedMatching_fourVertexProposal]
    tauto
  · ext u v
    simp only [crossProposal, addedMatching_reverse,
      removedMatching_fourVertexProposal, addedMatching_fourVertexProposal]
    tauto

theorem crossProposal_swap_right (i j k l : Fin n)
    (h : FourDistinct i j k l) (h' : FourDistinct i j l k) :
    crossProposal i j l k h' = reverseProposal (crossProposal i j k l h) := by
  apply SwitchProposal.ext_matchings
  · ext u v
    simp only [crossProposal, removedMatching_reverse,
      removedMatching_fourVertexProposal, addedMatching_fourVertexProposal]
  · ext u v
    simp only [crossProposal, addedMatching_reverse,
      removedMatching_fourVertexProposal, addedMatching_fourVertexProposal]

theorem crossProjection_swap_left (i j k l : Fin n)
    (h : FourDistinct i j k l) (h' : FourDistinct j i k l) :
    projection (d := d) (crossProposal j i k l h') =
      projection (crossProposal i j k l h) := by
  rw [crossProposal_swap_left i j k l h h', projection_reverse]

theorem crossProjection_swap_right (i j k l : Fin n)
    (h : FourDistinct i j k l) (h' : FourDistinct i j l k) :
    projection (d := d) (crossProposal i j l k h') =
      projection (crossProposal i j k l h) := by
  rw [crossProposal_swap_right i j k l h h', projection_reverse]

abbrev VertexPair (n : ℕ) := {a : Finset (Fin n) // a.card = 2}

def first (a : VertexPair n) : Fin n :=
  Classical.choose (Finset.card_eq_two.mp a.property)

def second (a : VertexPair n) : Fin n :=
  Classical.choose (Classical.choose_spec (Finset.card_eq_two.mp a.property))

theorem first_ne_second (a : VertexPair n) : first a ≠ second a :=
  (Classical.choose_spec (Classical.choose_spec (Finset.card_eq_two.mp a.property))).1

theorem pair_eq (a : VertexPair n) : a.val = {first a, second a} :=
  (Classical.choose_spec (Classical.choose_spec (Finset.card_eq_two.mp a.property))).2

theorem endpoints_cases (a : VertexPair n) (i j : Fin n) (h : a.val = {i, j}) :
    (first a = i ∧ second a = j) ∨ (first a = j ∧ second a = i) := by
  have hf : first a = i ∨ first a = j := by
    have hm : first a ∈ a.val := by rw [pair_eq]; simp
    simpa only [h, Finset.mem_insert, Finset.mem_singleton] using hm
  have hs : second a = i ∨ second a = j := by
    have hm : second a ∈ a.val := by rw [pair_eq]; simp
    simpa only [h, Finset.mem_insert, Finset.mem_singleton] using hm
  rcases hf with hf | hf <;> rcases hs with hs | hs
  · exact False.elim (first_ne_second a (hf.trans hs.symm))
  · exact Or.inl ⟨hf, hs⟩
  · exact Or.inr ⟨hf, hs⟩
  · exact False.elim (first_ne_second a (hf.trans hs.symm))

theorem endpoints_distinct (a b : VertexPair n) (h : Disjoint a.val b.val) :
    FourDistinct (first a) (second a) (first b) (second b) := by
  have hfirst (x : VertexPair n) : first x ∈ x.val := by rw [pair_eq]; simp
  have hsecond (x : VertexPair n) : second x ∈ x.val := by rw [pair_eq]; simp
  have hn := Finset.disjoint_left.mp h
  refine ⟨first_ne_second a, ?_, ?_, ?_, ?_, first_ne_second b⟩
  · intro he; exact hn (hfirst a) (he ▸ hfirst b)
  · intro he; exact hn (hfirst a) (he ▸ hsecond b)
  · intro he; exact hn (hsecond a) (he ▸ hfirst b)
  · intro he; exact hn (hsecond a) (he ▸ hsecond b)

def pairProposal (a b : VertexPair n) (h : Disjoint a.val b.val) : SwitchProposal n :=
  crossProposal (first a) (second a) (first b) (second b) (endpoints_distinct a b h)

theorem pairProposal_symm (a b : VertexPair n) (h : Disjoint a.val b.val) :
    pairProposal a b h = pairProposal b a h.symm :=
  crossProposal_swap_pairs _ _ _ _ _ _

theorem pairProposal_crosses_left (a b : VertexPair n) (h : Disjoint a.val b.val) :
    SwitchPairFiber.Crosses (pairProposal a b h) a.val := by
  rw [pair_eq a]
  exact crossProposal_left _ _ _ _ _

theorem pairProposal_crosses_right (a b : VertexPair n) (h : Disjoint a.val b.val) :
    SwitchPairFiber.Crosses (pairProposal a b h) b.val := by
  rw [pair_eq b]
  exact crossProposal_right _ _ _ _ _

def pairProjection (a b : VertexPair n) :
    PairResampling.StateSpace n d →L[ℝ] PairResampling.StateSpace n d :=
  if h : Disjoint a.val b.val then projection (pairProposal a b h) else 0

theorem pairProjection_of_disjoint (a b : VertexPair n) (h : Disjoint a.val b.val) :
    pairProjection (d := d) a b = projection (pairProposal a b h) := by
  simp [pairProjection, h]

theorem pairProjection_eq_explicit (a b : VertexPair n)
    (h : Disjoint a.val b.val) (i j k l : Fin n)
    (ha : a.val = {i, j}) (hb : b.val = {k, l}) (hf : FourDistinct i j k l) :
    pairProjection (d := d) a b = projection (crossProposal i j k l hf) := by
  rw [pairProjection_of_disjoint a b h]
  obtain (⟨hi, hj⟩ | ⟨hi, hj⟩) := endpoints_cases a i j ha
  all_goals obtain (⟨hk, hl⟩ | ⟨hk, hl⟩) := endpoints_cases b k l hb
  all_goals simp only [pairProposal, hi, hj, hk, hl]
  · exact crossProjection_swap_right i j k l hf _
  · exact crossProjection_swap_left i j k l hf _
  · have hm : FourDistinct j i k l :=
      ⟨hf.1.symm, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.1, hf.2.2.1, hf.2.2.2.2.2⟩
    rw [crossProjection_swap_right j i k l hm, crossProjection_swap_left i j k l hf]

theorem pairProjection_symm (a b : VertexPair n) :
    pairProjection (d := d) a b = pairProjection b a := by
  by_cases h : Disjoint a.val b.val
  · rw [pairProjection_of_disjoint a b h, pairProjection_of_disjoint b a h.symm,
      pairProposal_symm a b h]
  · have hr : ¬ Disjoint b.val a.val := fun hr => h hr.symm
    simp [pairProjection, h, hr]

theorem pairProjection_isSymmetric (a b : VertexPair n) :
    (pairProjection (d := d) a b).toLinearMap.IsSymmetric := by
  by_cases h : Disjoint a.val b.val
  · rw [pairProjection_of_disjoint a b h]
    exact projection_symmetric _
  · simp only [pairProjection, dite_eq_right h]
    intro f g
    simp

theorem pairProjection_idempotent (a b : VertexPair n)
    (f : PairResampling.StateSpace n d) :
    pairProjection a b (pairProjection a b f) = pairProjection a b f := by
  by_cases h : Disjoint a.val b.val
  · rw [pairProjection_of_disjoint a b h, projection_idempotent]
  · simp [pairProjection, h]

theorem pairProjection_mem_left_orthogonal (a b : VertexPair n)
    (f : PairResampling.StateSpace n d) :
    pairProjection a b f ∈ (PairResampling.fiberSpace n d a.val)ᗮ := by
  by_cases h : Disjoint a.val b.val
  · rw [pairProjection_of_disjoint a b h]
    exact projection_mem_orthogonal _ _ (pairProposal_crosses_left a b h) f
  · simp [pairProjection, h]

theorem pairProjection_mem_right_orthogonal (a b : VertexPair n)
    (f : PairResampling.StateSpace n d) :
    pairProjection a b f ∈ (PairResampling.fiberSpace n d b.val)ᗮ := by
  rw [pairProjection_symm a b]
  exact pairProjection_mem_left_orthogonal b a f

theorem pairProjection_mem_common (a b : VertexPair n)
    (f : PairResampling.StateSpace n d) :
    pairProjection a b f ∈
      (PairResampling.fiberSpace n d a.val ⊔ PairResampling.fiberSpace n d b.val)ᗮ := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [inner_add_left, pairProjection_mem_left_orthogonal a b f y hy,
    pairProjection_mem_right_orthogonal a b f z hz, add_zero]

theorem pairProjection_energy (a b : VertexPair n)
    (f : PairResampling.StateSpace n d) :
    ⟪f, pairProjection a b f⟫ = ‖pairProjection a b f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  have h := pairProjection_isSymmetric a b f (pairProjection a b f)
  change ⟪pairProjection a b f, pairProjection a b f⟫ =
    ⟪f, pairProjection a b (pairProjection a b f)⟫ at h
  simpa only [pairProjection_idempotent] using h.symm

end Problem315.CrossToggle

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/CrossTogglePairs.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairProjectionCell.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairResampling

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {d : Fin n → ℕ}

def restrictCell (C : GraphState n d → Prop) (f : StateSpace n d) : StateSpace n d :=
  WithLp.toLp 2 (fun G => if C G then f G else 0)

@[simp] theorem restrictCell_apply (C : GraphState n d → Prop)
    (f : StateSpace n d) (G : GraphState n d) :
    restrictCell C f G = if C G then f G else 0 := rfl

@[simp] theorem restrictCell_idempotent (C : GraphState n d → Prop)
    (f : StateSpace n d) : restrictCell C (restrictCell C f) = restrictCell C f := by
  ext G
  by_cases h : C G <;> simp [h]

@[simp] theorem restrictCell_sub (C : GraphState n d → Prop)
    (f g : StateSpace n d) : restrictCell C (f - g) = restrictCell C f - restrictCell C g := by
  ext G
  by_cases h : C G <;> simp [restrictCell, h]

def CellInvariant (a : Finset (Fin n)) (C : GraphState n d → Prop) : Prop :=
  ∀ G H, SameFiber a G.val H.val → (C G ↔ C H)

theorem expectation_restrictCell (a : Finset (Fin n))
    (C : GraphState n d → Prop) (hC : CellInvariant a C) (f : StateSpace n d) :
    expectation n d a (restrictCell C f) = restrictCell C (expectation n d a f) := by
  ext G
  rw [expectation_eq_average, restrictCell_apply]
  by_cases hG : C G
  · rw [ite_eq_left hG, expectation_eq_average]
    congr 1
    apply Finset.sum_congr rfl
    intro H hH
    have hH' : C H := (hC G H ((mem_fiberStates a G H).mp hH)).mp hG
    exact ite_eq_left hH'
  · rw [ite_eq_right hG]
    have hs : (∑ H ∈ fiberStates a G, restrictCell C f H) = 0 := by
      apply Finset.sum_eq_zero
      intro H hH
      have hH' : ¬ C H := fun hh => hG ((hC G H ((mem_fiberStates a G H).mp hH)).mpr hh)
      exact ite_eq_right hH'
    rw [hs, zero_div]

theorem fluctuation_restrictCell (a : Finset (Fin n))
    (C : GraphState n d → Prop) (hC : CellInvariant a C) (f : StateSpace n d) :
    fluctuation n d a (restrictCell C f) = restrictCell C (fluctuation n d a f) := by
  rw [fluctuation_eq_sub, expectation_restrictCell a C hC,
      fluctuation_eq_sub, restrictCell_sub]

theorem restrictCell_eq_self_iff (C : GraphState n d → Prop) (f : StateSpace n d) :
    restrictCell C f = f ↔ ∀ G, ¬ C G → f G = 0 := by
  constructor
  · intro h G hG
    have hh := congrArg (fun v : StateSpace n d => v G) h
    simpa [hG] using hh.symm
  · intro h
    ext G
    by_cases hG : C G
    · exact ite_eq_left hG
    · simp [hG, h G hG]

theorem expectation_preserves_cell_support (a : Finset (Fin n))
    (C : GraphState n d → Prop) (hC : CellInvariant a C) (f : StateSpace n d)
    (hf : ∀ G, ¬ C G → f G = 0) :
    ∀ G, ¬ C G → expectation n d a f G = 0 := by
  apply (restrictCell_eq_self_iff C _).mp
  rw [← expectation_restrictCell a C hC, (restrictCell_eq_self_iff C f).mpr hf]

theorem fluctuation_preserves_cell_support (a : Finset (Fin n))
    (C : GraphState n d → Prop) (hC : CellInvariant a C) (f : StateSpace n d)
    (hf : ∀ G, ¬ C G → f G = 0) :
    ∀ G, ¬ C G → fluctuation n d a f G = 0 := by
  apply (restrictCell_eq_self_iff C _).mp
  rw [← fluctuation_restrictCell a C hC, (restrictCell_eq_self_iff C f).mpr hf]

theorem restrictCell_inner (C : GraphState n d → Prop) (f g : StateSpace n d) :
    inner ℝ (restrictCell C f) g = inner ℝ f (restrictCell C g) := by
  rw [state_inner, state_inner]
  apply Finset.sum_congr rfl
  intro G hG
  by_cases h : C G <;> simp [h]

theorem sum_restrictCell {β : Type*} [Fintype β] (k : GraphState n d → β)
    (f : StateSpace n d) :
    (∑ b : β, restrictCell (fun G => k G = b) f) = f := by
  classical
  ext G
  simp [restrictCell]

theorem inner_eq_sum_cell_inner {β : Type*} [Fintype β]
    (k : GraphState n d → β) (f g : StateSpace n d) :
    inner ℝ f g = ∑ b : β,
      inner ℝ (restrictCell (fun G => k G = b) f)
        (restrictCell (fun G => k G = b) g) := by
  classical
  simp_rw [state_inner]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro G hG
  simp [restrictCell]

theorem norm_sq_eq_sum_cell_norm_sq {β : Type*} [Fintype β]
    (k : GraphState n d → β) (f : StateSpace n d) :
    ‖f‖ ^ 2 = ∑ b : β, ‖restrictCell (fun G => k G = b) f‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using inner_eq_sum_cell_inner k f f

theorem fluctuation_interaction_eq_sum_cells {β : Type*} [Fintype β]
    (k : GraphState n d → β) (a b : Finset (Fin n))
    (ha : ∀ c, CellInvariant a (fun G => k G = c))
    (hb : ∀ c, CellInvariant b (fun G => k G = c)) (f : StateSpace n d) :
    inner ℝ (fluctuation n d a f) (fluctuation n d b f) =
      ∑ c : β, inner ℝ (fluctuation n d a (restrictCell (fun G => k G = c) f))
        (fluctuation n d b (restrictCell (fun G => k G = c) f)) := by
  rw [inner_eq_sum_cell_inner k]
  apply Finset.sum_congr rfl
  intro c hc
  rw [fluctuation_restrictCell a _ (ha c), fluctuation_restrictCell b _ (hb c)]

end Problem315.PairResampling

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairProjectionCell.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/DisjointCellGlobal.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairResampling

attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem starProjection_restrictCell
    (M : Submodule ℝ (StateSpace n d)) (C : GraphState n d → Prop)
    (hM : ∀ f ∈ M, restrictCell C f ∈ M) (f : StateSpace n d) :
    M.starProjection (restrictCell C f) = restrictCell C (M.starProjection f) := by
  apply M.eq_starProjection_of_mem_of_inner_eq_zero
    (hM _ (M.starProjection_apply_mem f))
  intro w hw
  rw [← restrictCell_sub, restrictCell_inner]
  exact M.starProjection_inner_eq_zero f _ (hM w hw)

theorem map_norm_sq_eq_sum_cells {β : Type*} [Fintype β]
    (k : GraphState n d → β) (A : StateSpace n d → StateSpace n d)
    (hA : ∀ c f, A (restrictCell (fun G => k G = c) f) =
      restrictCell (fun G => k G = c) (A f)) (f : StateSpace n d) :
    ‖A f‖ ^ 2 = ∑ c : β, ‖A (restrictCell (fun G => k G = c) f)‖ ^ 2 := by
  simp_rw [hA]
  exact norm_sq_eq_sum_cell_norm_sq k (A f)

theorem starProjection_norm_sq_eq_sum_cells {β : Type*} [Fintype β]
    (k : GraphState n d → β) (M : Submodule ℝ (StateSpace n d))
    (hM : ∀ c f, f ∈ M → restrictCell (fun G => k G = c) f ∈ M)
    (f : StateSpace n d) :
    ‖M.starProjection f‖ ^ 2 =
      ∑ c : β, ‖M.starProjection (restrictCell (fun G => k G = c) f)‖ ^ 2 := by
  exact map_norm_sq_eq_sum_cells k M.starProjection
    (fun c f => starProjection_restrictCell M _ (hM c) f) f

theorem disjoint_interaction_of_cellwise {β : Type*} [Fintype β]
    (k : GraphState n d → β) (a b : Finset (Fin n))
    (ha : ∀ c, CellInvariant a (fun G => k G = c))
    (hb : ∀ c, CellInvariant b (fun G => k G = c))
    (g R S : StateSpace n d → StateSpace n d)
    (hg : ∀ c f, g (restrictCell (fun G => k G = c) f) =
      restrictCell (fun G => k G = c) (g f))
    (hR : ∀ c f, R (restrictCell (fun G => k G = c) f) =
      restrictCell (fun G => k G = c) (R f))
    (hS : ∀ c f, S (restrictCell (fun G => k G = c) f) =
      restrictCell (fun G => k G = c) (S f))
    (hlocal : ∀ c f, (∀ G, k G ≠ c → f G = 0) →
      2 * ‖g f‖ ^ 2 - ‖R f‖ ^ 2 - ‖S f‖ ^ 2 ≤
        2 * ⟪fluctuation n d a f, fluctuation n d b f⟫)
    (f : StateSpace n d) :
    2 * ‖g f‖ ^ 2 - ‖R f‖ ^ 2 - ‖S f‖ ^ 2 ≤
      2 * ⟪fluctuation n d a f, fluctuation n d b f⟫ := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
    hlocal c (restrictCell (fun G => k G = c) f)
      (by intro G hG; simp [hG]))
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  rw [← map_norm_sq_eq_sum_cells k g hg f,
    ← map_norm_sq_eq_sum_cells k R hR f,
    ← map_norm_sq_eq_sum_cells k S hS f,
    ← fluctuation_interaction_eq_sum_cells k a b ha hb f] at hsum
  exact hsum

end Problem315.PairResampling

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/DisjointCellGlobal.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/CrossToggleCells.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SwitchFlip

attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem projection_restrictCell_of_crosses (p : SwitchProposal n) (a : Finset (Fin n))
    (ha : SwitchPairFiber.Crosses p a) (C : GraphState n d → Prop)
    (hC : PairResampling.CellInvariant a C) (f : PairResampling.StateSpace n d) :
    projection p (PairResampling.restrictCell C f) =
      PairResampling.restrictCell C (projection p f) := by
  ext G
  have hCG : C G ↔ C (flip p G) := hC G (flip p G) (flip_sameFiber p a ha G)
  by_cases hG : C G
  · have hT := hCG.mp hG
    simp [projection_apply, PairResampling.restrictCell_apply, hG, hT]
  · have hT : ¬ C (flip p G) := fun h => hG (hCG.mpr h)
    simp [projection_apply, PairResampling.restrictCell_apply, hG, hT]

theorem projection_preserves_cell_support_of_crosses (p : SwitchProposal n) (a : Finset (Fin n))
    (ha : SwitchPairFiber.Crosses p a) (C : GraphState n d → Prop)
    (hC : PairResampling.CellInvariant a C) (f : PairResampling.StateSpace n d)
    (hf : ∀ G, ¬ C G → f G = 0) :
    ∀ G, ¬ C G → projection p f G = 0 := by
  apply (PairResampling.restrictCell_eq_self_iff C _).mp
  rw [← projection_restrictCell_of_crosses p a ha C hC,
    (PairResampling.restrictCell_eq_self_iff C f).mpr hf]

end Problem315.SwitchFlip

namespace Problem315.CrossToggle

attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem pairProjection_restrictCell (a b : VertexPair n)
    (C : GraphState n d → Prop) (hC : PairResampling.CellInvariant a.val C)
    (f : PairResampling.StateSpace n d) :
    pairProjection a b (PairResampling.restrictCell C f) =
      PairResampling.restrictCell C (pairProjection a b f) := by
  by_cases h : Disjoint a.val b.val
  · rw [pairProjection_of_disjoint a b h]
    exact SwitchFlip.projection_restrictCell_of_crosses _ _ (pairProposal_crosses_left a b h) C hC f
  · simp only [pairProjection, dite_eq_right h, zero_apply]
    ext G
    simp [PairResampling.restrictCell_apply]

theorem pairProjection_norm_sq_eq_sum_cells {β : Type*} [Fintype β]
    (k : GraphState n d → β) (a b : VertexPair n)
    (ha : ∀ c, PairResampling.CellInvariant a.val (fun G => k G = c))
    (f : PairResampling.StateSpace n d) :
    ‖pairProjection a b f‖ ^ 2 = ∑ c : β,
      ‖pairProjection a b (PairResampling.restrictCell (fun G => k G = c) f)‖ ^ 2 := by
  exact PairResampling.map_norm_sq_eq_sum_cells k (pairProjection a b)
    (fun c g => pairProjection_restrictCell a b _ (ha c) g) f

end Problem315.CrossToggle

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/CrossToggleCells.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/CrossToggleGain.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.CrossToggle

attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

def gain (a b : Finset (Fin n)) :
    PairResampling.StateSpace n d →L[ℝ] PairResampling.StateSpace n d :=
  if ha : a.card = 2 then
    if hb : b.card = 2 then pairProjection ⟨a, ha⟩ ⟨b, hb⟩ else 0
  else 0

theorem gain_of_pairs (a b : Finset (Fin n)) (ha : a.card = 2) (hb : b.card = 2) :
    gain (d := d) a b = pairProjection ⟨a, ha⟩ ⟨b, hb⟩ := by
  simp [gain, ha, hb]

theorem gain_pair_eq (i j k l : Fin n) (h : FourDistinct i j k l) :
    gain (d := d) {i,j} {k,l} = SwitchFlip.projection (crossProposal i j k l h) := by
  have ha : ({i,j} : Finset (Fin n)).card = 2 := by simp [h.1]
  have hb : ({k,l} : Finset (Fin n)).card = 2 := by simp [h.2.2.2.2.2]
  have hd : Disjoint ({i,j} : Finset (Fin n)) {k,l} := by
    simp [Finset.disjoint_left, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1]
  rw [gain_of_pairs _ _ ha hb]
  exact pairProjection_eq_explicit ⟨_,ha⟩ ⟨_,hb⟩ hd i j k l rfl rfl h

theorem gain_pair_apply (i j k l : Fin n) (h : FourDistinct i j k l)
    (f : PairResampling.StateSpace n d) (G : GraphState n d) :
    gain {i,j} {k,l} f G =
      (f G - f (SwitchFlip.flip (crossProposal i j k l h) G)) / 2 := by
  rw [gain_pair_eq i j k l h, SwitchFlip.projection_apply]

theorem norm_gain_pair_sq (i j k l : Fin n) (h : FourDistinct i j k l)
    (f : PairResampling.StateSpace n d) :
    ‖gain {i,j} {k,l} f‖ ^ 2 = (1 / 4 : ℝ) *
      ∑ G : GraphState n d, (f G - f (SwitchFlip.flip (crossProposal i j k l h) G)) ^ 2 := by
  rw [gain_pair_eq i j k l h]
  exact SwitchFlip.norm_projection_sq _ f

theorem gain_symm (a b : Finset (Fin n)) : gain (d := d) a b = gain b a := by
  by_cases ha : a.card = 2 <;> by_cases hb : b.card = 2
  · rw [gain_of_pairs a b ha hb, gain_of_pairs b a hb ha, pairProjection_symm]
  all_goals simp [gain, ha, hb]

theorem gain_eq_zero_of_not_disjoint (a b : Finset (Fin n)) (h : ¬ Disjoint a b) :
    gain (d := d) a b = 0 := by
  by_cases ha : a.card = 2 <;> by_cases hb : b.card = 2 <;>
    simp [gain, ha, hb, pairProjection, h]

theorem gain_pair_eq_ordered (i j k l : Fin n) :
    gain (d := d) {i,j} {k,l} =
      if h : FourDistinct i k l j then
        SwitchFlip.projection (fourVertexProposal i k l j h) else 0 := by
  by_cases h : FourDistinct i k l j
  · rw [dite_eq_left h]
    have h' : FourDistinct i j k l :=
      ⟨h.2.2.1, h.1, h.2.1, h.2.2.2.2.1.symm,
        h.2.2.2.2.2.symm, h.2.2.2.1⟩
    rw [gain_pair_eq i j k l h']
    rfl
  · rw [dite_eq_right h]
    by_cases hij : i = j
    · subst j
      simp [gain]
    by_cases hkl : k = l
    · subst l
      simp [gain]
    apply gain_eq_zero_of_not_disjoint
    intro hd
    apply h
    have hik : i ≠ k := by
      intro e
      exact Finset.disjoint_left.mp hd (show i ∈ ({i,j} : Finset (Fin n)) by simp)
        (by simp [← e])
    have hil : i ≠ l := by
      intro e
      exact Finset.disjoint_left.mp hd (show i ∈ ({i,j} : Finset (Fin n)) by simp)
        (by simp [← e])
    have hjk : j ≠ k := by
      intro e
      exact Finset.disjoint_left.mp hd (show j ∈ ({i,j} : Finset (Fin n)) by simp)
        (by simp [← e])
    have hjl : j ≠ l := by
      intro e
      exact Finset.disjoint_left.mp hd (show j ∈ ({i,j} : Finset (Fin n)) by simp)
        (by simp [← e])
    exact ⟨hik, hil, hij, hkl, hjk.symm, hjl.symm⟩

theorem gain_idempotent (a b : Finset (Fin n)) (f : PairResampling.StateSpace n d) :
    gain a b (gain a b f) = gain a b f := by
  by_cases ha : a.card = 2 <;> by_cases hb : b.card = 2
  · rw [gain_of_pairs a b ha hb, pairProjection_idempotent]
  all_goals simp [gain, ha, hb]

theorem gain_isSymmetric (a b : Finset (Fin n)) :
    (gain (d := d) a b).toLinearMap.IsSymmetric := by
  by_cases ha : a.card = 2 <;> by_cases hb : b.card = 2
  · rw [gain_of_pairs a b ha hb]
    exact pairProjection_isSymmetric _ _
  all_goals
    intro f g
    simp [gain, ha, hb]

theorem gain_expectation_left (a b : Finset (Fin n))
    (f : PairResampling.StateSpace n d) :
    gain a b (PairResampling.expectation n d a f) = 0 := by
  by_cases ha : a.card = 2 <;> by_cases hb : b.card = 2
  · rw [gain_of_pairs a b ha hb]
    by_cases h : Disjoint a b
    · rw [pairProjection_of_disjoint _ _ h]
      exact SwitchFlip.projection_expectation _ a
        (pairProposal_crosses_left ⟨a,ha⟩ ⟨b,hb⟩ h) f
    · simp [pairProjection, h]
  all_goals simp [gain, ha, hb]

theorem gain_expectation_right (a b : Finset (Fin n))
    (f : PairResampling.StateSpace n d) :
    gain a b (PairResampling.expectation n d b f) = 0 := by
  rw [gain_symm a b]
  exact gain_expectation_left b a f

theorem gain_mem_common (a b : Finset (Fin n)) (f : PairResampling.StateSpace n d) :
    gain a b f ∈ (PairResampling.fiberSpace n d a ⊔
      PairResampling.fiberSpace n d b)ᗮ := by
  by_cases ha : a.card = 2 <;> by_cases hb : b.card = 2
  · rw [gain_of_pairs a b ha hb]
    exact pairProjection_mem_common ⟨a, ha⟩ ⟨b, hb⟩ f
  all_goals simp [gain, ha, hb]

theorem gain_norm_le_common (a b : Finset (Fin n)) (f : PairResampling.StateSpace n d) :
    ‖gain a b f‖ ≤ ‖(PairResampling.fiberSpace n d a ⊔
      PairResampling.fiberSpace n d b)ᗮ.starProjection f‖ := by
  by_cases ha : a.card = 2 <;> by_cases hb : b.card = 2
  · rw [gain_of_pairs a b ha hb]
    by_cases h : Disjoint a b
    · rw [pairProjection_of_disjoint _ _ h]
      exact SwitchFlip.norm_projection_le_jointOrthogonal _ a b
        (pairProposal_crosses_left ⟨a, ha⟩ ⟨b, hb⟩ h)
        (pairProposal_crosses_right ⟨a, ha⟩ ⟨b, hb⟩ h) f
    · simp only [pairProjection, dite_eq_right h, zero_apply, norm_zero]
      exact norm_nonneg _
  all_goals simp [gain, ha, hb]

theorem gain_restrictCell (a b : Finset (Fin n)) (C : GraphState n d → Prop)
    (hC : PairResampling.CellInvariant a C) (f : PairResampling.StateSpace n d) :
    gain a b (PairResampling.restrictCell C f) =
      PairResampling.restrictCell C (gain a b f) := by
  by_cases ha : a.card = 2 <;> by_cases hb : b.card = 2
  · rw [gain_of_pairs a b ha hb]
    exact pairProjection_restrictCell ⟨a, ha⟩ ⟨b, hb⟩ C hC f
  all_goals
    ext G
    simp [gain, ha, hb, PairResampling.restrictCell_apply]

end Problem315.CrossToggle

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/CrossToggleGain.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairFiberBridge.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairFiber
attribute [local instance] Classical.propDecidable

variable {n : Nat}

theorem expectation_eq_assignment_average {d : Fin n → Nat}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (f : PairResampling.StateSpace n d) :
    PairResampling.expectation n d {i, j} f G =
      (∑ T : Assignment G.val i j, f ((stateFiberEquiv G i j hij).symm T).val) /
        (Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card : ℝ) := by
  classical
  rw [PairResampling.expectation_eq_average, fiberStates_card G i j hij]
  congr 1
  rw [← Finset.sum_coe_sort]
  exact ((resamplingFiberEquiv G i j hij).symm.sum_comp
    (fun H : (PairResampling.fiberStates {i, j} G) => f H.val)).symm

end Problem315.PairFiber

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairFiberBridge.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairFiberOrientation.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairFiber
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

@[simp] theorem singletonSet_swap (G : SimpleGraph V) (i j : V) :
    singletonSet G j i = singletonSet G i j := by
  ext w
  simp only [mem_singletonSet, Outside, Xor]
  tauto

theorem leftSet_swap (G : SimpleGraph V) (i j : V) :
    leftSet G j i = singletonSet G i j \ leftSet G i j := by
  classical
  ext w
  simp only [mem_leftSet, Finset.mem_sdiff, mem_singletonSet, Outside, Xor]
  tauto

theorem leftSet_card_swap (G : SimpleGraph V) (i j : V) :
    (leftSet G j i).card = (singletonSet G i j).card - (leftSet G i j).card := by
  classical
  rw [leftSet_swap, Finset.card_sdiff_of_subset (leftSet_subset_singletonSet G i j)]

def assignmentReverse (G : SimpleGraph V) (i j : V) :
    Assignment G i j ≃ Assignment G j i where
  toFun T := ⟨singletonSet G i j \ T.val, by
    constructor
    · exact (Finset.sdiff_subset).trans (singletonSet_swap G i j).symm.subset
    · rw [Finset.card_sdiff_of_subset T.property.1, T.property.2]
      exact (leftSet_card_swap G i j).symm⟩
  invFun T := ⟨singletonSet G j i \ T.val, by
    constructor
    · exact (Finset.sdiff_subset).trans (singletonSet_swap G i j).subset
    · rw [Finset.card_sdiff_of_subset T.property.1, T.property.2]
      exact (leftSet_card_swap G j i).symm⟩
  left_inv T := by
    apply Subtype.ext
    change singletonSet G j i \ (singletonSet G i j \ T.val) = T.val
    rw [singletonSet_swap]
    exact Finset.sdiff_sdiff_eq_self T.property.1
  right_inv T := by
    apply Subtype.ext
    change singletonSet G i j \ (singletonSet G j i \ T.val) = T.val
    rw [← singletonSet_swap G i j]
    exact Finset.sdiff_sdiff_eq_self T.property.1

@[simp] theorem assignmentReverse_val (G : SimpleGraph V) (i j : V)
    (T : Assignment G i j) :
    (assignmentReverse G i j T).val = singletonSet G i j \ T.val := rfl

theorem trade_reverse (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (T : Assignment G i j) :
    trade G j i hij.symm (assignmentReverse G i j T).val
      (assignmentReverse G i j T).property.1 =
      trade G i j hij T.val T.property.1 := by
  apply graph_eq_of_key_leftSet_eq (i := j) (j := i)
  · calc
      key j i _ = key j i G := key_trade _ _ _ _ _ _
      _ = key i j G := key_swap G j i
      _ = key i j _ := (key_trade G i j hij T.val T.property.1).symm
      _ = key j i _ := key_swap _ i j
  · simp only [leftSet_trade, assignmentReverse_val,
      leftSet_swap (trade G i j hij T.val T.property.1) i j,
      singletonSet_eq_of_key_eq (key_trade G i j hij T.val T.property.1)]

theorem assignment_equal_reverse (G : SimpleGraph V) (i j k l : V)
    (hk : k ∈ singletonSet G i j) (hl : l ∈ singletonSet G i j)
    (T : Assignment G i j) :
    (k ∈ (assignmentReverse G i j T).val ↔ l ∈ (assignmentReverse G i j T).val) ↔
      (k ∈ T.val ↔ l ∈ T.val) := by
  simp only [assignmentReverse_val, Finset.mem_sdiff, hk, hl, true_and]
  tauto

theorem singleton_adj_equal_swap (G : SimpleGraph V) (i j k l : V)
    (hk : k ∈ singletonSet G i j) (hl : l ∈ singletonSet G i j) :
    (G.Adj i k ↔ G.Adj i l) ↔ (G.Adj j k ↔ G.Adj j l) := by
  have hk' := (mem_singletonSet G i j k).mp hk
  have hl' := (mem_singletonSet G i j l).mp hl
  simp only [Xor] at hk' hl'
  tauto

theorem singleton_equality_indicator_swap (G : SimpleGraph V) (i j k l : V) :
    (if k ∈ singletonSet G i j ∧ l ∈ singletonSet G i j then
      if G.Adj i k ↔ G.Adj i l then (1 : ℝ) else 0 else 0) =
    (if k ∈ singletonSet G j i ∧ l ∈ singletonSet G j i then
      if G.Adj j k ↔ G.Adj j l then (1 : ℝ) else 0 else 0) := by
  simp only [singletonSet_swap]
  by_cases h : k ∈ singletonSet G i j ∧ l ∈ singletonSet G i j
  · simp only [h, singleton_adj_equal_swap G i j k l h.1 h.2]
  · simp only [h, ite_false]

theorem stateFiberEquiv_reverse {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (T : Assignment G.val i j) :
    ((stateFiberEquiv G j i hij.symm).symm
      (assignmentReverse G.val i j T)).val =
      ((stateFiberEquiv G i j hij).symm T).val := by
  apply Subtype.ext
  exact trade_reverse G.val i j hij T

theorem sum_assignment_reverse {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (f : GraphState n d → ℝ) :
    (∑ T : Assignment G.val j i, f ((stateFiberEquiv G j i hij.symm).symm T).val) =
      ∑ T : Assignment G.val i j, f ((stateFiberEquiv G i j hij).symm T).val := by
  classical
  rw [← (assignmentReverse G.val i j).sum_comp]
  apply Finset.sum_congr rfl
  intro T _
  rw [stateFiberEquiv_reverse]

end Problem315.PairFiber

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairFiberOrientation.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairEqualityProjection.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

def observable (i k l : Fin n) : StateSpace n d :=
  WithLp.toLp 2 (fun G => if G.val.Adj i k ↔ G.val.Adj i l then 1 else 0)

def centered (i j k l : Fin n) : StateSpace n d :=
  fluctuation n d {i,j} (observable i k l)

def active (i j k l : Fin n) (G : GraphState n d) : Prop :=
  k ∈ singletonSet G.val i j ∧ l ∈ singletonSet G.val i j

def equalitySpace (i j k l : Fin n) : Submodule ℝ (StateSpace n d) where
  carrier := {f | ∀ G : GraphState n d, ∃ c : ℝ,
    ∀ H : GraphState n d, SameFiber {i,j} G.val H.val →
      f H = c * (if active i j k l G then centered i j k l H else 0)}
  zero_mem' := by
    intro G
    exact ⟨0, fun H h => by simp⟩
  add_mem' := by
    intro f g hf hg G
    obtain ⟨c,hc⟩ := hf G
    obtain ⟨e,he⟩ := hg G
    refine ⟨c+e, fun H h => ?_⟩
    change f H + g H = _
    rw [hc H h, he H h, add_mul]
  smul_mem' := by
    intro c f hf G
    obtain ⟨e,he⟩ := hf G
    refine ⟨c*e, fun H h => ?_⟩
    change c * f H = _
    rw [he H h, mul_assoc]

def projection (i j k l : Fin n) : StateSpace n d →L[ℝ] StateSpace n d :=
  (equalitySpace i j k l).starProjection

@[simp] theorem projection_eq_self_iff (i j k l : Fin n) (f : StateSpace n d) :
    projection i j k l f = f ↔ f ∈ equalitySpace i j k l :=
  Submodule.starProjection_eq_self_iff

def crossTotal (i j k l : Fin n) (G : GraphState n d) : ℕ :=
  edgeBit G.val i k + edgeBit G.val j k +
    (edgeBit G.val i l + edgeBit G.val j l)

theorem active_sameFiber (i j k l : Fin n) (hij : i ≠ j)
    {G H : GraphState n d} (h : SameFiber {i,j} G.val H.val) :
    active i j k l G ↔ active i j k l H := by
  have hh := singletonSet_eq_of_key_eq ((sameFiber_iff_key_eq i j hij G.val H.val).mp h)
  unfold active
  rw [hh]

theorem crossTotal_sameFiber (i j k l : Fin n) (hij : i ≠ j)
    {G H : GraphState n d} (h : SameFiber {i,j} G.val H.val) :
    crossTotal i j k l G = crossTotal i j k l H := by
  have hh := (sameFiber_iff_key_eq i j hij G.val H.val).mp h
  exact congrArg₂ (· + ·) (key_count hh k) (key_count hh l)

theorem observable_zero_of_inactive (i j k l : Fin n)
    (hk : Outside i j k) (hl : Outside i j l) (G : GraphState n d)
    (ht : crossTotal i j k l G = 2) (ha : ¬ active i j k l G) :
    observable i k l G = 0 := by
  unfold crossTotal at ht
  simp only [active, mem_singletonSet, hk, hl, true_and] at ha
  change (if G.val.Adj i k ↔ G.val.Adj i l then (1:ℝ) else 0) = 0
  by_cases hik : G.val.Adj i k <;> by_cases hjk : G.val.Adj j k <;>
    by_cases hil : G.val.Adj i l <;> by_cases hjl : G.val.Adj j l <;>
    simp_all [edgeBit, Xor]

theorem centered_zero_of_inactive (i j k l : Fin n) (hij : i ≠ j)
    (hk : Outside i j k) (hl : Outside i j l) (G : GraphState n d)
    (ht : crossTotal i j k l G = 2) (ha : ¬ active i j k l G) :
    centered i j k l G = 0 := by
  unfold centered
  rw [fluctuation_eq_sub]
  change observable i k l G - expectation n d {i,j} (observable i k l) G = 0
  rw [observable_zero_of_inactive i j k l hk hl G ht ha, expectation_eq_average]
  have hz : (∑ H ∈ fiberStates {i,j} G, observable i k l H) = 0 := by
    apply Finset.sum_eq_zero
    intro H hH
    have h := (mem_fiberStates {i,j} G H).mp hH
    apply observable_zero_of_inactive i j k l hk hl H
    · rw [← crossTotal_sameFiber i j k l hij h]
      exact ht
    · exact fun hA => ha ((active_sameFiber i j k l hij h).mpr hA)
  rw [hz]
  simp

def multiply (f g : StateSpace n d) : StateSpace n d :=
  WithLp.toLp 2 (fun G => f G * g G)

theorem expectation_multiply (a : Finset (Fin n)) (w f : StateSpace n d)
    (hw : w ∈ fiberSpace n d a) :
    expectation n d a (multiply w f) = multiply w (expectation n d a f) := by
  ext G
  rw [expectation_eq_average]
  change (∑ H ∈ fiberStates a G, w H * f H) / _ =
    w G * expectation n d a f G
  rw [expectation_eq_average]
  have heq : (∑ H ∈ fiberStates a G, w H * f H) =
      w G * ∑ H ∈ fiberStates a G, f H := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro H hH
    rw [hw H G ((mem_fiberStates a G H).mp hH).symm]
  rw [heq, mul_div_assoc]

theorem fluctuation_multiply (a : Finset (Fin n)) (w f : StateSpace n d)
    (hw : w ∈ fiberSpace n d a) :
    fluctuation n d a (multiply w f) = multiply w (fluctuation n d a f) := by
  rw [fluctuation_eq_sub, expectation_multiply a w f hw, fluctuation_eq_sub]
  ext G
  change w G * f G - w G * expectation n d a f G =
    w G * (f G - expectation n d a f G)
  ring

theorem multiply_centered_mem (i j k l : Fin n) (hij : i ≠ j)
    (hk : Outside i j k) (hl : Outside i j l) (w : StateSpace n d)
    (hw : w ∈ fiberSpace n d {i,j})
    (hsupport : ∀ G : GraphState n d, crossTotal i j k l G ≠ 2 → w G = 0) :
    multiply w (centered i j k l) ∈ equalitySpace i j k l := by
  intro G
  refine ⟨w G, fun H h => ?_⟩
  change w H * centered i j k l H = _
  rw [hw H G h.symm]
  by_cases ha : active i j k l G
  · simp only [ite_eq_left ha]
  · simp only [ite_eq_right ha, mul_zero]
    by_cases ht : crossTotal i j k l G = 2
    · have hH : crossTotal i j k l H = 2 :=
        (crossTotal_sameFiber i j k l hij h).symm.trans ht
      have hA : ¬ active i j k l H :=
        fun hA => ha ((active_sameFiber i j k l hij h).mpr hA)
      rw [centered_zero_of_inactive i j k l hij hk hl H hH hA, mul_zero]
    · rw [hsupport G ht, zero_mul]

theorem fluctuation_weighted_observable_mem (i j k l : Fin n) (hij : i ≠ j)
    (hk : Outside i j k) (hl : Outside i j l) (w : StateSpace n d)
    (hw : w ∈ fiberSpace n d {i,j})
    (hsupport : ∀ G : GraphState n d, crossTotal i j k l G ≠ 2 → w G = 0) :
    fluctuation n d {i,j} (multiply w (observable i k l)) ∈
      equalitySpace i j k l := by
  rw [fluctuation_multiply _ _ _ hw]
  exact multiply_centered_mem i j k l hij hk hl w hw hsupport

theorem fluctuation_weighted_centered_flag_mem (i j k l : Fin n) (hij : i ≠ j)
    (hk : Outside i j k) (hl : Outside i j l) (w : StateSpace n d) (c : ℝ)
    (hw : w ∈ fiberSpace n d {i,j})
    (hsupport : ∀ G : GraphState n d, crossTotal i j k l G ≠ 2 → w G = 0) :
    fluctuation n d {i,j}
      (multiply w (observable i k l - WithLp.toLp 2 (fun _ => c))) ∈
      equalitySpace i j k l := by
  rw [fluctuation_multiply _ _ _ hw, map_sub,
    (fluctuation_eq_zero_iff _ _).mpr (constant_mem _ c), sub_zero]
  exact multiply_centered_mem i j k l hij hk hl w hw hsupport

theorem projection_fixes_weighted_flag_fluctuation
    (i j k l : Fin n) (hij : i ≠ j)
    (hk : Outside i j k) (hl : Outside i j l) (w : StateSpace n d) (c : ℝ)
    (hw : w ∈ fiberSpace n d {i,j})
    (hsupport : ∀ G : GraphState n d, crossTotal i j k l G ≠ 2 → w G = 0) :
    projection i j k l (fluctuation n d {i,j}
      (multiply w (observable i k l - WithLp.toLp 2 (fun _ => c)))) =
      fluctuation n d {i,j}
        (multiply w (observable i k l - WithLp.toLp 2 (fun _ => c))) := by
  exact (projection_eq_self_iff _ _ _ _ _).mpr
    (fluctuation_weighted_centered_flag_mem i j k l hij hk hl w c hw hsupport)

theorem line_projection_norm_le (i j k l : Fin n) (z f : StateSpace n d)
    (hz : z ∈ equalitySpace i j k l) :
    ‖(Submodule.span ℝ {z}).starProjection f‖ ≤ ‖projection i j k l f‖ := by
  have hle : Submodule.span ℝ {z} ≤ equalitySpace i j k l := by
    rw [Submodule.span_le]
    intro x hx
    have hxz : x = z := Set.mem_singleton_iff.mp hx
    subst x
    exact hz
  have hcomp := Submodule.starProjection_comp_starProjection_of_le hle
  have heq := congrArg (fun A : StateSpace n d →L[ℝ] StateSpace n d => A f) hcomp
  change (Submodule.span ℝ {z}).starProjection (projection i j k l f) =
    (Submodule.span ℝ {z}).starProjection f at heq
  rw [← heq]
  exact (Submodule.span ℝ {z}).norm_starProjection_apply_le _

end Problem315.PairEquality

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairEqualityProjection.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairEqualityOrientation.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

@[simp] theorem observable_swap_right (i k l : Fin n) :
    observable (d := d) i l k = observable i k l := by
  ext G
  change (if G.val.Adj i l ↔ G.val.Adj i k then (1 : ℝ) else 0) =
    if G.val.Adj i k ↔ G.val.Adj i l then 1 else 0
  simp only [iff_comm]

@[simp] theorem centered_swap_right (i j k l : Fin n) :
    centered (d := d) i j l k = centered i j k l := by
  simp only [centered, observable_swap_right]

@[simp] theorem active_swap_left (i j k l : Fin n) (G : GraphState n d) :
    active j i k l G ↔ active i j k l G := by
  simp only [active, singletonSet_swap]

@[simp] theorem active_swap_right (i j k l : Fin n) (G : GraphState n d) :
    active i j l k G ↔ active i j k l G := by
  exact and_comm

theorem observable_eq_of_active (i j k l : Fin n) (G : GraphState n d)
    (ha : active i j k l G) : observable i k l G = observable j k l G := by
  change (if G.val.Adj i k ↔ G.val.Adj i l then (1 : ℝ) else 0) =
    if G.val.Adj j k ↔ G.val.Adj j l then 1 else 0
  simp only [singleton_adj_equal_swap G.val i j k l ha.1 ha.2]

theorem centered_eq_of_active (i j k l : Fin n) (hij : i ≠ j)
    (G : GraphState n d) (ha : active i j k l G) :
    centered i j k l G = centered j i k l G := by
  unfold centered
  rw [fluctuation_eq_sub, fluctuation_eq_sub]
  change observable i k l G - expectation n d {i,j} (observable i k l) G =
    observable j k l G - expectation n d {j,i} (observable j k l) G
  rw [observable_eq_of_active i j k l G ha, Finset.pair_comm j i]
  congr 1
  rw [expectation_eq_average, expectation_eq_average]
  congr 1
  apply Finset.sum_congr rfl
  intro H hH
  exact observable_eq_of_active i j k l H
    ((active_sameFiber i j k l hij ((mem_fiberStates {i,j} G H).mp hH)).mp ha)

theorem gated_centered_swap_left (i j k l : Fin n) (hij : i ≠ j)
    (G H : GraphState n d) (h : SameFiber {i,j} G.val H.val) :
    (if active i j k l G then centered i j k l H else 0) =
      (if active j i k l G then centered j i k l H else 0) := by
  simp only [active_swap_left]
  by_cases ha : active i j k l G
  · simp only [ite_eq_left ha]
    exact centered_eq_of_active i j k l hij H ((active_sameFiber i j k l hij h).mp ha)
  · simp only [ite_eq_right ha]

theorem equalitySpace_le_swap_left (i j k l : Fin n) (hij : i ≠ j) :
    equalitySpace (d := d) i j k l ≤ equalitySpace j i k l := by
  intro f hf G
  obtain ⟨c,hc⟩ := hf G
  refine ⟨c, fun H h => ?_⟩
  have h' : SameFiber {i,j} G.val H.val := by
    simpa only [Finset.pair_comm j i] using h
  rw [hc H h', gated_centered_swap_left i j k l hij G H h']

theorem equalitySpace_swap_left (i j k l : Fin n) (hij : i ≠ j) :
    equalitySpace (d := d) i j k l = equalitySpace j i k l :=
  le_antisymm (equalitySpace_le_swap_left i j k l hij)
    (equalitySpace_le_swap_left j i k l hij.symm)

theorem equalitySpace_swap_right (i j k l : Fin n) :
    equalitySpace (d := d) i j k l = equalitySpace i j l k := by
  ext f
  simp only [equalitySpace, Submodule.mem_mk,
    active_swap_right, centered_swap_right]

theorem projection_swap_left (i j k l : Fin n) (hij : i ≠ j) :
    projection (d := d) i j k l = projection j i k l := by
  exact congrArg (fun M : Submodule ℝ (StateSpace n d) => M.starProjection)
    (equalitySpace_swap_left i j k l hij)

theorem projection_swap_right (i j k l : Fin n) :
    projection (d := d) i j k l = projection i j l k := by
  exact congrArg (fun M : Submodule ℝ (StateSpace n d) => M.starProjection)
    (equalitySpace_swap_right i j k l)

theorem projection_eq_of_left_pair_eq (i j i' j' k l : Fin n) (hij : i ≠ j)
    (h : ({i,j} : Finset (Fin n)) = {i',j'}) :
    projection (d := d) i j k l = projection i' j' k l := by
  have hs : ({i,j} : Set (Fin n)) = {i',j'} := by
    simpa only [Finset.coe_pair] using congrArg (fun a : Finset (Fin n) => (a : Set (Fin n))) h
  rcases Set.pair_eq_pair_iff.mp hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rfl
  · exact projection_swap_left _ _ _ _ hij

theorem projection_eq_of_right_pair_eq (i j k l k' l' : Fin n)
    (h : ({k,l} : Finset (Fin n)) = {k',l'}) :
    projection (d := d) i j k l = projection i j k' l' := by
  have hs : ({k,l} : Set (Fin n)) = {k',l'} := by
    simpa only [Finset.coe_pair] using congrArg (fun a : Finset (Fin n) => (a : Set (Fin n))) h
  rcases Set.pair_eq_pair_iff.mp hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rfl
  · exact projection_swap_right _ _ _ _

end Problem315.PairEquality

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairEqualityOrientation.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairEqualityUnordered.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem equalitySpace_eq_bot_of_inactive (i j k l : Fin n)
    (h : ∀ G : GraphState n d, ¬ active i j k l G) :
    equalitySpace (d := d) i j k l = ⊥ := by
  apply le_antisymm
  · intro f hf
    change f = 0
    ext G
    change f G = 0
    obtain ⟨c, hc⟩ := hf G
    have he := hc G (SameFiber.refl _ _)
    simpa only [ite_eq_right (h G), mul_zero] using he
  · exact bot_le

theorem projection_eq_zero_of_not_disjoint (i j k l : Fin n)
    (h : ¬ Disjoint ({i,j} : Finset (Fin n)) {k,l}) :
    projection (d := d) i j k l = 0 := by
  have hinactive : ∀ G : GraphState n d, ¬ active i j k l G := by
    intro G ha
    obtain ⟨v,hv,hv'⟩ := Finset.not_disjoint_iff.mp h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv hv'
    have hk := ((mem_singletonSet G.val i j k).mp ha.1).1
    have hl := ((mem_singletonSet G.val i j l).mp ha.2).1
    rcases hv with rfl | rfl <;> rcases hv' with hv' | hv'
    · exact hk.1 hv'.symm
    · exact hl.1 hv'.symm
    · exact hk.2 hv'.symm
    · exact hl.2 hv'.symm
  have he := congrArg (fun M : Submodule ℝ (StateSpace n d) => M.starProjection)
    (equalitySpace_eq_bot_of_inactive i j k l hinactive)
  exact he.trans Submodule.starProjection_bot

private theorem exists_pair_endpoints (a : Finset (Fin n)) (ha : a.card = 2) :
    ∃ p : Fin n × Fin n, p.1 ≠ p.2 ∧ a = {p.1,p.2} := by
  obtain ⟨i,j,hij,hpair⟩ := Finset.card_eq_two.mp ha
  exact ⟨(i,j),hij,hpair⟩

private def endpoints (a : Finset (Fin n)) (ha : a.card = 2) : Fin n × Fin n :=
  Classical.choose (exists_pair_endpoints a ha)

private theorem endpoints_spec (a : Finset (Fin n)) (ha : a.card = 2) :
    (endpoints a ha).1 ≠ (endpoints a ha).2 ∧
      a = {(endpoints a ha).1,(endpoints a ha).2} :=
  Classical.choose_spec (exists_pair_endpoints a ha)

def pairProjection (a b : Finset (Fin n)) : StateSpace n d →L[ℝ] StateSpace n d :=
  if ha : a.card = 2 then
    if hb : b.card = 2 then
      projection (endpoints a ha).1 (endpoints a ha).2
        (endpoints b hb).1 (endpoints b hb).2
    else 0
  else 0

theorem pairProjection_eq (a b : Finset (Fin n))
    (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (ha : a = {i,j}) (hb : b = {k,l}) :
    pairProjection (d := d) a b = projection i j k l := by
  have hca : a.card = 2 := by rw [ha]; simp [hij]
  have hcb : b.card = 2 := by rw [hb]; simp [hkl]
  rw [pairProjection, dite_eq_left hca, dite_eq_left hcb]
  have hpa := endpoints_spec a hca
  have hpb := endpoints_spec b hcb
  calc
    _ = projection i j (endpoints b hcb).1 (endpoints b hcb).2 :=
      projection_eq_of_left_pair_eq _ _ _ _ _ _ hpa.1 (hpa.2.symm.trans ha)
    _ = _ := projection_eq_of_right_pair_eq _ _ _ _ _ _ (hpb.2.symm.trans hb)

@[simp] theorem pairProjection_pair (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l) :
    pairProjection (d := d) {i,j} {k,l} = projection i j k l :=
  pairProjection_eq _ _ i j k l hij hkl rfl rfl

@[simp] theorem pairProjection_eq_zero_left (a b : Finset (Fin n))
    (ha : a.card ≠ 2) : pairProjection (d := d) a b = 0 := by
  simp only [pairProjection, dite_eq_right ha]

@[simp] theorem pairProjection_eq_zero_right (a b : Finset (Fin n))
    (hb : b.card ≠ 2) : pairProjection (d := d) a b = 0 := by
  unfold pairProjection
  split_ifs <;> rfl

theorem pairProjection_eq_zero_of_not_disjoint (a b : Finset (Fin n))
    (hab : ¬ Disjoint a b) : pairProjection (d := d) a b = 0 := by
  by_cases ha : a.card = 2
  · by_cases hb : b.card = 2
    · obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp ha
      obtain ⟨k,l,hkl,rfl⟩ := Finset.card_eq_two.mp hb
      rw [pairProjection_pair i j k l hij hkl]
      exact projection_eq_zero_of_not_disjoint i j k l hab
    · exact pairProjection_eq_zero_right a b hb
  · exact pairProjection_eq_zero_left a b ha

theorem sum_pairProjection_norm_sq (a : Finset (Fin n))
    (s : Finset (Finset (Fin n))) (f : StateSpace n d) :
    (∑ b ∈ s, if Disjoint a b then ‖pairProjection a b f‖ ^ 2 else 0) =
      ∑ b ∈ s, ‖pairProjection a b f‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : Disjoint a b
  · rw [ite_eq_left hab]
  · rw [ite_eq_right hab, pairProjection_eq_zero_of_not_disjoint a b hab]
    simp

theorem pairProjection_idempotent (a b : Finset (Fin n)) (f : StateSpace n d) :
    pairProjection a b (pairProjection a b f) = pairProjection a b f := by
  unfold pairProjection
  split_ifs
  · exact Submodule.starProjection_eq_self_iff.mpr
      ((equalitySpace _ _ _ _).starProjection_apply_mem f)
  all_goals simp

theorem pairProjection_isSymmetric (a b : Finset (Fin n)) :
    (pairProjection (d := d) a b).toLinearMap.IsSymmetric := by
  intro f g
  change ⟪pairProjection a b f, g⟫ = ⟪f, pairProjection a b g⟫
  by_cases ha : a.card = 2
  · by_cases hb : b.card = 2
    · simp only [pairProjection, dite_eq_left ha, dite_eq_left hb]
      exact (equalitySpace (d := d) (endpoints a ha).1 (endpoints a ha).2
        (endpoints b hb).1 (endpoints b hb).2).inner_starProjection_left_eq_right f g
    · rw [pairProjection_eq_zero_right a b hb]
      simp
  · rw [pairProjection_eq_zero_left a b ha]
    simp

theorem inner_pairProjection (a b : Finset (Fin n)) (f : StateSpace n d) :
    ⟪f, pairProjection a b f⟫ = ‖pairProjection a b f‖ ^ 2 := by
  have h := pairProjection_isSymmetric a b f (pairProjection a b f)
  change ⟪pairProjection a b f, pairProjection a b f⟫ =
    ⟪f, pairProjection a b (pairProjection a b f)⟫ at h
  rw [pairProjection_idempotent, real_inner_self_eq_norm_sq] at h
  exact h.symm

theorem sum_pairProjection_energy (a : Finset (Fin n))
    (s : Finset (Finset (Fin n))) (f : StateSpace n d) :
    (∑ b ∈ s, ‖pairProjection a b f‖ ^ 2) =
      ⟪f, ∑ b ∈ s, pairProjection a b f⟫ := by
  simp only [inner_sum, inner_pairProjection]

end Problem315.PairEquality

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairEqualityUnordered.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairDisjointAssembly.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairResampling
attribute [local instance] Classical.propDecidable

theorem interaction_on_pairs_of_named {n : ℕ} {d : Fin n → ℕ}
    (f : StateSpace n d)
    (hlocal : ∀ (i j k l : Fin n) (h : FourDistinct i j k l),
      2 * ‖SwitchFlip.projection (CrossToggle.crossProposal i j k l h) f‖ ^ 2 -
        ‖PairEquality.projection i j k l f‖ ^ 2 -
        ‖PairEquality.projection k l i j f‖ ^ 2 ≤
      2 * ⟪fluctuation n d {i,j} f, fluctuation n d {k,l} f⟫)
    (a : Finset (Fin n)) (ha : a ∈ pairs n)
    (b : Finset (Fin n)) (hb : b ∈ pairs n) (hab : Disjoint a b) :
    2 * ‖CrossToggle.gain a b f‖ ^ 2 - ‖PairEquality.pairProjection a b f‖ ^ 2 -
      ‖PairEquality.pairProjection b a f‖ ^ 2 ≤
      2 * ⟪fluctuation n d a f, fluctuation n d b f⟫ := by
  have hca : a.card = 2 := (Finset.mem_powersetCard.mp ha).2
  have hcb : b.card = 2 := (Finset.mem_powersetCard.mp hb).2
  let A : CrossToggle.VertexPair n := ⟨a, hca⟩
  let B : CrossToggle.VertexPair n := ⟨b, hcb⟩
  have hA : a = {CrossToggle.first A, CrossToggle.second A} := CrossToggle.pair_eq A
  have hB : b = {CrossToggle.first B, CrossToggle.second B} := CrossToggle.pair_eq B
  have hfour := CrossToggle.endpoints_distinct A B hab
  have hg : CrossToggle.gain (d := d) a b =
      SwitchFlip.projection (CrossToggle.crossProposal
        (CrossToggle.first A) (CrossToggle.second A)
        (CrossToggle.first B) (CrossToggle.second B) hfour) := by
    rw [CrossToggle.gain_of_pairs a b hca hcb]
    exact CrossToggle.pairProjection_of_disjoint A B hab
  rw [hg,
    PairEquality.pairProjection_eq a b _ _ _ _
      (CrossToggle.first_ne_second A) (CrossToggle.first_ne_second B) hA hB,
    PairEquality.pairProjection_eq b a _ _ _ _
      (CrossToggle.first_ne_second B) (CrossToggle.first_ne_second A) hB hA]
  simpa only [← hA, ← hB] using hlocal _ _ _ _ hfour

theorem disjoint_sum_nonneg_of_named_interaction_budget {n : ℕ} {d : Fin n → ℕ}
    (f : StateSpace n d)
    (hlocal : ∀ (i j k l : Fin n) (h : FourDistinct i j k l),
      2 * ‖SwitchFlip.projection (CrossToggle.crossProposal i j k l h) f‖ ^ 2 -
        ‖PairEquality.projection i j k l f‖ ^ 2 -
        ‖PairEquality.projection k l i j f‖ ^ 2 ≤
      2 * ⟪fluctuation n d {i,j} f, fluctuation n d {k,l} f⟫)
    (hbudget : ∀ a ∈ pairs n,
      (∑ b ∈ pairs n, ‖PairEquality.pairProjection a b f‖ ^ 2) ≤
        ∑ b ∈ pairs n, ‖CrossToggle.gain a b f‖ ^ 2) :
    0 ≤ ∑ a ∈ pairs n, ∑ b ∈ pairs n,
      if Disjoint a b then ⟪fluctuation n d a f, fluctuation n d b f⟫ else 0 := by
  apply disjoint_sum_nonneg_of_interaction_budget f
    (fun a b => CrossToggle.gain a b) (fun a b => PairEquality.pairProjection a b)
    (interaction_on_pairs_of_named f hlocal)
  intro a ha
  rw [PairEquality.sum_pairProjection_norm_sq]
  have hg : (∑ b ∈ pairs n, if Disjoint a b then ‖CrossToggle.gain a b f‖ ^ 2 else 0) =
      ∑ b ∈ pairs n, ‖CrossToggle.gain a b f‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hab : Disjoint a b
    · rw [ite_eq_left hab]
    · rw [ite_eq_right hab, CrossToggle.gain_eq_zero_of_not_disjoint a b hab]
      simp
  rw [hg]
  exact hbudget a ha

end Problem315.PairResampling

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairDisjointAssembly.lean -/
