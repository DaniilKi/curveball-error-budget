import AnalyticGeneratorSquare

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/ProposalUniqueness.lean -/
section

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
namespace Problem315

theorem IsPerfectMatchingOn.mem_iff_exists_adj {n : Nat} {S : Finset (Fin n)}
    {M : SimpleGraph (Fin n)} (hm : IsPerfectMatchingOn S M) (v : Fin n) :
    v ∈ S ↔ ∃ w, M.Adj v w := by
  constructor
  · intro hv
    obtain ⟨w, hw, _⟩ := (hm v).1 hv
    exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    by_contra hv
    exact (hm v).2 hv w hw

theorem IsPerfectMatchingOn.support_unique {n : Nat} {S T : Finset (Fin n)}
    {M : SimpleGraph (Fin n)} (hS : IsPerfectMatchingOn S M)
    (hT : IsPerfectMatchingOn T M) : S = T := by
  ext v
  rw [hS.mem_iff_exists_adj v, hT.mem_iff_exists_adj v]

theorem SwitchProposal.ext_matchings {n : Nat} {p q : SwitchProposal n}
    (hM : removedMatching p = removedMatching q)
    (hN : addedMatching p = addedMatching q) : p = q := by
  rcases p with ⟨⟨S, hS⟩, ⟨⟨⟨M, hm⟩, ⟨N, hn⟩⟩, hmn⟩⟩
  rcases q with ⟨⟨T, hT⟩, ⟨⟨⟨M', hm'⟩, ⟨N', hn'⟩⟩, hmn'⟩⟩
  change M = M' at hM
  change N = N' at hN
  subst M'
  subst N'
  have hST : S = T := hm.support_unique hm'
  subst T
  rfl

theorem removedMatching_adj_iff {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (hp : validSwitch G p) (u v : Fin n) :
    (removedMatching p).Adj u v ↔
      G.Adj u v ∧ ¬ (proposalResult G p).Adj u v := by
  classical
  rw [proposalResult, ite_eq_left hp]
  change (removedMatching p).Adj u v ↔ G.Adj u v ∧
    ¬ ((G.Adj u v ∧ ¬ (removedMatching p).Adj u v) ∨ (addedMatching p).Adj u v)
  constructor
  · intro hm
    refine ⟨hp.1 hm, ?_⟩
    rintro (⟨_, hnm⟩ | hn)
    · exact hnm hm
    · exact hp.2 hn (hp.1 hm)
  · rintro ⟨hg, hh⟩
    by_contra hnm
    exact hh (Or.inl ⟨hg, hnm⟩)

theorem addedMatching_adj_iff {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (hp : validSwitch G p) (u v : Fin n) :
    (addedMatching p).Adj u v ↔
      (proposalResult G p).Adj u v ∧ ¬ G.Adj u v := by
  classical
  rw [proposalResult, ite_eq_left hp]
  change (addedMatching p).Adj u v ↔
    ((G.Adj u v ∧ ¬ (removedMatching p).Adj u v) ∨ (addedMatching p).Adj u v) ∧
      ¬ G.Adj u v
  constructor
  · intro hn
    exact ⟨Or.inr hn, hp.2 hn⟩
  · rintro ⟨⟨hg, _⟩ | hn, hng⟩
    · exact False.elim (hng hg)
    · exact hn

theorem proposalResult_injective_on_valid {n : Nat} {G : SimpleGraph (Fin n)}
    {p q : SwitchProposal n} (hp : validSwitch G p) (hq : validSwitch G q)
    (heq : proposalResult G p = proposalResult G q) : p = q := by
  apply SwitchProposal.ext_matchings
  · ext u v
    rw [removedMatching_adj_iff hp, removedMatching_adj_iff hq, heq]
  · ext u v
    rw [addedMatching_adj_iff hp, addedMatching_adj_iff hq, heq]

theorem validSwitch_of_proposalResult_ne {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (h : proposalResult G p ≠ G) : validSwitch G p := by
  classical
  by_contra hn
  exact h (by simp [proposalResult, hn])

theorem proposalResult_ne_of_validSwitch {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (hp : validSwitch G p) : proposalResult G p ≠ G := by
  have hs : p.1.val.Nonempty := Finset.card_pos.mp (by rw [p.1.property]; decide)
  obtain ⟨v, hv⟩ := hs
  obtain ⟨w, hw⟩ := (p.2.val.1.property.mem_iff_exists_adj v).mp hv
  have hh := (removedMatching_adj_iff hp v w).mp hw
  intro heq
  rw [heq] at hh
  exact hh.2 hh.1

theorem validSwitch_iff_proposalResult_ne {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} : validSwitch G p ↔ proposalResult G p ≠ G :=
  ⟨proposalResult_ne_of_validSwitch, validSwitch_of_proposalResult_ne⟩

theorem proposal_count_eq_one {n : Nat} {G H : SimpleGraph (Fin n)}
    (hGH : G ≠ H) (hex : ∃ p : SwitchProposal n, proposalResult G p = H) :
    ((allProposals n).filter (fun p => proposalResult G p = H)).card = 1 := by
  classical
  obtain ⟨p, hp⟩ := hex
  apply Finset.card_eq_one.mpr
  refine ⟨p, ?_⟩
  ext q
  simp only [allProposals, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro hq
    apply proposalResult_injective_on_valid
    · apply validSwitch_of_proposalResult_ne
      rw [hq]
      exact Ne.symm hGH
    · apply validSwitch_of_proposalResult_ne
      rw [hp]
      exact Ne.symm hGH
    · exact hq.trans hp.symm
  · rintro rfl
    exact hp

theorem proposal_count_eq_zero {n : Nat} {G H : SimpleGraph (Fin n)}
    (hex : ¬ ∃ p : SwitchProposal n, proposalResult G p = H) :
    ((allProposals n).filter (fun p => proposalResult G p = H)).card = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact hex ⟨p, (Finset.mem_filter.mp hp).2⟩

theorem switchKernel_of_ne {n : Nat} {d : Fin n → Nat}
    {G H : GraphState n d} (hGH : G ≠ H) :
    switchKernel n d G H =
      if SwitchStep n d G H then 1 / (12 * (Nat.choose n 4 : ℝ)) else 0 := by
  classical
  have hv : G.val ≠ H.val := fun h => hGH (Subtype.ext h)
  have hiff : SwitchStep n d G H ↔
      ∃ p : SwitchProposal n, proposalResult G.val p = H.val := by
    constructor
    · rintro ⟨p, _, hp⟩
      exact ⟨p, hp⟩
    · rintro ⟨p, hp⟩
      refine ⟨p, ?_, hp⟩
      apply validSwitch_of_proposalResult_ne
      rw [hp]
      exact Ne.symm hv
  by_cases hs : SwitchStep n d G H
  · rw [switchKernel, ite_eq_right hGH, ite_eq_left hs,
      proposal_count_eq_one hv (hiff.mp hs)]
    simp
  · rw [switchKernel, ite_eq_right hGH, ite_eq_right hs,
      proposal_count_eq_zero (fun h => hs (hiff.mpr h))]
    simp

end Problem315

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/ProposalUniqueness.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/MatchingCount.lean -/
section

namespace OAI

noncomputable section

namespace Problem315.MatchingCount

abbrev FixedPointFreeInvolution (V : Type*) :=
  {f : V → V // Function.Involutive f ∧ ∀ v, f v ≠ v}

instance {V : Type*} [Fintype V] [DecidableEq V] :
    Fintype (FixedPointFreeInvolution V) := by
  letI : DecidablePred (fun f : V → V => Function.Involutive f ∧ ∀ v, f v ≠ v) :=
    fun f => inferInstanceAs (Decidable ((∀ v, f (f v) = v) ∧ ∀ v, f v ≠ v))
  exact Subtype.fintype _

private theorem involution_fin_four_card :
    Fintype.card (FixedPointFreeInvolution (Fin 4)) = 3 := by
  decide

noncomputable def involutionCongr {V W : Type*} (e : V ≃ W) :
    FixedPointFreeInvolution V ≃ FixedPointFreeInvolution W where
  toFun f := ⟨fun w => e (f.val (e.symm w)), by
    constructor
    · intro w
      simp only [Equiv.symm_apply_apply]
      rw [f.property.1 (e.symm w), Equiv.apply_symm_apply]
    · intro w h
      have h' := congrArg e.symm h
      simp only [Equiv.symm_apply_apply] at h'
      exact f.property.2 (e.symm w) h'⟩
  invFun f := ⟨fun v => e.symm (f.val (e v)), by
    constructor
    · intro v
      simp only [Equiv.apply_symm_apply]
      rw [f.property.1 (e v), Equiv.symm_apply_apply]
    · intro v h
      have h' := congrArg e h
      simp only [Equiv.apply_symm_apply] at h'
      exact f.property.2 (e v) h'⟩
  left_inv f := by ext v; simp
  right_inv f := by ext v; simp

 theorem involution_card_of_card_four {V : Type*} [Fintype V]
    (hV : Fintype.card V = 4) : Nat.card (FixedPointFreeInvolution V) = 3 := by
  classical
  let e : V ≃ Fin 4 := Fintype.equivFinOfCardEq hV
  rw [Nat.card_congr (involutionCongr e), Nat.card_eq_fintype_card]
  exact involution_fin_four_card

variable {n : ℕ} {S : FourSet n}

private theorem matching_neighbor_mem (M : PerfectMatching S)
    {u v : Fin n} (h : M.val.Adj u v) : v ∈ S.val := by
  by_contra hv
  exact ((M.property v).2 hv u) (M.val.symm.symm u v h)

noncomputable def mate (M : PerfectMatching S) (v : S.val) : S.val :=
  ⟨Classical.choose ((M.property v.val).1 v.property).exists,
    matching_neighbor_mem M (Classical.choose_spec ((M.property v.val).1 v.property).exists)⟩

private theorem mate_adj (M : PerfectMatching S) (v : S.val) :
    M.val.Adj v.val (mate M v).val :=
  Classical.choose_spec ((M.property v.val).1 v.property).exists

private theorem mate_unique (M : PerfectMatching S) (v : S.val) {w : Fin n}
    (hw : M.val.Adj v.val w) : w = (mate M v).val :=
  ((M.property v.val).1 v.property).unique hw (mate_adj M v)

noncomputable def matchingToInvolution (M : PerfectMatching S) :
    FixedPointFreeInvolution S.val := ⟨mate M, by
  constructor
  · intro v
    apply Subtype.ext
    exact (mate_unique M (mate M v) (M.val.symm.symm _ _ (mate_adj M v))).symm
  · intro v h
    have hh := mate_adj M v
    rw [h] at hh
    exact M.val.loopless.irrefl _ hh⟩

def involutionGraph (f : FixedPointFreeInvolution S.val) : SimpleGraph (Fin n) where
  Adj u v := ∃ (hu : u ∈ S.val) (hv : v ∈ S.val), f.val ⟨u, hu⟩ = ⟨v, hv⟩
  symm := by
    constructor
    rintro u v ⟨hu, hv, h⟩
    refine ⟨hv, hu, ?_⟩
    rw [← h, f.property.1]
  loopless := by
    constructor
    rintro v ⟨hv, hv', h⟩
    exact f.property.2 ⟨v, hv⟩ h

noncomputable def involutionToMatching (f : FixedPointFreeInvolution S.val) :
    PerfectMatching S := ⟨involutionGraph f, by
  intro v
  constructor
  · intro hv
    refine ⟨(f.val ⟨v, hv⟩).val, ?_, ?_⟩
    · exact ⟨hv, (f.val ⟨v, hv⟩).property, rfl⟩
    · rintro w ⟨hv', hw, h⟩
      exact (congrArg Subtype.val h).symm
  · intro hv w h
    exact hv h.choose⟩

noncomputable def matchingEquivInvolution (S : FourSet n) :
    PerfectMatching S ≃ FixedPointFreeInvolution S.val where
  toFun := matchingToInvolution
  invFun := involutionToMatching
  left_inv M := by
    apply Subtype.ext
    apply SimpleGraph.ext
    funext u v
    apply propext
    constructor
    · rintro ⟨hu, hv, h⟩
      have hh := mate_adj M ⟨u, hu⟩
      change mate M ⟨u, hu⟩ = ⟨v, hv⟩ at h
      rw [h] at hh
      exact hh
    · intro h
      have hu := matching_neighbor_mem M (M.val.symm.symm _ _ h)
      have hv := matching_neighbor_mem M h
      refine ⟨hu, hv, ?_⟩
      apply Subtype.ext
      exact (mate_unique M ⟨u, hu⟩ h).symm
  right_inv f := by
    apply Subtype.ext
    funext v
    apply Subtype.ext
    exact (mate_unique (involutionToMatching f) v
      ⟨v.property, (f.val v).property, rfl⟩).symm

theorem perfectMatching_card (S : FourSet n) : Nat.card (PerfectMatching S) = 3 := by
  rw [Nat.card_congr (matchingEquivInvolution S)]
  apply involution_card_of_card_four
  simpa only [Fintype.card_coe] using S.property

theorem orderedMatchings_card (S : FourSet n) :
    Nat.card {p : PerfectMatching S × PerfectMatching S // p.1 ≠ p.2} = 6 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hfilter : (Finset.univ.filter fun p : PerfectMatching S × PerfectMatching S => p.1 ≠ p.2) =
      (Finset.univ : Finset (PerfectMatching S)).offDiag := by
    ext p
    simp
  rw [hfilter, Finset.offDiag_card, Finset.card_univ]
  have hcard : Fintype.card (PerfectMatching S) = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact perfectMatching_card S
  rw [hcard]

theorem fourSet_card (n : ℕ) : Nat.card (FourSet n) = n.choose 4 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.univ_filter_card_eq, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

theorem switchProposal_card (n : ℕ) : Nat.card (SwitchProposal n) = 6 * n.choose 4 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  have hcard (S : FourSet n) :
      Fintype.card {p : PerfectMatching S × PerfectMatching S // p.1 ≠ p.2} = 6 := by
    rw [← Nat.card_eq_fintype_card]
    exact orderedMatchings_card S
  simp_rw [hcard]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
    fourSet_card, Nat.mul_comm]

theorem allProposals_card (n : ℕ) : (allProposals n).card = 6 * n.choose 4 := by
  classical
  unfold allProposals
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
  exact switchProposal_card n

end Problem315.MatchingCount

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/MatchingCount.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/KernelNormalization.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace Problem315

def proposalState {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (p : SwitchProposal n) : GraphState n d :=
  ⟨proposalResult G.val p, proposalResult_realizes G.property p⟩

theorem proposal_fiber_cards_sum {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) :
    (∑ H ∈ allGraphStates n d,
      ((allProposals n).filter (fun p => proposalResult G.val p = H.val)).card) =
      (allProposals n).card := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (allProposals n) (allGraphStates n d) (proposalState G)
  have hf (H : GraphState n d) :
      ((allProposals n).filter (fun p => proposalState G p = H)) =
      ((allProposals n).filter (fun p => proposalResult G.val p = H.val)) := by
    ext p
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro _
    exact Subtype.ext_iff
  simp_rw [hf] at h
  simpa only [allGraphStates, Finset.mem_univ, Finset.filter_true] using h

theorem switchKernel_row_sum {n : ℕ} {d : Fin n → ℕ}
    (hn : 4 ≤ n) (G : GraphState n d) :
    (∑ H ∈ allGraphStates n d, switchKernel n d G H) = 1 := by
  classical
  have hc : (Nat.choose n 4 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hn))
  unfold switchKernel
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Nat.cast_sum,
    proposal_fiber_cards_sum, MatchingCount.allProposals_card]
  have hdiag : (∑ H ∈ allGraphStates n d, if G = H then (1 : ℝ) / 2 else 0) = 1 / 2 := by
    simp [allGraphStates]
  rw [hdiag]
  push_cast
  field_simp
  ring

theorem switchKernel_column_sum {n : ℕ} {d : Fin n → ℕ}
    (hn : 4 ≤ n) (H : GraphState n d) :
    (∑ G ∈ allGraphStates n d, switchKernel n d G H) = 1 := by
  simp_rw [switchKernel_symm (_ : GraphState n d) H]
  exact switchKernel_row_sum hn H

end Problem315

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/KernelNormalization.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SwitchLaplacian.lean -/
section

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace Problem315

def switchLaplacian (n : Nat) (d : Fin n → Nat)
    (f : GraphState n d → ℝ) (G : GraphState n d) : ℝ :=
  ∑ H ∈ allGraphStates n d, if SwitchStep n d G H then f G - f H else 0

theorem switchStep_ne {n : Nat} {d : Fin n → Nat} {G H : GraphState n d}
    (h : SwitchStep n d G H) : G ≠ H := by
  obtain ⟨p, hp, heq⟩ := h
  intro heq'
  subst H
  exact proposalResult_ne_of_validSwitch hp heq

theorem switchKernel_mul_sub_eq {n : Nat} {d : Fin n → Nat}
    (f : GraphState n d → ℝ) (G H : GraphState n d) :
    switchKernel n d G H * (f G - f H) =
      (if SwitchStep n d G H then f G - f H else 0) /
        (12 * (Nat.choose n 4 : ℝ)) := by
  by_cases h : G = H
  · subst H
    simp
  · rw [switchKernel_of_ne h]
    split_ifs <;> ring

theorem sub_markovApply_eq_switchLaplacian {n : Nat} {d : Fin n → Nat}
    (hrow : ∀ G : GraphState n d,
      ∑ H ∈ allGraphStates n d, switchKernel n d G H = 1)
    (f : GraphState n d → ℝ) (G : GraphState n d) :
    f G - markovApply n d f G =
      switchLaplacian n d f G / (12 * (Nat.choose n 4 : ℝ)) := by
  calc
    f G - markovApply n d f G =
        (∑ H ∈ allGraphStates n d, switchKernel n d G H) * f G -
          ∑ H ∈ allGraphStates n d, switchKernel n d G H * f H := by
            rw [hrow G, one_mul]
            rfl
    _ = ∑ H ∈ allGraphStates n d, switchKernel n d G H * (f G - f H) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro H hH
      ring
    _ = switchLaplacian n d f G / (12 * (Nat.choose n 4 : ℝ)) := by
      simp only [switchKernel_mul_sub_eq, switchLaplacian, Finset.sum_div]

theorem dirichletEnergy_eq_switchLaplacian {n : Nat} {d : Fin n → Nat}
    (hrow : ∀ G : GraphState n d,
      ∑ H ∈ allGraphStates n d, switchKernel n d G H = 1)
    (f : GraphState n d → ℝ) :
    dirichletEnergy n d f =
      uniformInner n d f (switchLaplacian n d f) /
        (12 * (Nat.choose n 4 : ℝ)) := by
  unfold dirichletEnergy uniformInner uniformAverage
  simp only [sub_markovApply_eq_switchLaplacian hrow, ← mul_div_assoc]
  rw [← Finset.sum_div]
  ring

theorem hasSpectralGapAtLeast_of_switchLaplacian {n : Nat} {d : Fin n → Nat}
    (hn : 4 ≤ n)
    (hrow : ∀ G : GraphState n d,
      ∑ H ∈ allGraphStates n d, switchKernel n d G H = 1)
    (hpoincare : ∀ f : GraphState n d → ℝ,
      uniformVariance n d f ≤
        2 * (n : ℝ)^2 * uniformInner n d f (switchLaplacian n d f)) :
    hasSpectralGapAtLeast n d
      ((1 : ℝ) / (24 * (n : ℝ)^2 * (Nat.choose n 4 : ℝ))) := by
  intro f
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hc : (0 : ℝ) < Nat.choose n 4 := by exact_mod_cast Nat.choose_pos hn
  have hd : (0 : ℝ) < 12 * (Nat.choose n 4 : ℝ) := by positivity
  have hden : (0 : ℝ) < 24 * (n : ℝ)^2 * (Nat.choose n 4 : ℝ) := by positivity
  rw [dirichletEnergy_eq_switchLaplacian hrow]
  rw [div_mul_eq_mul_div, one_mul]
  apply (div_le_div_iff₀ hden hd).mpr
  have h := mul_le_mul_of_nonneg_right (hpoincare f) (le_of_lt hd)
  nlinarith only [h]

theorem switch_chain_gap_of_laplacian_poincare {n : Nat} {d : Fin n → Nat}
    (hn : 4 ≤ n)
    (hpoincare : ∀ f : GraphState n d → ℝ,
      uniformVariance n d f ≤
        2 * (n : ℝ)^2 * uniformInner n d f (switchLaplacian n d f)) :
    hasSpectralGapAtLeast n d
      ((1 : ℝ) / (24 * (n : ℝ)^2 * (Nat.choose n 4 : ℝ))) :=
  hasSpectralGapAtLeast_of_switchLaplacian hn (switchKernel_row_sum hn) hpoincare

end Problem315

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SwitchLaplacian.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SwitchPairFiber.lean -/
section

namespace OAI

noncomputable section

namespace Problem315.SwitchPairFiber

attribute [local instance] Classical.propDecidable

lemma matching_endpoints_mem {n : ℕ} {S : FourSet n}
    (M : PerfectMatching S) {u v : Fin n} (h : M.val.Adj u v) :
    u ∈ S.val ∧ v ∈ S.val := by
  constructor
  · by_contra hu
    exact (M.property u).2 hu v h
  · by_contra hv
    exact (M.property v).2 hv u h.symm

theorem exists_cross_cut {n : ℕ} {G : SimpleGraph (Fin n)}
    (p : SwitchProposal n) (hp : validSwitch G p) :
    ∃ A : Finset (Fin n), A.card = 2 ∧ A ⊆ p.1.val ∧
      ∀ a b, ((removedMatching p).Adj a b ∨ (addedMatching p).Adj a b) →
        (a ∈ A ↔ b ∉ A) := by
  classical
  let S := p.1
  let M := p.2.val.1
  let N := p.2.val.2
  have hS : S.val.card = 4 := S.property
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < S.val.card by omega)
  obtain ⟨v, huv, hvuniq⟩ := (M.property u).1 hu
  obtain ⟨w, huw, hwuniq⟩ := (N.property u).1 hu
  have hv := (matching_endpoints_mem M huv).2
  have hw := (matching_endpoints_mem N huw).2
  have huvne : u ≠ v := M.val.ne_of_adj huv
  have huwne : u ≠ w := N.val.ne_of_adj huw
  have hvwne : v ≠ w := by
    intro heq
    subst w
    exact validSwitch_matchings_disjoint hp huv huw
  let T : Finset (Fin n) := {u, v, w}
  have hT : T.card = 3 := by simp [T, huvne, huwne, hvwne]
  have hnot : ¬ S.val ⊆ T := by
    intro h
    have := Finset.card_le_card h
    omega
  obtain ⟨x, hx⟩ := Finset.sdiff_nonempty.mpr hnot
  have hxS : x ∈ S.val := (Finset.mem_sdiff.mp hx).1
  have hxT : x ∉ T := (Finset.mem_sdiff.mp hx).2
  have hxune : x ≠ u := by intro h; apply hxT; simp [T, h]
  have hxvne : x ≠ v := by intro h; apply hxT; simp [T, h]
  have hxwne : x ≠ w := by intro h; apply hxT; simp [T, h]
  have hfull : S.val = {u, v, w, x} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> assumption
    · simp [hS, huvne, huwne, hvwne, hxune.symm, hxvne.symm, hxwne.symm]
  have hMxw : M.val.Adj x w := by
    obtain ⟨y, hxy, hyuniq⟩ := (M.property x).1 hxS
    have hy := (matching_endpoints_mem M hxy).2
    rw [hfull] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with hy | hy | hy | hy <;> subst y
    · exact False.elim (hxvne (hvuniq x hxy.symm))
    · obtain ⟨z, hz, hzuniq⟩ := (M.property v).1 hv
      have hxu : x = u := (hzuniq x hxy.symm).trans (hzuniq u huv.symm).symm
      exact False.elim (hxune hxu)
    · exact hxy
    · exact False.elim (M.val.loopless.irrefl x hxy)
  have hNxv : N.val.Adj x v := by
    obtain ⟨y, hxy, hyuniq⟩ := (N.property x).1 hxS
    have hy := (matching_endpoints_mem N hxy).2
    rw [hfull] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with hy | hy | hy | hy <;> subst y
    · exact False.elim (hxwne (hwuniq x hxy.symm))
    · exact hxy
    · obtain ⟨z, hz, hzuniq⟩ := (N.property w).1 hw
      have hxu : x = u := (hzuniq x hxy.symm).trans (hzuniq u huw.symm).symm
      exact False.elim (hxune hxu)
    · exact False.elim (N.val.loopless.irrefl x hxy)
  refine ⟨{u, x}, by simp [hxune.symm], ?_, ?_⟩
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> assumption
  · intro a b hab
    have hmem : a ∈ S.val := by
      rcases hab with hab | hab
      · exact (matching_endpoints_mem M hab).1
      · exact (matching_endpoints_mem N hab).1
    rw [hfull] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with ha | ha | ha | ha <;> subst a
    all_goals rcases hab with hab | hab
    all_goals simp only [Finset.mem_insert, Finset.mem_singleton]
    · have hb := hvuniq b hab
      subst b
      simp [huvne, hxvne, hxune, Ne.symm]
    · have hb := hwuniq b hab
      subst b
      simp [huwne, hxwne, hxune, Ne.symm]
    · have hb : b = u := by
        obtain ⟨z, hz, hzuniq⟩ := (M.property v).1 hv
        exact (hzuniq b hab).trans (hzuniq u huv.symm).symm
      subst b
      simp [huvne, hxvne, hxune, Ne.symm]
    · have hb : b = x := by
        obtain ⟨z, hz, hzuniq⟩ := (N.property v).1 hv
        exact (hzuniq b hab).trans (hzuniq x hNxv.symm).symm
      subst b
      simp [huvne, hxvne, hxune, Ne.symm]
    · have hb : b = x := by
        obtain ⟨z, hz, hzuniq⟩ := (M.property w).1 hw
        exact (hzuniq b hab).trans (hzuniq x hMxw.symm).symm
      subst b
      simp [huwne, hxwne, hxune, Ne.symm]
    · have hb : b = u := by
        obtain ⟨z, hz, hzuniq⟩ := (N.property w).1 hw
        exact (hzuniq b hab).trans (hzuniq u huw.symm).symm
      subst b
      simp [huwne, hxwne, hxune, Ne.symm]
    · have hb : b = w := by
        obtain ⟨z, hz, hzuniq⟩ := (M.property x).1 hxS
        exact (hzuniq b hab).trans (hzuniq w hMxw).symm
      subst b
      simp [huwne, hxwne, hxune, Ne.symm]
    · have hb : b = v := by
        obtain ⟨z, hz, hzuniq⟩ := (N.property x).1 hxS
        exact (hzuniq b hab).trans (hzuniq v hNxv).symm
      subst b
      simp [huvne, hxvne, hxune, Ne.symm]

theorem exists_frozen_cut {n : ℕ} {G : SimpleGraph (Fin n)}
    (p : SwitchProposal n) (hp : validSwitch G p) :
    ∃ A : Finset (Fin n), A.card = 2 ∧ A ⊆ p.1.val ∧
      ∀ a b, (a ∈ A ↔ b ∈ A) →
        ((proposalResult G p).Adj a b ↔ G.Adj a b) := by
  classical
  obtain ⟨A, hA, hAS, hcross⟩ := exists_cross_cut p hp
  refine ⟨A, hA, hAS, ?_⟩
  intro a b hside
  have hm : ¬ (removedMatching p).Adj a b := by
    intro h
    have := hcross a b (Or.inl h)
    tauto
  have hn : ¬ (addedMatching p).Adj a b := by
    intro h
    have := hcross a b (Or.inr h)
    tauto
  rw [proposalResult_of_valid hp]
  change ((G.Adj a b ∧ ¬ (removedMatching p).Adj a b) ∨
    (addedMatching p).Adj a b) ↔ G.Adj a b
  simp [hm, hn]

theorem degree_into_eq {n : ℕ} (G H : SimpleGraph (Fin n))
    (A : Finset (Fin n)) (w : Fin n)
    (hdegree : graphDegree G w = graphDegree H w)
    (hout : ∀ v, v ∉ A → (G.Adj w v ↔ H.Adj w v)) :
    (A.filter (G.Adj w)).card = (A.filter (H.Adj w)).card := by
  classical
  let D (X : SimpleGraph (Fin n)) := Finset.univ.filter (X.Adj w)
  have hinter (X : SimpleGraph (Fin n)) :
      D X ∩ A = A.filter (X.Adj w) := by
    ext v
    simp [D, and_comm]
  have hdiff : D G \ A = D H \ A := by
    ext v
    simp only [Finset.mem_sdiff, D, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact ⟨(hout v h.2).mp h.1, h.2⟩
    · intro h
      exact ⟨(hout v h.2).mpr h.1, h.2⟩
  have hG := Finset.card_sdiff_add_card_inter (D G) A
  have hH := Finset.card_sdiff_add_card_inter (D H) A
  rw [hinter] at hG hH
  have hcard : (D G).card = (D H).card := hdegree
  rw [hdiff, hcard] at hG
  exact Nat.add_left_cancel (hG.trans hH.symm)

end Problem315.SwitchPairFiber

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SwitchPairFiber.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SwitchMultiplicity.lean -/
section

namespace OAI

noncomputable section

namespace Problem315.SwitchPairFiber

attribute [local instance] Classical.propDecidable

def Crosses {n : ℕ} (p : SwitchProposal n) (A : Finset (Fin n)) : Prop :=
  ∀ u v, ((removedMatching p).Adj u v ∨ (addedMatching p).Adj u v) →
    (u ∈ A ↔ v ∉ A)

lemma complement_card {n : ℕ} (p : SwitchProposal n) {A : Finset (Fin n)}
    (hAS : A ⊆ p.1.val) (hA : A.card = 2) : (p.1.val \ A).card = 2 := by
  rw [Finset.card_sdiff_of_subset hAS, p.1.property, hA]

lemma crosses_complement {n : ℕ} (p : SwitchProposal n) {A : Finset (Fin n)}
    (hcross : Crosses p A) : Crosses p (p.1.val \ A) := by
  intro u v huv
  have hmem : u ∈ p.1.val ∧ v ∈ p.1.val := by
    rcases huv with h | h
    · exact matching_endpoints_mem p.2.val.1 h
    · exact matching_endpoints_mem p.2.val.2 h
  have h := hcross u v huv
  simp only [Finset.mem_sdiff, hmem.1, hmem.2, true_and]
  tauto

theorem cross_cuts_eq_of_inter_nonempty {n : ℕ} {G : SimpleGraph (Fin n)}
    (p : SwitchProposal n) (hp : validSwitch G p) {A B : Finset (Fin n)}
    (hA : A.card = 2) (hB : B.card = 2) (hAS : A ⊆ p.1.val) (hBS : B ⊆ p.1.val)
    (hcA : Crosses p A) (hcB : Crosses p B) (hi : (A ∩ B).Nonempty) : A = B := by
  classical
  obtain ⟨u, hu⟩ := hi
  obtain ⟨huA, huB⟩ := Finset.mem_inter.mp hu
  have huS := hAS huA
  obtain ⟨v, huv, hvuniq⟩ := (p.2.val.1.property u).1 huS
  obtain ⟨w, huw, hwuniq⟩ := (p.2.val.2.property u).1 huS
  have hvS := (matching_endpoints_mem p.2.val.1 huv).2
  have hwS := (matching_endpoints_mem p.2.val.2 huw).2
  have hvw : v ≠ w := by
    intro h
    subst w
    exact validSwitch_matchings_disjoint hp huv huw
  have hvA : v ∉ A := (hcA u v (Or.inl huv)).mp huA
  have hwA : w ∉ A := (hcA u w (Or.inr huw)).mp huA
  have hvB : v ∉ B := (hcB u v (Or.inl huv)).mp huB
  have hwB : w ∉ B := (hcB u w (Or.inr huw)).mp huB
  have heqA : p.1.val \ A = {v, w} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hz | hz <;> subst z
      · exact Finset.mem_sdiff.mpr ⟨hvS, hvA⟩
      · exact Finset.mem_sdiff.mpr ⟨hwS, hwA⟩
    · simp [complement_card p hAS hA, hvw]
  have heqB : p.1.val \ B = {v, w} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hz | hz <;> subst z
      · exact Finset.mem_sdiff.mpr ⟨hvS, hvB⟩
      · exact Finset.mem_sdiff.mpr ⟨hwS, hwB⟩
    · simp [complement_card p hBS hB, hvw]
  have heq : p.1.val \ A = p.1.val \ B := heqA.trans heqB.symm
  ext z
  have hz := Finset.ext_iff.mp heq z
  simp only [Finset.mem_sdiff] at hz
  constructor
  · intro hzA
    have hzS := hAS hzA
    tauto
  · intro hzB
    have hzS := hBS hzB
    tauto

theorem cross_cuts_eq_or_complement {n : ℕ} {G : SimpleGraph (Fin n)}
    (p : SwitchProposal n) (hp : validSwitch G p) {A B : Finset (Fin n)}
    (hA : A.card = 2) (hB : B.card = 2) (hAS : A ⊆ p.1.val) (hBS : B ⊆ p.1.val)
    (hcA : Crosses p A) (hcB : Crosses p B) :
    B = A ∨ B = p.1.val \ A := by
  classical
  by_cases hi : (A ∩ B).Nonempty
  · exact Or.inl (cross_cuts_eq_of_inter_nonempty p hp hA hB hAS hBS hcA hcB hi).symm
  · right
    apply Finset.eq_of_subset_of_card_le
    · intro z hzB
      apply Finset.mem_sdiff.mpr
      refine ⟨hBS hzB, ?_⟩
      intro hzA
      exact hi ⟨z, Finset.mem_inter.mpr ⟨hzA, hzB⟩⟩
    · rw [complement_card p hAS hA, hB]

def crossingPairs {n : ℕ} (p : SwitchProposal n) : Finset (Finset (Fin n)) :=
  (p.1.val.powersetCard 2).filter (Crosses p)

theorem crossingPairs_card {n : ℕ} {G : SimpleGraph (Fin n)}
    (p : SwitchProposal n) (hp : validSwitch G p) :
    (crossingPairs p).card = 2 := by
  classical
  obtain ⟨A, hA, hAS, hcA⟩ := exists_cross_cut p hp
  have hAc : (p.1.val \ A).card = 2 := complement_card p hAS hA
  have hcAc : Crosses p (p.1.val \ A) := crosses_complement p hcA
  have hne : A ≠ p.1.val \ A := by
    intro heq
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
    have hu' : u ∈ p.1.val \ A := heq ▸ hu
    exact (Finset.mem_sdiff.mp hu').2 hu
  have heq : crossingPairs p = {A, p.1.val \ A} := by
    ext B
    simp only [crossingPairs, Finset.mem_filter, Finset.mem_powersetCard,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hBS, hB⟩, hcB⟩
      exact cross_cuts_eq_or_complement p hp hA hB hAS hBS hcA hcB
    · intro h
      rcases h with h | h <;> subst B
      · exact ⟨⟨hAS, hA⟩, hcA⟩
      · exact ⟨⟨Finset.sdiff_subset, hAc⟩, hcAc⟩
  rw [heq]
  simp [hne]

end Problem315.SwitchPairFiber

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SwitchMultiplicity.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/ProposalLaplacian.lean -/
section

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace Problem315

theorem switchLaplacian_eq_sum_proposals {n : Nat} {d : Fin n → Nat}
    (f : GraphState n d → ℝ) (G : GraphState n d) :
    switchLaplacian n d f G =
      ∑ p ∈ allProposals n, (f G - f (proposalState G p)) := by
  have hterm (H : GraphState n d) :
      (if SwitchStep n d G H then f G - f H else 0) =
        (((allProposals n).filter (fun p => proposalResult G.val p = H.val)).card : ℝ) *
          (f G - f H) := by
    by_cases hGH : G = H
    · subst H
      simp
    · have hv : G.val ≠ H.val := fun h => hGH (Subtype.ext h)
      by_cases hs : SwitchStep n d G H
      · obtain ⟨p, hvalid, hp⟩ := hs
        rw [ite_eq_left ⟨p, hvalid, hp⟩, proposal_count_eq_one hv ⟨p, hp⟩]
        simp
      · rw [ite_eq_right hs, proposal_count_eq_zero]
        · simp
        · rintro ⟨p, hp⟩
          apply hs
          refine ⟨p, ?_, hp⟩
          apply validSwitch_of_proposalResult_ne
          rw [hp]
          exact Ne.symm hv
  unfold switchLaplacian
  simp_rw [hterm]
  calc
    _ = ∑ H ∈ allGraphStates n d, ∑ p ∈ allProposals n,
        if proposalState G p = H then f G - f H else 0 := by
      apply Finset.sum_congr rfl
      intro H hH
      rw [← Finset.sum_filter]
      have hfilter : (allProposals n).filter (fun p => proposalState G p = H) =
          (allProposals n).filter (fun p => proposalResult G.val p = H.val) := by
        ext p
        simp only [Finset.mem_filter, and_congr_right_iff]
        intro _
        exact Subtype.ext_iff
      rw [hfilter]
      simp
      ring
    _ = ∑ p ∈ allProposals n, (f G - f (proposalState G p)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      simp [allGraphStates]

theorem sum_pairProposalLaplacian_eq {n : Nat} {d : Fin n → Nat}
    {ι : Type*} (pairs : Finset ι) (crosses : ι → SwitchProposal n → Prop)
    [∀ a p, Decidable (crosses a p)]
    (hcount : ∀ p : SwitchProposal n, (pairs.filter (fun a => crosses a p)).card = 2)
    (f : GraphState n d → ℝ) (G : GraphState n d) :
    (∑ a ∈ pairs, ∑ p ∈ allProposals n,
      if crosses a p then f G - f (proposalState G p) else 0) =
      2 * switchLaplacian n d f G := by
  rw [Finset.sum_comm, switchLaplacian_eq_sum_proposals, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_filter]
  simp [hcount p]
  ring

theorem sum_pairProposalLaplacian_eq_of_valid {n : Nat} {d : Fin n → Nat}
    {ι : Type*} (pairs : Finset ι) (crosses : ι → SwitchProposal n → Prop)
    [∀ a p, Decidable (crosses a p)]
    (f : GraphState n d → ℝ) (G : GraphState n d)
    (hcount : ∀ p : SwitchProposal n, validSwitch G.val p →
      (pairs.filter (fun a => crosses a p)).card = 2) :
    (∑ a ∈ pairs, ∑ p ∈ allProposals n,
      if crosses a p then f G - f (proposalState G p) else 0) =
      2 * switchLaplacian n d f G := by
  rw [Finset.sum_comm, switchLaplacian_eq_sum_proposals, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hv : validSwitch G.val p
  · rw [← Finset.sum_filter]
    simp [hcount p hv]
    ring
  · have heq : proposalState G p = G := by
      apply Subtype.ext
      simp [proposalState, proposalResult, hv]
    simp [heq]

def pairSwitchLaplacian (n : Nat) (d : Fin n → Nat) (a : Finset (Fin n))
    (f : GraphState n d → ℝ) (G : GraphState n d) : ℝ :=
  ∑ p ∈ allProposals n,
    if a ∈ SwitchPairFiber.crossingPairs p then f G - f (proposalState G p) else 0

theorem sum_pairSwitchLaplacian {n : Nat} {d : Fin n → Nat}
    (f : GraphState n d → ℝ) (G : GraphState n d) :
    (∑ a ∈ (Finset.univ : Finset (Fin n)).powersetCard 2,
      pairSwitchLaplacian n d a f G) = 2 * switchLaplacian n d f G := by
  unfold pairSwitchLaplacian
  refine sum_pairProposalLaplacian_eq_of_valid
    ((Finset.univ : Finset (Fin n)).powersetCard 2)
    (fun a p => a ∈ SwitchPairFiber.crossingPairs p) f G ?_
  intro p hp
  have heq : ((Finset.univ : Finset (Fin n)).powersetCard 2).filter
      (fun a => a ∈ SwitchPairFiber.crossingPairs p) = SwitchPairFiber.crossingPairs p := by
    ext a
    constructor
    · intro ha
      exact (Finset.mem_filter.mp ha).2
    · intro ha
      refine Finset.mem_filter.mpr ⟨?_, ha⟩
      apply Finset.mem_powersetCard.mpr
      refine ⟨Finset.subset_univ a, ?_⟩
      exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp ha).1).2
  rw [heq]
  exact SwitchPairFiber.crossingPairs_card p hp

end Problem315

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/ProposalLaplacian.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairSquaredEnergy.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315.PairSquaredEnergy
attribute [local instance] Classical.propDecidable

def reverseMove {n : ℕ} {d : Fin n → ℕ}
    (x : GraphState n d × SwitchProposal n) : GraphState n d × SwitchProposal n :=
  if validSwitch x.1.val x.2 then (proposalState x.1 x.2, reverseProposal x.2) else x

lemma reverseMove_involutive {n : ℕ} {d : Fin n → ℕ} :
    Function.Involutive (@reverseMove n d) := by
  intro x
  rcases x with ⟨G,p⟩
  by_cases h : validSwitch G.val p
  · have hr : validSwitch (proposalState G p).val (reverseProposal p) := by
      change validSwitch (proposalResult G.val p) (reverseProposal p)
      rw [proposalResult_of_valid h]
      exact validSwitch_reverse_replace h
    have hb : proposalState (proposalState G p) (reverseProposal p) = G := by
      apply Subtype.ext
      exact proposalResult_reverse h
    simp [reverseMove, h, hr, hb]
  · simp [reverseMove, h]

def reverseMoveEquiv {n : ℕ} {d : Fin n → ℕ} :
    Equiv.Perm (GraphState n d × SwitchProposal n) :=
  ⟨reverseMove, reverseMove, reverseMove_involutive, reverseMove_involutive⟩

lemma reverseMove_fst {n : ℕ} {d : Fin n → ℕ}
    (x : GraphState n d × SwitchProposal n) :
    (reverseMove x).1 = proposalState x.1 x.2 := by
  by_cases h : validSwitch x.1.val x.2
  · simp [reverseMove, h]
  · simp only [reverseMove, ite_eq_right h]
    apply Subtype.ext
    simp [proposalState, proposalResult, h]

lemma crossingPairs_reverse {n : ℕ} (p : SwitchProposal n) :
    SwitchPairFiber.crossingPairs (reverseProposal p) = SwitchPairFiber.crossingPairs p := by
  ext a
  simp only [SwitchPairFiber.crossingPairs, Finset.mem_filter]
  change (a ∈ p.1.val.powersetCard 2 ∧ SwitchPairFiber.Crosses (reverseProposal p) a) ↔ _
  unfold SwitchPairFiber.Crosses
  simp only [removedMatching_reverse, addedMatching_reverse, or_comm]

lemma reverseMove_crossing {n : ℕ} {d : Fin n → ℕ}
    (x : GraphState n d × SwitchProposal n) (a : Finset (Fin n)) :
    a ∈ SwitchPairFiber.crossingPairs (reverseMove x).2 ↔
      a ∈ SwitchPairFiber.crossingPairs x.2 := by
  by_cases h : validSwitch x.1.val x.2
  · simp [reverseMove, h, crossingPairs_reverse]
  · simp [reverseMove, h]

theorem involution_energy {X : Type*} [Fintype X] (e : Equiv.Perm X)
    (he : Function.Involutive e) (w f : X → ℝ) (hw : ∀ x, w (e x) = w x) :
    (∑ x, w x * f x * (f x - f (e x))) =
      (1 / 2 : ℝ) * ∑ x, w x * (f x - f (e x)) ^ 2 := by
  have hr : (∑ x, w x * f (e x) * (f (e x) - f x)) =
      ∑ x, w x * f x * (f x - f (e x)) := by
    have h := Equiv.sum_comp e (fun x => w x * f x * (f x - f (e x)))
    have he' (x : X) : e (e x) = x := he x
    simpa only [hw, he'] using h
  have hsum : (∑ x, w x * (f x - f (e x)) ^ 2) =
      (∑ x, w x * f x * (f x - f (e x))) +
      (∑ x, w x * f (e x) * (f (e x) - f x)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum, hr]
  ring

theorem pairSwitchLaplacian_energy {n : ℕ} {d : Fin n → ℕ}
    (a : Finset (Fin n)) (f : GraphState n d → ℝ) :
    (∑ G, f G * pairSwitchLaplacian n d a f G) =
      (1 / 2 : ℝ) * ∑ G, ∑ p ∈ allProposals n,
        if a ∈ SwitchPairFiber.crossingPairs p then
          (f G - f (proposalState G p)) ^ 2 else 0 := by
  let w : GraphState n d × SwitchProposal n → ℝ :=
    fun x => if a ∈ SwitchPairFiber.crossingPairs x.2 then 1 else 0
  have hw (x : GraphState n d × SwitchProposal n) :
      w (reverseMoveEquiv x) = w x := by
    change (if a ∈ SwitchPairFiber.crossingPairs (reverseMove x).2 then (1:ℝ) else 0) = _
    simp only [reverseMove_crossing, w]
  have h := involution_energy (@reverseMoveEquiv n d) reverseMove_involutive
    w (fun x => f x.1) hw
  change (∑ x, w x * f x.1 * (f x.1 - f (reverseMove x).1)) =
    (1 / 2 : ℝ) * ∑ x, w x * (f x.1 - f (reverseMove x).1) ^ 2 at h
  simp only [reverseMove_fst, Fintype.sum_prod_type] at h
  simpa only [w, pairSwitchLaplacian, allProposals, Finset.mul_sum,
    ite_mul, one_mul, zero_mul, mul_ite, mul_zero] using h

end Problem315.PairSquaredEnergy

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairSquaredEnergy.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SwitchInFiber.lean -/
section

namespace OAI

noncomputable section

namespace Problem315

attribute [local instance] Classical.propDecidable

theorem sameFiber_of_same_side {n : ℕ} {d : Fin n → ℕ}
    (A : Finset (Fin n)) (G H : GraphState n d)
    (hsame : ∀ u v, (u ∈ A ↔ v ∈ A) → (G.val.Adj u v ↔ H.val.Adj u v)) :
    PairResampling.SameFiber A G.val H.val := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu v hv
    exact hsame u v (by simp [hu, hv])
  · intro u hu v hv
    exact hsame u v (by simp [hu, hv])
  · intro w hw
    apply SwitchPairFiber.degree_into_eq G.val H.val A w
    · exact (G.property w).trans (H.property w).symm
    · intro v hv
      exact hsame w v (by simp [hw, hv])

theorem switchStep_sameFiber {n : ℕ} {d : Fin n → ℕ}
    {G H : GraphState n d} (hstep : SwitchStep n d G H) :
    ∃ A ∈ PairResampling.pairs n, PairResampling.SameFiber A G.val H.val := by
  obtain ⟨p, hp, hresult⟩ := hstep
  obtain ⟨A, hA, hAS, hfrozen⟩ := SwitchPairFiber.exists_frozen_cut p hp
  refine ⟨A, ?_, sameFiber_of_same_side A G H ?_⟩
  · simp [PairResampling.pairs, hA]
  · intro u v hside
    have h := hfrozen u v hside
    rw [hresult] at h
    exact h.symm

theorem generator_kernel_constant_on_paths {n : ℕ} {d : Fin n → ℕ}
    (f : PairResampling.StateSpace n d) (hf : PairResampling.generator n d f = 0)
    {G H : GraphState n d} (hpath : Relation.ReflTransGen (SwitchStep n d) G H) :
    f G = f H := by
  have hfib := (PairResampling.generator_eq_zero_iff f).mp hf
  induction hpath with
  | refl => rfl
  | @tail H K hpath hstep ih =>
    obtain ⟨A, hA, hGH⟩ := switchStep_sameFiber hstep
    exact ih.trans (hfib A hA H K hGH)

theorem generator_eq_zero_iff_constant_of_connected {n : ℕ} {d : Fin n → ℕ}
    (hconn : ∀ G H : GraphState n d, Relation.ReflTransGen (SwitchStep n d) G H)
    (f : PairResampling.StateSpace n d) :
    PairResampling.generator n d f = 0 ↔ ∀ G H, f G = f H := by
  constructor
  · intro hf G H
    exact generator_kernel_constant_on_paths f hf (hconn G H)
  · intro hf
    apply (PairResampling.generator_eq_zero_iff f).mpr
    intro A hA G H hGH
    exact hf G H

end Problem315

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SwitchInFiber.lean -/
