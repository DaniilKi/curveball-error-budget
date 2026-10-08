import AnalyticConnectivity

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SpectralFromSquare.lean -/
section

namespace OAI

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace Problem315.Analytic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem norm_sq_le_inner_of_square_ge
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hpos : ∀ x : E, 0 ≤ ⟪x, T x⟫)
    (hsquare : ∀ x : E, ⟪x, T x⟫ ≤ ⟪T x, T x⟫)
    (x : E) (hx : ∀ y : E, T y = 0 → ⟪y, x⟫ = 0) :
    ‖x‖ ^ 2 ≤ ⟪x, T x⟫ := by
  classical
  let b := hT.eigenvectorBasis (rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  let ev := hT.eigenvalues (rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  have hbe (i : Fin (Module.finrank ℝ E)) : T (b i) = ev i • b i :=
    hT.apply_eigenvectorBasis rfl i
  have hunit (i : Fin (Module.finrank ℝ E)) : ⟪b i, b i⟫ = 1 :=
    by rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i]; norm_num
  have hevpos (i : Fin (Module.finrank ℝ E)) : 0 ≤ ev i := by
    simpa only [hbe, inner_smul_right, hunit, mul_one] using hpos (b i)
  have hevsquare (i : Fin (Module.finrank ℝ E)) : ev i ≤ (ev i) ^ 2 := by
    simpa only [hbe, inner_smul_left, inner_smul_right, hunit, mul_one,
      RCLike.conj_to_real, pow_two] using hsquare (b i)
  rw [← b.sum_sq_inner_right x, ← b.sum_inner_mul_inner x (T x)]
  apply Finset.sum_le_sum
  intro i hi
  have hcoord : ⟪b i, T x⟫ = ev i * ⟪b i, x⟫ := by
    rw [← hT (b i) x, hbe, inner_smul_left]
    simp
  have hcomm : ⟪x, b i⟫ = ⟪b i, x⟫ := real_inner_comm _ _
  rw [hcoord, hcomm]
  by_cases he : ev i = 0
  · have hz : ⟪b i, x⟫ = 0 := hx (b i) (by simp [hbe, he])
    simp [hz]
  · have hone : 1 ≤ ev i := by
      have hp := hevpos i
      have hs := hevsquare i
      have hp' : 0 < ev i := lt_of_le_of_ne hp (Ne.symm he)
      nlinarith
    nlinarith [sq_nonneg ⟪b i, x⟫]

theorem norm_apply_le_of_inner_bounds
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) {r : ℝ} (hr : 0 ≤ r)
    (hpos : ∀ x : E, 0 ≤ ⟪x, T x⟫)
    (hbound : ∀ x : E, ⟪x, T x⟫ ≤ r * ‖x‖ ^ 2)
    (x : E) : ‖T x‖ ≤ r * ‖x‖ := by
  classical
  let b := hT.eigenvectorBasis (rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  let ev := hT.eigenvalues (rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  have hbe (i : Fin (Module.finrank ℝ E)) : T (b i) = ev i • b i :=
    hT.apply_eigenvectorBasis rfl i
  have hunit (i : Fin (Module.finrank ℝ E)) : ⟪b i, b i⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i]
    norm_num
  have hev (i : Fin (Module.finrank ℝ E)) : 0 ≤ ev i ∧ ev i ≤ r := by
    constructor
    · simpa only [hbe, inner_smul_right, hunit, mul_one] using hpos (b i)
    · simpa only [hbe, inner_smul_right, hunit, mul_one, b.orthonormal.1 i,
        one_pow] using hbound (b i)
  have hsq : ‖T x‖ ^ 2 ≤ (r * ‖x‖) ^ 2 := by
    rw [mul_pow, ← b.sum_sq_inner_right (T x), ← b.sum_sq_inner_right x,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hcoord : ⟪b i, T x⟫ = ev i * ⟪b i, x⟫ := by
      rw [← hT (b i) x, hbe, inner_smul_left]
      simp
    rw [hcoord, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (hev i).1 (hev i).2 2
  nlinarith [norm_nonneg (T x), norm_nonneg x, mul_nonneg hr (norm_nonneg x)]

omit [FiniteDimensional ℝ E] in

theorem norm_iterate_le
    (T : E →ₗ[ℝ] E) {r : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ x : E, ‖T x‖ ≤ r * ‖x‖) (t : ℕ) (x : E) :
    ‖(T : E → E)^[t] x‖ ≤ r ^ t * ‖x‖ := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      calc
        ‖T ((T : E → E)^[t] x)‖ ≤ r * ‖(T : E → E)^[t] x‖ := hbound _
        _ ≤ r * (r ^ t * ‖x‖) := mul_le_mul_of_nonneg_left ih hr
        _ = r ^ (t + 1) * ‖x‖ := by ring

theorem norm_iterate_le_exp_of_inner_bounds
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) {γ : ℝ} (hγ : γ ≤ 1)
    (hpos : ∀ x : E, 0 ≤ ⟪x, T x⟫)
    (hgap : ∀ x : E, ⟪x, T x⟫ ≤ (1 - γ) * ‖x‖ ^ 2)
    (t : ℕ) (x : E) :
    ‖(T : E → E)^[t] x‖ ≤ Real.exp (-γ * (t : ℝ)) * ‖x‖ := by
  have hr : 0 ≤ 1 - γ := sub_nonneg.mpr hγ
  calc
    ‖(T : E → E)^[t] x‖ ≤ (1 - γ) ^ t * ‖x‖ :=
      norm_iterate_le T hr (norm_apply_le_of_inner_bounds T hT hr hpos hgap) t x
    _ ≤ (Real.exp (-γ)) ^ t * ‖x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
      exact pow_le_pow_left₀ hr (Real.one_sub_le_exp_neg γ) t
    _ = Real.exp (-γ * (t : ℝ)) * ‖x‖ := by
      rw [← Real.exp_nat_mul]
      congr 2
      ring

end Problem315.Analytic

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SpectralFromSquare.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairPoincare.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Problem315.PairResampling
attribute [local instance] Classical.propDecidable

theorem generator_centered_poincare {n : Nat} {d : Fin n → Nat}
    (hsquare : ∀ f : StateSpace n d,
      ⟪f, generator n d f⟫ ≤ ⟪generator n d f, generator n d f⟫)
    (f : StateSpace n d) (hf : ∑ G : GraphState n d, f G = 0) :
    ‖f‖ ^ 2 ≤ ⟪f, generator n d f⟫ := by
  classical
  apply Analytic.norm_sq_le_inner_of_square_ge (generator n d).toLinearMap
    generator_isSymmetric generator_nonneg hsquare f
  intro y hy
  have hconst := (generator_eq_zero_iff_constant y).mp hy
  by_cases hne : Nonempty (GraphState n d)
  · let G : GraphState n d := Classical.choice hne
    rw [state_inner]
    simp_rw [hconst _ G]
    rw [← Finset.mul_sum, hf, mul_zero]
  · have : IsEmpty (GraphState n d) := not_nonempty_iff.mp hne
    simp [state_inner]

theorem uniformVariance_le_generator {n : Nat} {d : Fin n → Nat}
    (hgraph : Graphical n d)
    (hsquare : ∀ f : StateSpace n d,
      ⟪f, generator n d f⟫ ≤ ⟪generator n d f, generator n d f⟫)
    (f : GraphState n d → ℝ) :
    uniformVariance n d f ≤
      ⟪WithLp.toLp 2 f, generator n d (WithLp.toLp 2 f)⟫ / (stateCount n d : ℝ) := by
  classical
  let : Nonempty (GraphState n d) := hgraph
  have hN : (0 : ℝ) < (stateCount n d : ℝ) := by
    exact_mod_cast (show 0 < stateCount n d by
      simpa only [stateCount, allGraphStates, Finset.card_univ] using
        (Fintype.card_pos (α := GraphState n d)))
  let v : StateSpace n d := WithLp.toLp 2 f
  let c : ℝ := uniformAverage n d f
  let k : StateSpace n d := WithLp.toLp 2 (fun _ : GraphState n d => c)
  let x : StateSpace n d := v - k
  have hx : (∑ G : GraphState n d, x G) = 0 := by
    simp only [x, v, k, PiLp.sub_apply]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change (∑ G : GraphState n d, f G) - (Fintype.card (GraphState n d) : ℝ) *
      ((∑ G : GraphState n d, f G) / (stateCount n d : ℝ)) = 0
    have hcard : (Fintype.card (GraphState n d) : ℝ) = stateCount n d := rfl
    rw [hcard]
    field_simp
    ring
  have hk : generator n d k = 0 := generator_constant c
  have hgen : generator n d x = generator n d v := by
    change generator n d (v - k) = generator n d v
    rw [map_sub, hk, sub_zero]
  have horth : ⟪k, generator n d v⟫ = 0 := by
    have h := generator_isSymmetric (n := n) (d := d) k v
    change ⟪generator n d k, v⟫ = ⟪k, generator n d v⟫ at h
    rw [hk, inner_zero_left] at h
    exact h.symm
  have henergy : ⟪x, generator n d x⟫ = ⟪v, generator n d v⟫ := by
    rw [hgen]
    change ⟪v - k, generator n d v⟫ = _
    rw [inner_sub_left, horth, sub_zero]
  have hnorm : ‖x‖ ^ 2 = ∑ G ∈ allGraphStates n d, (f G - c) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, state_inner]
    simp only [x, v, k, PiLp.sub_apply, allGraphStates, pow_two]
  have hp := generator_centered_poincare hsquare x hx
  rw [henergy, hnorm] at hp
  exact div_le_div_of_nonneg_right hp (le_of_lt hN)

theorem spectralGap_of_square_and_comparison {n : Nat} {d : Fin n → Nat}
    (hn : 4 ≤ n) (hgraph : Graphical n d)
    (hsquare : ∀ f : StateSpace n d,
      ⟪f, generator n d f⟫ ≤ ⟪generator n d f, generator n d f⟫)
    (hcomparison : ∀ f : GraphState n d → ℝ,
      ⟪WithLp.toLp 2 f, generator n d (WithLp.toLp 2 f)⟫ / (stateCount n d : ℝ) ≤
        (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ)) * dirichletEnergy n d f) :
    hasSpectralGapAtLeast n d ((1 : ℝ) /
      (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc : (0 : ℝ) < (Nat.choose n 4 : ℝ) := by exact_mod_cast Nat.choose_pos hn
  have hD : (0 : ℝ) < 24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ) := by positivity
  intro f
  have h := (uniformVariance_le_generator hgraph hsquare f).trans (hcomparison f)
  rw [one_div, ← div_eq_inv_mul]
  apply (div_le_iff₀ hD).mpr
  simpa only [mul_comm] using h

end Problem315.PairResampling

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairPoincare.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairAggregation.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairAggregation

variable {V : Type*} [DecidableEq V]

lemma card_union_of_pairs {a b : Finset V} (ha : a.card = 2) (hb : b.card = 2)
    (hne : a ≠ b) (hnd : ¬ Disjoint a b) : (a ∪ b).card = 3 := by
  have hi_pos : 0 < (a ∩ b).card := by
    apply Finset.card_pos.mpr
    exact Finset.not_disjoint_iff_nonempty_inter.mp hnd
  have hi_le : (a ∩ b).card ≤ 2 := by
    simpa [ha] using Finset.card_le_card (Finset.inter_subset_left : a ∩ b ⊆ a)
  have hi_ne : (a ∩ b).card ≠ 2 := by
    intro hi
    have hia : a ∩ b = a := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hab : a ⊆ b := by rw [← hia]; exact Finset.inter_subset_right
    exact hne (Finset.eq_of_subset_of_card_le hab (by omega))
  have h := Finset.card_union_add_card_inter a b
  omega

lemma triple_incidence_count (s a b : Finset V) (ha : a.card = 2) (hb : b.card = 2)
    (has : a ⊆ s) (hbs : b ⊆ s) :
    ((s.powersetCard 3).filter (fun T => a ⊆ T ∧ b ⊆ T)).card =
      if a = b then s.card - 2 else if Disjoint a b then 0 else 1 := by
  have hfilter : (s.powersetCard 3).filter (fun T => a ⊆ T ∧ b ⊆ T) =
      (s.powersetCard 3).filter (a ∪ b ⊆ ·) := by
    ext T
    simp only [Finset.mem_filter, Finset.union_subset_iff]
  rw [hfilter]
  by_cases hab : a = b
  · subst b
    simp only [Finset.union_self]
    rw [Finset.card_filter_powersetCard_subset a s 3 has (by omega), ha]
    simp
  · simp only [ite_eq_right hab]
    by_cases hd : Disjoint a b
    · rw [ite_eq_left hd]
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro T hT
      obtain ⟨hT, huT⟩ := Finset.mem_filter.mp hT
      have hcard := Finset.card_le_card huT
      have hTu := (Finset.mem_powersetCard.mp hT).2
      have hu := Finset.card_union_of_disjoint hd
      omega
    · rw [ite_eq_right hd]
      have hu := card_union_of_pairs ha hb hab hd
      rw [Finset.card_filter_powersetCard_subset (a ∪ b) s 3
        (Finset.union_subset has hbs) (by omega), hu]
      simp

lemma sum_triple_incidence (s : Finset V) (B : Finset V → Finset V → ℝ) :
    (∑ T ∈ s.powersetCard 3, ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
      if a ⊆ T ∧ b ⊆ T then B a b else 0) =
    ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
      (((s.powersetCard 3).filter (fun T => a ⊆ T ∧ b ⊆ T)).card : ℝ) * B a b := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← Finset.sum_filter]
  simp

lemma triple_expansion (s : Finset V) (hs : 3 ≤ s.card)
    (B : Finset V → Finset V → ℝ) :
    (∑ T ∈ s.powersetCard 3, ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
      if a ⊆ T ∧ b ⊆ T then B a b else 0) =
    (∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2, B a b) +
      (s.card - 3 : ℕ) * (∑ a ∈ s.powersetCard 2, B a a) -
      (∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
        if Disjoint a b then B a b else 0) := by
  rw [sum_triple_incidence]
  have hpoint : ∀ a ∈ s.powersetCard 2, ∀ b ∈ s.powersetCard 2,
      (((s.powersetCard 3).filter (fun T => a ⊆ T ∧ b ⊆ T)).card : ℝ) * B a b =
        B a b + (if a = b then (s.card - 3 : ℕ) * B a b else 0) -
          (if Disjoint a b then B a b else 0) := by
    intro a ha b hb
    obtain ⟨has, ha⟩ := Finset.mem_powersetCard.mp ha
    obtain ⟨hbs, hb⟩ := Finset.mem_powersetCard.mp hb
    rw [triple_incidence_count s a b ha hb has hbs]
    by_cases he : a = b
    · subst b
      have hnd : ¬ Disjoint a a := by
        intro hd
        have he := disjoint_self.mp hd
        simp [he] at ha
      simp only [ite_eq_right hnd]
      have hc : s.card - 2 = (s.card - 3) + 1 := by omega
      rw [hc]
      push_cast
      ring
    · by_cases hd : Disjoint a b <;> simp [he, hd]
  simp_rw [Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (hpoint a ha))]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  congr 2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp [ha]

lemma sum_pair_terms_over_triples (s : Finset V) (h : Finset V → ℝ) :
    (∑ T ∈ s.powersetCard 3, ∑ a ∈ s.powersetCard 2,
      if a ⊆ T then h a else 0) =
      (s.card - 2 : ℕ) * (∑ a ∈ s.powersetCard 2, h a) := by
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  obtain ⟨has, ha⟩ := Finset.mem_powersetCard.mp ha
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_filter_powersetCard_subset a s 3 has (by omega), ha]
  simp

theorem global_of_local_ambient (s : Finset V) (hs : 3 ≤ s.card)
    (h : Finset V → ℝ) (B : Finset V → Finset V → ℝ)
    (hdiag : ∀ a ∈ s.powersetCard 2, B a a = h a)
    (htriple : ∀ T ∈ s.powersetCard 3,
      (∑ a ∈ s.powersetCard 2, if a ⊆ T then h a else 0) ≤
      ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
        if a ⊆ T ∧ b ⊆ T then B a b else 0)
    (hdisjoint : 0 ≤ ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
      if Disjoint a b then B a b else 0) :
    (∑ a ∈ s.powersetCard 2, h a) ≤
      ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2, B a b := by
  have hsum := Finset.sum_le_sum htriple
  rw [sum_pair_terms_over_triples, triple_expansion s hs] at hsum
  have hd : (∑ a ∈ s.powersetCard 2, B a a) =
      ∑ a ∈ s.powersetCard 2, h a := Finset.sum_congr rfl hdiag
  rw [hd] at hsum
  have hc : s.card - 2 = (s.card - 3) + 1 := by omega
  rw [hc] at hsum
  push_cast at hsum
  nlinarith

lemma pairSum_restrict (s T : Finset V) (hTs : T ⊆ s) (f : Finset V → ℝ) :
    (∑ a ∈ s.powersetCard 2, if a ⊆ T then f a else 0) =
      ∑ a ∈ T.powersetCard 2, f a := by
  rw [← Finset.sum_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨has, ha⟩, haT⟩
    exact ⟨haT, ha⟩
  · rintro ⟨haT, ha⟩
    exact ⟨⟨haT.trans hTs, ha⟩, haT⟩

lemma local_quadratic_restrict (s T : Finset V) (hTs : T ⊆ s)
    (B : Finset V → Finset V → ℝ) :
    (∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
      if a ⊆ T ∧ b ⊆ T then B a b else 0) =
      ∑ a ∈ T.powersetCard 2, ∑ b ∈ T.powersetCard 2, B a b := by
  have he : (∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
      if a ⊆ T ∧ b ⊆ T then B a b else 0) =
      ∑ a ∈ s.powersetCard 2, if a ⊆ T then
        (∑ b ∈ s.powersetCard 2, if b ⊆ T then B a b else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    by_cases haT : a ⊆ T <;> simp [haT]
  rw [he, pairSum_restrict s T hTs]
  apply Finset.sum_congr rfl
  intro a ha
  exact pairSum_restrict s T hTs (B a)

theorem global_of_local (s : Finset V) (hs : 3 ≤ s.card)
    (h : Finset V → ℝ) (B : Finset V → Finset V → ℝ)
    (hdiag : ∀ a ∈ s.powersetCard 2, B a a = h a)
    (htriple : ∀ T ∈ s.powersetCard 3,
      (∑ a ∈ T.powersetCard 2, h a) ≤
      ∑ a ∈ T.powersetCard 2, ∑ b ∈ T.powersetCard 2, B a b)
    (hdisjoint : 0 ≤ ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
      if Disjoint a b then B a b else 0) :
    (∑ a ∈ s.powersetCard 2, h a) ≤
      ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2, B a b := by
  apply global_of_local_ambient s hs h B hdiag _ hdisjoint
  intro T hT
  have hTs := (Finset.mem_powersetCard.mp hT).1
  rw [pairSum_restrict s T hTs, local_quadratic_restrict s T hTs]
  exact htriple T hT

end Problem315.PairAggregation

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairAggregation.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairGeneratorSquare.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairResampling

attribute [local instance] Classical.propDecidable

def tripleGenerator (n : Nat) (d : Fin n → Nat) (T : Finset (Fin n)) :
    StateSpace n d →L[ℝ] StateSpace n d :=
  ∑ a ∈ T.powersetCard 2, fluctuation n d a

theorem tripleGenerator_apply {n : Nat} {d : Fin n → Nat}
    (T : Finset (Fin n)) (f : StateSpace n d) :
    tripleGenerator n d T f = ∑ a ∈ T.powersetCard 2, fluctuation n d a f := by
  simp [tripleGenerator]

theorem inner_tripleGenerator {n : Nat} {d : Fin n → Nat}
    (T : Finset (Fin n)) (f : StateSpace n d) :
    ⟪f, tripleGenerator n d T f⟫ =
      ∑ a ∈ T.powersetCard 2, ‖fluctuation n d a f‖ ^ 2 := by
  simp only [tripleGenerator_apply, inner_sum, inner_fluctuation]

theorem generator_square_of_local {n : Nat} {d : Fin n → Nat}
    (hn : 3 ≤ n) (f : StateSpace n d)
    (htriple : ∀ T : Finset (Fin n), T.card = 3 →
      ⟪f, tripleGenerator n d T f⟫ ≤
        ⟪tripleGenerator n d T f, tripleGenerator n d T f⟫)
    (hdisjoint : 0 ≤ ∑ a ∈ pairs n, ∑ b ∈ pairs n,
      if Disjoint a b then ⟪fluctuation n d a f, fluctuation n d b f⟫ else 0) :
    ⟪f, generator n d f⟫ ≤ ⟪generator n d f, generator n d f⟫ := by
  rw [inner_generator]
  simp only [generator_apply]
  simp only [sum_inner]
  simp only [inner_sum]
  apply PairAggregation.global_of_local (Finset.univ : Finset (Fin n)) (by simpa using hn)
    (fun a => ‖fluctuation n d a f‖ ^ 2)
    (fun a b => ⟪fluctuation n d a f, fluctuation n d b f⟫)
  · intro a ha
    exact real_inner_self_eq_norm_sq _
  · intro T hT
    have hcard := (Finset.mem_powersetCard.mp hT).2
    have h := htriple T hcard
    rw [inner_tripleGenerator] at h
    simp only [tripleGenerator_apply] at h
    simp only [sum_inner] at h
    simp only [inner_sum] at h
    exact h
  · exact hdisjoint

end Problem315.PairResampling

namespace Problem315

attribute [local instance] Classical.propDecidable

theorem spectralGap_of_local_pair_bounds (n : Nat) (d : Fin n → Nat)
    (hn : 4 ≤ n) (hgraphical : Graphical n d)
    (htriple : ∀ (f : PairResampling.StateSpace n d) (T : Finset (Fin n)),
      T.card = 3 →
      ⟪f, PairResampling.tripleGenerator n d T f⟫ ≤
        ⟪PairResampling.tripleGenerator n d T f, PairResampling.tripleGenerator n d T f⟫)
    (hdisjoint : ∀ f : PairResampling.StateSpace n d,
      0 ≤ ∑ a ∈ PairResampling.pairs n, ∑ b ∈ PairResampling.pairs n,
        if Disjoint a b then
          ⟪PairResampling.fluctuation n d a f, PairResampling.fluctuation n d b f⟫ else 0)
    (hcomparison : ∀ f : PairResampling.StateSpace n d,
      uniformInner n d (fun G => f G) (fun G => PairResampling.generator n d f G) ≤
        (24 * (n : ℝ) ^ 2 * (n.choose 4 : ℝ)) *
          dirichletEnergy n d (fun G => f G)) :
    hasSpectralGapAtLeast n d ((1 : ℝ) / (24 * (n : ℝ) ^ 2 * (n.choose 4 : ℝ))) := by
  apply PairResampling.spectralGap_of_square_and_comparison hn hgraphical
  · intro f
    exact PairResampling.generator_square_of_local (by omega) f (htriple f) (hdisjoint f)
  · intro f
    rw [PairResampling.state_inner]
    exact hcomparison (WithLp.toLp 2 f)

end Problem315

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairGeneratorSquare.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/ActualTripleSquare.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairResampling
attribute [local instance] Classical.propDecidable

theorem tripleGenerator_square {n : ℕ} {d : Fin n → ℕ}
    (f : StateSpace n d) (T : Finset (Fin n)) (hT : T.card = 3) :
    ⟪f, tripleGenerator n d T f⟫ ≤
      ⟪tripleGenerator n d T f, tripleGenerator n d T f⟫ := by
  rw [real_inner_self_eq_norm_sq, tripleGenerator_apply]
  exact TripleActualRowBound.triple_square T hT f

end Problem315.PairResampling

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/ActualTripleSquare.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/ProjectionTools.lean -/
section

namespace OAI

namespace Problem315
namespace ProjectionTools

open scoped BigOperators

theorem rankOne_plane_bound (x y ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    -(x ^ 2 + y ^ 2) * (1 - ρ ^ 2) ≤
      2 * x * y * ρ * (1 - ρ ^ 2) := by
  have hfac : 0 ≤ 1 - ρ ^ 2 := by nlinarith
  have hbase : -(x ^ 2 + y ^ 2) ≤ 2 * x * y * ρ := by
    have hplus := sq_nonneg (x + y)
    have hminus := sq_nonneg (x - y)
    have hleft := mul_nonneg hρ0 hplus
    have hright := mul_nonneg (sub_nonneg.mpr hρ1) (add_nonneg (sq_nonneg x) (sq_nonneg y))
    nlinarith
  exact mul_le_mul_of_nonneg_right hbase hfac

theorem sum_disjoint_nonneg {ι : Type*} [DecidableEq ι]
    (s : Finset (ι × ι)) (cross gain err : ι → ι → ℝ)
    (hsymm : ∀ p ∈ s, p.swap ∈ s)
    (hlocal : ∀ a b, (a,b) ∈ s →
      2 * gain a b - err a b - err b a ≤ 2 * cross a b)
    (hbudget : (∑ p ∈ s, err p.1 p.2) ≤ ∑ p ∈ s, gain p.1 p.2) :
    0 ≤ ∑ p ∈ s, cross p.1 p.2 := by
  have hswap : (∑ p ∈ s, err p.2 p.1) = ∑ p ∈ s, err p.1 p.2 := by
    apply Finset.sum_bij (fun p _ => p.swap)
    · intro p hp
      exact hsymm p hp
    · intro p hp q hq hpq
      exact Prod.swap_injective hpq
    · intro p hp
      exact ⟨p.swap, hsymm p hp, Prod.swap_swap p⟩
    · intro p hp
      rfl
  have hsum := Finset.sum_le_sum (s := s) (fun p hp => hlocal p.1 p.2 hp)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  rw [hswap] at hsum
  linarith

theorem slice_numerator_bound (N q r : ℝ) (hN : 3 ≤ N)
    (hq : 1 ≤ q) (hr : 1 ≤ r) (hsum : q + r = N) :
    (2 * q - N) ^ 2 * (N - 1) ≤
      (N - 2) * (q * (q - 1) + r * (r - 1)) := by
  have hqr : N - 1 ≤ q * r := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hr)]
  have hprod : 0 ≤ 2 * N * (q * r - (N - 1)) :=
    mul_nonneg (by linarith) (by linarith)
  rw [← hsum] at hprod ⊢
  nlinarith

theorem slice_mu_one_le (N q r : ℝ) (hN : 3 ≤ N)
    (hq : 1 ≤ q) (hr : 1 ≤ r) (hsum : q + r = N) :
    (2 * q - N) ^ 2 /
      (2 * (N - 2) * ((q * (q - 1) + r * (r - 1)) / (N * (N - 1)))) ≤
      N / 2 := by
  have hN0 : 0 < N := by linarith
  have hN1 : 0 < N - 1 := by linarith
  have hN2 : 0 < N - 2 := by linarith
  have hnum : 0 < q * (q - 1) + r * (r - 1) := by
    nlinarith [sq_nonneg (q - 1), sq_nonneg (r - 1)]
  have hp : 0 < (q * (q - 1) + r * (r - 1)) / (N * (N - 1)) :=
    div_pos hnum (mul_pos hN0 hN1)
  apply (div_le_iff₀ (mul_pos (mul_pos (by norm_num) hN2) hp)).mpr
  have hb := slice_numerator_bound N q r hN hq hr hsum
  apply (mul_le_mul_iff_of_pos_right (mul_pos hN0 hN1)).mp
  field_simp
  nlinarith [mul_nonneg (le_of_lt hN0) (sub_nonneg.mpr hb)]

theorem slice_mu_two_le (N μ : ℝ) (hN : 4 ≤ N)
    (htrace : (N * (N - 1) / 2 - N) * μ ≤ N * (N - 1) / 2) :
    μ ≤ N - 1 := by
  have hNpos : 0 < N := by linarith
  have hdim : 0 < N * (N - 1) / 2 - N := by nlinarith
  have hpoly : N * (N - 1) / 2 ≤
      (N * (N - 1) / 2 - N) * (N - 1) := by
    have hfactor := mul_nonneg (mul_nonneg (le_of_lt hNpos) (by linarith : 0 ≤ N - 1))
      (by linarith : 0 ≤ N - 4)
    nlinarith
  exact (mul_le_mul_iff_of_pos_left hdim).mp (htrace.trans hpoly)

theorem disjoint_event_correlation (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hpq : p + q < 1) :
    0 < Real.sqrt (p * q / ((1 - p) * (1 - q))) ∧
      Real.sqrt (p * q / ((1 - p) * (1 - q))) < 1 := by
  have hp1 : 0 < 1 - p := by linarith
  have hq1 : 0 < 1 - q := by linarith
  have hden : 0 < (1 - p) * (1 - q) := mul_pos hp1 hq1
  have hratio : 0 < p * q / ((1 - p) * (1 - q)) := div_pos (mul_pos hp hq) hden
  constructor
  · exact Real.sqrt_pos.mpr hratio
  · apply (Real.sqrt_lt (le_of_lt hratio) (by norm_num : (0 : ℝ) ≤ 1)).mpr
    apply (div_lt_iff₀ hden).mpr
    nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open scoped RealInnerProductSpace

theorem inner_error_bound (a b : E) :
    -(‖a‖ ^ 2 + ‖b‖ ^ 2) ≤ 2 * ⟪a, b⟫ := by
  have h : 0 ≤ ⟪a + b, a + b⟫ := real_inner_self_nonneg
  simp only [inner_add_left, inner_add_right, real_inner_self_eq_norm_sq,
    real_inner_comm b a] at h
  rw [real_inner_comm a b] at h
  linarith

theorem interaction_of_orthogonal_decomposition (z a b g ra rb : E)
    (hza : ⟪z, a⟫ = 0) (hzb : ⟪z, b⟫ = 0)
    (hg : ‖g‖ ≤ ‖z‖) (ha : ‖a‖ ≤ ‖ra‖) (hb : ‖b‖ ≤ ‖rb‖) :
    2 * ‖g‖ ^ 2 - ‖ra‖ ^ 2 - ‖rb‖ ^ 2 ≤
      2 * ⟪z + a, z + b⟫ := by
  have hga : ‖g‖ ^ 2 ≤ ‖z‖ ^ 2 := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hg
  have haa : ‖a‖ ^ 2 ≤ ‖ra‖ ^ 2 := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr ha
  have hbb : ‖b‖ ^ 2 ≤ ‖rb‖ ^ 2 := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hb
  have hab := inner_error_bound a b
  have haz : ⟪a, z⟫ = 0 := by rw [real_inner_comm, hza]
  simp only [inner_add_left, inner_add_right, real_inner_self_eq_norm_sq,
    hzb, haz, add_zero, zero_add]
  linarith

end ProjectionTools
end Problem315

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/ProjectionTools.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairDisjointBudget.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairResampling
attribute [local instance] Classical.propDecidable

theorem disjoint_sum_nonneg_of_interaction_budget {n : ℕ} {d : Fin n → ℕ}
    (f : StateSpace n d)
    (g R : Finset (Fin n) → Finset (Fin n) → StateSpace n d → StateSpace n d)
    (hlocal : ∀ a ∈ pairs n, ∀ b ∈ pairs n, Disjoint a b →
      2 * ‖g a b f‖ ^ 2 - ‖R a b f‖ ^ 2 - ‖R b a f‖ ^ 2 ≤
        2 * ⟪fluctuation n d a f, fluctuation n d b f⟫)
    (hbudget : ∀ a ∈ pairs n,
      (∑ b ∈ pairs n, if Disjoint a b then ‖R a b f‖ ^ 2 else 0) ≤
        ∑ b ∈ pairs n, if Disjoint a b then ‖g a b f‖ ^ 2 else 0) :
    0 ≤ ∑ a ∈ pairs n, ∑ b ∈ pairs n,
      if Disjoint a b then ⟪fluctuation n d a f, fluctuation n d b f⟫ else 0 := by
  classical
  let s := (pairs n ×ˢ pairs n).filter (fun p => Disjoint p.1 p.2)
  have hmem (a b : Finset (Fin n)) :
      (a,b) ∈ s ↔ a ∈ pairs n ∧ b ∈ pairs n ∧ Disjoint a b := by
    simp only [s, Finset.mem_filter, Finset.mem_product]
    tauto
  have hsum (F : Finset (Fin n) → Finset (Fin n) → ℝ) :
      (∑ p ∈ s, F p.1 p.2) =
        ∑ a ∈ pairs n, ∑ b ∈ pairs n, if Disjoint a b then F a b else 0 := by
    rw [show s = (pairs n ×ˢ pairs n).filter
      (fun p => Disjoint p.1 p.2) from rfl, Finset.sum_filter, Finset.sum_product]
  have h := ProjectionTools.sum_disjoint_nonneg s
    (fun a b => ⟪fluctuation n d a f, fluctuation n d b f⟫)
    (fun a b => ‖g a b f‖ ^ 2) (fun a b => ‖R a b f‖ ^ 2) ?_ ?_ ?_
  · rw [hsum (fun a b => ⟪fluctuation n d a f, fluctuation n d b f⟫)] at h
    exact h
  · rintro ⟨a,b⟩ hab
    have hp := (hmem a b).mp hab
    exact (hmem b a).mpr ⟨hp.2.1, hp.1, hp.2.2.symm⟩
  · intro a b hab
    have hp := (hmem a b).mp hab
    exact hlocal a hp.1 b hp.2.1 hp.2.2
  · rw [hsum (fun a b => ‖R a b f‖ ^ 2), hsum (fun a b => ‖g a b f‖ ^ 2)]
    exact Finset.sum_le_sum hbudget

theorem generator_square_of_interaction_budget {n : ℕ} {d : Fin n → ℕ}
    (hn : 3 ≤ n) (f : StateSpace n d)
    (g R : Finset (Fin n) → Finset (Fin n) → StateSpace n d → StateSpace n d)
    (htriple : ∀ T : Finset (Fin n), T.card = 3 →
      ⟪f, tripleGenerator n d T f⟫ ≤
        ⟪tripleGenerator n d T f, tripleGenerator n d T f⟫)
    (hlocal : ∀ a ∈ pairs n, ∀ b ∈ pairs n, Disjoint a b →
      2 * ‖g a b f‖ ^ 2 - ‖R a b f‖ ^ 2 - ‖R b a f‖ ^ 2 ≤
        2 * ⟪fluctuation n d a f, fluctuation n d b f⟫)
    (hbudget : ∀ a ∈ pairs n,
      (∑ b ∈ pairs n, if Disjoint a b then ‖R a b f‖ ^ 2 else 0) ≤
        ∑ b ∈ pairs n, if Disjoint a b then ‖g a b f‖ ^ 2 else 0) :
    ⟪f, generator n d f⟫ ≤ ⟪generator n d f, generator n d f⟫ :=
  generator_square_of_local hn f htriple
    (disjoint_sum_nonneg_of_interaction_budget f g R hlocal hbudget)

end Problem315.PairResampling

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairDisjointBudget.lean -/
