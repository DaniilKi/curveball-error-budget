import AnalyticCrossCell

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SliceMoments.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Problem315.SliceMoments

variable {V : Type*} [sectionDecidableEqV : DecidableEq V]

def average (U : Finset V) (q : ℕ) (f : Finset V → ℝ) : ℝ :=
  (∑ S ∈ U.powersetCard q, f S) / (U.card.choose q : ℝ)

def coord (i : V) (S : Finset V) : ℝ := if i ∈ S then 1 else 0

theorem average_containment (U C : Finset V) (q : ℕ)
    (hCU : C ⊆ U) (hq : q ≤ U.card) (hCq : C.card ≤ q) :
    average U q (fun S => if C ⊆ S then 1 else 0) =
      (q.choose C.card : ℝ) / (U.card.choose C.card : ℝ) := by
  have hden : (U.card.choose q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hq).ne'
  have hdenC : (U.card.choose C.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (hCq.trans hq)).ne'
  have hmul := Nat.choose_mul (n := U.card) hCq
  have hmulR : (U.card.choose q : ℝ) * (q.choose C.card : ℝ) =
      (U.card.choose C.card : ℝ) * ((U.card - C.card).choose (q - C.card) : ℝ) := by
    exact_mod_cast hmul
  unfold average
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.card_filter_powersetCard_subset C U q hCU hCq]
  apply (div_eq_div_iff hden hdenC).mpr
  nlinarith

theorem average_containment_all (U C : Finset V) (q : ℕ)
    (hCU : C ⊆ U) (hq : q ≤ U.card) :
    average U q (fun S => if C ⊆ S then 1 else 0) =
      (q.choose C.card : ℝ) / (U.card.choose C.card : ℝ) := by
  by_cases hCq : C.card ≤ q
  · exact average_containment U C q hCU hq hCq
  · have hlt : q < C.card := by omega
    have hempty : (U.powersetCard q).filter (C ⊆ ·) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro S hS hCS
      have hcard := Finset.card_le_card hCS
      have hScard := (Finset.mem_powersetCard.mp hS).2
      omega
    unfold average
    rw [← Finset.sum_filter, hempty]
    simp [Nat.choose_eq_zero_of_lt hlt]

theorem average_coord (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (i : V) (hi : i ∈ U) :
    average U q (coord i) = (q : ℝ) / U.card := by
  change average U q (fun S => if i ∈ S then 1 else 0) = _
  simpa using average_containment_all U {i} q
    (Finset.singleton_subset_iff.mpr hi) hq

theorem average_coord_mul (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (i j : V) (hi : i ∈ U) (hj : j ∈ U) (hne : i ≠ j) :
    average U q (fun S => coord i S * coord j S) =
      (q : ℝ) * ((q : ℝ) - 1) / ((U.card : ℝ) * ((U.card : ℝ) - 1)) := by
  have hpair : ({i, j} : Finset V).card = 2 := by simp [hne]
  have hCU : ({i, j} : Finset V) ⊆ U := by simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hi, hj]
  have hfun : (fun S => coord i S * coord j S) =
      (fun S : Finset V => if ({i, j} : Finset V) ⊆ S then (1 : ℝ) else 0) := by
    funext S
    by_cases hiS : i ∈ S <;> by_cases hjS : j ∈ S <;> simp [coord, Finset.insert_subset_iff, Finset.singleton_subset_iff, hiS, hjS]
  rw [hfun, average_containment_all U {i, j} q hCU hq, hpair,
    Nat.cast_choose_two, Nat.cast_choose_two]
  exact div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0) _ _

@[simp] theorem coord_sq (i : V) (S : Finset V) : (coord i S)^2 = coord i S := by
  by_cases hi : i ∈ S <;> simp [coord, hi]

include sectionDecidableEqV in
@[simp] theorem average_add (U : Finset V) (q : ℕ) (f g : Finset V → ℝ) :
    average U q (fun S => f S + g S) = average U q f + average U q g := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  simp [average, Finset.sum_add_distrib, add_div]

include sectionDecidableEqV in
@[simp] theorem average_mul_left (U : Finset V) (q : ℕ) (c : ℝ) (f : Finset V → ℝ) :
    average U q (fun S => c * f S) = c * average U q f := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  simp [average, ← Finset.mul_sum, mul_div_assoc]

include sectionDecidableEqV in
theorem average_sum {I : Type*} (U : Finset V) (q : ℕ) (s : Finset I)
    (f : I → Finset V → ℝ) :
    average U q (fun S => ∑ i ∈ s, f i S) = ∑ i ∈ s, average U q (f i) := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  unfold average
  rw [Finset.sum_comm, Finset.sum_div]

theorem average_linear (U : Finset V) (q : ℕ) (hq : q ≤ U.card) (u : V → ℝ) :
    average U q (fun S => ∑ i ∈ U, u i * coord i S) =
      ((q : ℝ) / U.card) * ∑ i ∈ U, u i := by
  rw [average_sum]
  simp only [average_mul_left]
  calc
    (∑ i ∈ U, u i * average U q (coord i)) =
        ∑ i ∈ U, u i * ((q : ℝ) / U.card) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [average_coord U q hq i hi]
    _ = ((q : ℝ) / U.card) * ∑ i ∈ U, u i := by
      rw [← Finset.sum_mul]
      ring

theorem average_linear_sq (U : Finset V) (q : ℕ) (hq : q ≤ U.card) (u : V → ℝ) :
    average U q (fun S => (∑ i ∈ U, u i * coord i S)^2) =
      ((q : ℝ) / U.card -
        (q : ℝ) * ((q : ℝ) - 1) / ((U.card : ℝ) * ((U.card : ℝ) - 1))) *
        (∑ i ∈ U, (u i)^2) +
      ((q : ℝ) * ((q : ℝ) - 1) / ((U.card : ℝ) * ((U.card : ℝ) - 1))) *
        (∑ i ∈ U, u i)^2 := by
  let p₁ : ℝ := (q : ℝ) / U.card
  let p₂ : ℝ := (q : ℝ) * ((q : ℝ) - 1) /
    ((U.card : ℝ) * ((U.card : ℝ) - 1))
  have hm : ∀ i ∈ U, ∀ j ∈ U,
      average U q (fun S => coord i S * coord j S) = if i = j then p₁ else p₂ := by
    intro i hi j hj
    by_cases hij : i = j
    · subst j
      simpa only [↓reduceIte, ← pow_two, coord_sq] using average_coord U q hq i hi
    · simpa only [ite_eq_right hij] using average_coord_mul U q hq i j hi hj hij
  have hfun : (fun S => (∑ i ∈ U, u i * coord i S)^2) =
      (fun S => ∑ i ∈ U, ∑ j ∈ U, (u i * u j) * (coord i S * coord j S)) := by
    funext S
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hfun, average_sum]
  simp only [average_sum, average_mul_left]
  have hrearrange : (∑ i ∈ U, ∑ j ∈ U,
      (u i * u j) * average U q (fun S => coord i S * coord j S)) =
      ∑ i ∈ U, ∑ j ∈ U,
        (p₂ * (u i * u j) + if i = j then (p₁ - p₂) * (u i)^2 else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hm i hi j hj]
    by_cases hij : i = j
    · subst j
      simp only [↓reduceIte]
      ring
    · simp only [ite_eq_right hij, add_zero]
      ring
  rw [hrearrange]
  have hconstant : (∑ i ∈ U, ∑ j ∈ U, p₂ * (u i * u j)) =
      p₂ * (∑ i ∈ U, u i)^2 := by
    rw [pow_two, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
  have hdiag : (∑ i ∈ U, ∑ j ∈ U,
      if i = j then (p₁ - p₂) * (u i)^2 else 0) =
      (p₁ - p₂) * ∑ i ∈ U, (u i)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [hi]
  simp only [Finset.sum_add_distrib]
  rw [hconstant, hdiag]
  change p₂ * (∑ i ∈ U, u i)^2 + (p₁ - p₂) * (∑ i ∈ U, (u i)^2) =
    (p₁ - p₂) * (∑ i ∈ U, (u i)^2) + p₂ * (∑ i ∈ U, u i)^2
  ring

theorem average_linear_zero_sum (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (u : V → ℝ) (hu : ∑ i ∈ U, u i = 0) :
    average U q (fun S => ∑ i ∈ U, u i * coord i S) = 0 := by
  rw [average_linear U q hq u, hu, mul_zero]

theorem average_linear_sq_zero_sum (U : Finset V) (q : ℕ)
    (hN : 2 ≤ U.card) (hq : q ≤ U.card) (u : V → ℝ)
    (hu : ∑ i ∈ U, u i = 0) :
    average U q (fun S => (∑ i ∈ U, u i * coord i S)^2) =
      ((q : ℝ) * ((U.card : ℝ) - q) /
        ((U.card : ℝ) * ((U.card : ℝ) - 1))) * (∑ i ∈ U, (u i)^2) := by
  have hNR : (2 : ℝ) ≤ U.card := by exact_mod_cast hN
  have hN0 : (U.card : ℝ) ≠ 0 := by linarith
  have hN1 : (U.card : ℝ) - 1 ≠ 0 := by linarith
  have hcoeff : (q : ℝ) / U.card -
      (q : ℝ) * ((q : ℝ) - 1) / ((U.card : ℝ) * ((U.card : ℝ) - 1)) =
      (q : ℝ) * ((U.card : ℝ) - q) / ((U.card : ℝ) * ((U.card : ℝ) - 1)) := by
    field_simp
    ; ring
  rw [average_linear_sq U q hq u, hu, hcoeff]
  simp

include sectionDecidableEqV in
theorem average_congr (U : Finset V) (q : ℕ) (f g : Finset V → ℝ)
    (h : ∀ S ∈ U.powersetCard q, f S = g S) : average U q f = average U q g := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  unfold average
  congr 1
  exact Finset.sum_congr rfl h

include sectionDecidableEqV in
@[simp] theorem average_const (U : Finset V) (q : ℕ) (hq : q ≤ U.card) (c : ℝ) :
    average U q (fun _ => c) = c := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  have hden : (U.card.choose q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hq).ne'
  simp [average, Finset.card_powersetCard, hden]

include sectionDecidableEqV in
@[simp] theorem average_sub (U : Finset V) (q : ℕ) (f g : Finset V → ℝ) :
    average U q (fun S => f S - g S) = average U q f - average U q g := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  simp [average, Finset.sum_sub_distrib, sub_div]

def equalIndicator (i j : V) (S : Finset V) : ℝ :=
  if (i ∈ S ↔ j ∈ S) then 1 else 0

theorem equalIndicator_eq (i j : V) (S : Finset V) :
    equalIndicator i j S = 1 - coord i S - coord j S + 2 * (coord i S * coord j S) := by
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> norm_num [equalIndicator, coord, hi, hj]

@[simp] theorem equalIndicator_sq (i j : V) (S : Finset V) :
    (equalIndicator i j S)^2 = equalIndicator i j S := by
  unfold equalIndicator
  split_ifs <;> norm_num

def equalMean (U : Finset V) (q : ℕ) : ℝ :=
  ((q : ℝ) * ((q : ℝ) - 1) +
    ((U.card : ℝ) - q) * ((U.card : ℝ) - q - 1)) /
    ((U.card : ℝ) * ((U.card : ℝ) - 1))

theorem average_equalIndicator (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (i j : V) (hi : i ∈ U) (hj : j ∈ U) (hne : i ≠ j) :
    average U q (equalIndicator i j) = equalMean U q := by
  have hN : 2 ≤ U.card := by
    have hsub : ({i, j} : Finset V) ⊆ U := by
      simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hi, hj]
    have := Finset.card_le_card hsub
    simpa [hne] using this
  have hNR : (2 : ℝ) ≤ U.card := by exact_mod_cast hN
  have hN0 : (U.card : ℝ) ≠ 0 := by linarith
  have hN1 : (U.card : ℝ) - 1 ≠ 0 := by linarith
  have hf : equalIndicator i j =
      (fun S => 1 - coord i S - coord j S + 2 * (coord i S * coord j S)) := by
    funext S
    exact equalIndicator_eq i j S
  rw [hf, average_add, average_sub, average_sub, average_const U q hq 1,
    average_coord U q hq i hi, average_coord U q hq j hj,
    average_mul_left, average_coord_mul U q hq i j hi hj hne]
  unfold equalMean
  field_simp
  ring

def centeredEqual (U : Finset V) (q : ℕ) (i j : V) (S : Finset V) : ℝ :=
  equalIndicator i j S - equalMean U q

theorem average_centeredEqual (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (i j : V) (hi : i ∈ U) (hj : j ∈ U) (hne : i ≠ j) :
    average U q (centeredEqual U q i j) = 0 := by
  unfold centeredEqual
  rw [average_sub, average_equalIndicator U q hq i j hi hj hne,
    average_const U q hq]
  ring

theorem average_centeredEqual_sq (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (i j : V) (hi : i ∈ U) (hj : j ∈ U) (hne : i ≠ j) :
    average U q (fun S => (centeredEqual U q i j S)^2) =
      equalMean U q * (1 - equalMean U q) := by
  have hf : (fun S => (centeredEqual U q i j S)^2) =
      (fun S => equalIndicator i j S -
        (2 * equalMean U q) * equalIndicator i j S + (equalMean U q)^2) := by
    funext S
    have hs := equalIndicator_sq i j S
    unfold centeredEqual
    nlinarith
  rw [hf, average_add, average_sub, average_mul_left,
    average_equalIndicator U q hq i j hi hj hne, average_const U q hq]
  ring

include sectionDecidableEqV in
theorem average_map_embedding {W : Type*} [DecidableEq W]
    (e : V ↪ W) (U : Finset V) (q : ℕ) (f : Finset W → ℝ) :
    average (U.map e) q f = average U q (fun S => f (S.map e)) := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  simp [average, Finset.powersetCard_map]

@[simp] theorem coord_map_embedding {W : Type*} [DecidableEq W]
    (e : V ↪ W) (i : V) (S : Finset V) :
    coord (e i) (S.map e) = coord i S := by
  simp [coord]

@[simp] theorem equalIndicator_map_embedding {W : Type*} [DecidableEq W]
    (e : V ↪ W) (i j : V) (S : Finset V) :
    equalIndicator (e i) (e j) (S.map e) = equalIndicator i j S := by
  simp [equalIndicator]

include sectionDecidableEqV in
@[simp] theorem equalMean_map_embedding {W : Type*} [DecidableEq W]
    (e : V ↪ W) (U : Finset V) (q : ℕ) :
    equalMean (U.map e) q = equalMean U q := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  simp [equalMean]

@[simp] theorem centeredEqual_map_embedding {W : Type*} [DecidableEq W]
    (e : V ↪ W) (U : Finset V) (q : ℕ) (i j : V) (S : Finset V) :
    centeredEqual (U.map e) q (e i) (e j) (S.map e) = centeredEqual U q i j S := by
  simp [centeredEqual]

theorem average_permute (e : Equiv.Perm V) (U : Finset V) (q : ℕ)
    (hU : U.map e.toEmbedding = U) (f : Finset V → ℝ) :
    average U q (fun S => f (S.map e.toEmbedding)) = average U q f := by
  rw [← average_map_embedding, hU]

theorem centeredEqual_covariance_map {W : Type*} [DecidableEq W]
    (e : V ↪ W) (U : Finset V) (q : ℕ) (i j k l : V) :
    average (U.map e) q (fun S => centeredEqual (U.map e) q (e i) (e j) S *
      centeredEqual (U.map e) q (e k) (e l) S) =
    average U q (fun S => centeredEqual U q i j S * centeredEqual U q k l S) := by
  rw [average_map_embedding]
  simp

include sectionDecidableEqV in
theorem average_sq_eq_zero_iff (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (f : Finset V → ℝ) :
    average U q (fun S => (f S)^2) = 0 ↔ ∀ S ∈ U.powersetCard q, f S = 0 := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  have hden : (U.card.choose q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hq).ne'
  constructor
  · intro h S hS
    have hsum : (∑ T ∈ U.powersetCard q, (f T)^2) = 0 := by
      exact (div_eq_zero_iff.mp h).resolve_right hden
    have hf := (Finset.sum_eq_zero_iff_of_nonneg
      (fun T _ => sq_nonneg (f T))).mp hsum S hS
    exact sq_eq_zero_iff.mp hf
  · intro h
    unfold average
    have hs : (∑ S ∈ U.powersetCard q, (f S)^2) = 0 := by
      apply Finset.sum_eq_zero
      intro S hS
      rw [h S hS]
      norm_num
    rw [hs, zero_div]

theorem centeredEqual_eq_zero_of_degenerate_mean (U : Finset V) (q : ℕ)
    (hq : q ≤ U.card) (i j : V) (hi : i ∈ U) (hj : j ∈ U) (hne : i ≠ j)
    (hp : equalMean U q = 0 ∨ equalMean U q = 1) :
    ∀ S ∈ U.powersetCard q, centeredEqual U q i j S = 0 := by
  apply (average_sq_eq_zero_iff U q hq (centeredEqual U q i j)).mp
  rw [average_centeredEqual_sq U q hq i j hi hj hne]
  rcases hp with hp | hp <;> rw [hp] <;> norm_num

theorem centeredEqual_eq_zero_of_boundary (U : Finset V) (q : ℕ)
    (hq : q ≤ U.card) (i j : V) (hi : i ∈ U) (hj : j ∈ U) (hne : i ≠ j)
    (hboundary : q = 0 ∨ q = U.card ∨ U.card ≤ 2) :
    ∀ S ∈ U.powersetCard q, centeredEqual U q i j S = 0 := by
  have hN : 2 ≤ U.card := by
    have hsub : ({i, j} : Finset V) ⊆ U := by
      simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hi, hj]
    have := Finset.card_le_card hsub
    simpa [hne] using this
  have hNR : (2 : ℝ) ≤ U.card := by exact_mod_cast hN
  have hN0 : (U.card : ℝ) ≠ 0 := by linarith
  have hN1 : (U.card : ℝ) - 1 ≠ 0 := by linarith
  apply centeredEqual_eq_zero_of_degenerate_mean U q hq i j hi hj hne
  rcases hboundary with hzero | hfull | hsmall
  · right
    subst q
    unfold equalMean
    field_simp
    ring
  · right
    subst q
    unfold equalMean
    field_simp
    ring
  · have hcard : U.card = 2 := by omega
    have hq2 : q ≤ 2 := by omega
    interval_cases q <;> norm_num [equalMean, hcard]

abbrev State (U : Finset V) (q : ℕ) := ↥(U.powersetCard q)

include sectionDecidableEqV in
theorem average_eq_fintype_sum (U : Finset V) (q : ℕ) (f : Finset V → ℝ) :
    average U q f = (∑ S : State U q, f S.val) / (Fintype.card (State U q) : ℝ) := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  simp [average, State, Finset.sum_attach, Finset.card_powersetCard]

def vector (U : Finset V) (q : ℕ) (f : Finset V → ℝ) : EuclideanSpace ℝ (State U q) :=
  WithLp.toLp 2 (fun S => f S.val)

theorem vector_norm_sq (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (f : Finset V → ℝ) :
    ‖vector U q f‖^2 = (U.card.choose q : ℝ) * average U q (fun S => (f S)^2) := by
  have hden : (U.card.choose q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hq).ne'
  rw [EuclideanSpace.real_norm_sq_eq, average_eq_fintype_sum]
  simp [vector, State, Finset.card_powersetCard]
  field_simp

theorem vector_inner (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (f g : Finset V → ℝ) :
    inner ℝ (vector U q f) (vector U q g) =
      (U.card.choose q : ℝ) * average U q (fun S => f S * g S) := by
  have hden : (U.card.choose q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hq).ne'
  rw [PiLp.inner_apply, average_eq_fintype_sum]
  simp [vector, State, Finset.card_powersetCard, mul_comm]
  field_simp

end Problem315.SliceMoments

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SliceMoments.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairEqualitySlice.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem observable_eq_equalIndicator (i j k l : Fin n) (G : GraphState n d)
    (ha : active i j k l G) :
    observable i k l G = SliceMoments.equalIndicator k l (leftSet G.val i j) := by
  have hk := (mem_singletonSet G.val i j k).mp ha.1
  have hl := (mem_singletonSet G.val i j l).mp ha.2
  have hkl : (k ∈ leftSet G.val i j) ↔ G.val.Adj i k := by
    rw [mem_leftSet]
    simp only [hk.1, true_and]
    rcases hk.2 with h | h <;> tauto
  have hll : (l ∈ leftSet G.val i j) ↔ G.val.Adj i l := by
    rw [mem_leftSet]
    simp only [hl.1, true_and]
    rcases hl.2 with h | h <;> tauto
  change (if G.val.Adj i k ↔ G.val.Adj i l then (1:ℝ) else 0) = _
  simp only [SliceMoments.equalIndicator, hkl, hll]

theorem assignment_sum (G : GraphState n d) (i j : Fin n)
    (f : Finset (Fin n) → ℝ) :
    (∑ T : Assignment G.val i j, f T.val) =
      ∑ T ∈ (singletonSet G.val i j).powersetCard (leftSet G.val i j).card, f T := by
  let e : Assignment G.val i j ≃
      ↥((singletonSet G.val i j).powersetCard (leftSet G.val i j).card) :=
    { toFun := fun T => ⟨T.val, Finset.mem_powersetCard.mpr T.property⟩
      invFun := fun T => ⟨T.val, Finset.mem_powersetCard.mp T.property⟩
      left_inv := fun T => by apply Subtype.ext; rfl
      right_inv := fun T => by apply Subtype.ext; rfl }
  calc
    _ = ∑ T : ↥((singletonSet G.val i j).powersetCard (leftSet G.val i j).card),
        f T.val := e.sum_comp (fun T => f T.val)
    _ = _ := Finset.sum_coe_sort _ f

theorem reconstructed_sameFiber (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (T : Assignment G.val i j) :
    SameFiber {i,j} G.val ((stateFiberEquiv G i j hij).symm T).val.val := by
  apply (sameFiber_iff_key_eq i j hij _ _).mpr
  exact ((stateFiberEquiv G i j hij).symm T).property.symm

theorem observable_reconstruction (G : GraphState n d) (i j k l : Fin n)
    (hij : i ≠ j) (ha : active i j k l G) (T : Assignment G.val i j) :
    observable i k l ((stateFiberEquiv G i j hij).symm T).val =
      SliceMoments.equalIndicator k l T.val := by
  have hA := (active_sameFiber i j k l hij (reconstructed_sameFiber G i j hij T)).mp ha
  rw [observable_eq_equalIndicator i j k l _ hA]
  rw [stateFiberEquiv_symm_apply, leftSet_trade]

theorem expectation_observable_eq_mean (G : GraphState n d) (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l) (ha : active i j k l G) :
    expectation n d {i,j} (observable i k l) G =
      SliceMoments.equalMean (singletonSet G.val i j) (leftSet G.val i j).card := by
  rw [expectation_eq_assignment_average G i j hij]
  simp_rw [observable_reconstruction G i j k l hij ha]
  rw [assignment_sum]
  exact SliceMoments.average_equalIndicator _ _
    (Finset.card_le_card (leftSet_subset_singletonSet G.val i j)) k l ha.1 ha.2 hkl

theorem centered_eq_slice (G : GraphState n d) (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l) (ha : active i j k l G) :
    centered i j k l G = SliceMoments.centeredEqual (singletonSet G.val i j)
      (leftSet G.val i j).card k l (leftSet G.val i j) := by
  unfold centered
  rw [fluctuation_eq_sub]
  change observable i k l G - expectation n d {i,j} (observable i k l) G = _
  rw [observable_eq_equalIndicator i j k l G ha,
    expectation_observable_eq_mean G i j k l hij hkl ha]
  rfl

theorem centered_reconstruction (G : GraphState n d) (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l) (ha : active i j k l G)
    (T : Assignment G.val i j) :
    centered i j k l ((stateFiberEquiv G i j hij).symm T).val =
      SliceMoments.centeredEqual (singletonSet G.val i j)
        (leftSet G.val i j).card k l T.val := by
  unfold centered
  rw [fluctuation_eq_sub]
  change observable i k l ((stateFiberEquiv G i j hij).symm T).val -
    expectation n d {i,j} (observable i k l) ((stateFiberEquiv G i j hij).symm T).val = _
  rw [observable_reconstruction G i j k l hij ha]
  rw [(expectation_mem {i,j} (observable i k l)) _ G
    (reconstructed_sameFiber G i j hij T).symm]
  rw [expectation_observable_eq_mean G i j k l hij hkl ha]
  rfl

theorem mem_equalitySpace_iff_assignment (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l) (f : StateSpace n d) :
    f ∈ equalitySpace i j k l ↔
      ∀ G : GraphState n d, ∃ c : ℝ, ∀ T : Assignment G.val i j,
        f ((stateFiberEquiv G i j hij).symm T).val =
          c * (if active i j k l G then
            SliceMoments.centeredEqual (singletonSet G.val i j)
              (leftSet G.val i j).card k l T.val else 0) := by
  constructor
  · intro hf G
    obtain ⟨c,hc⟩ := hf G
    refine ⟨c, fun T => ?_⟩
    have h := hc _ (reconstructed_sameFiber G i j hij T)
    by_cases ha : active i j k l G
    · simpa only [ite_eq_left ha, centered_reconstruction G i j k l hij hkl ha T] using h
    · simpa only [ite_eq_right ha] using h
  · intro hf G
    obtain ⟨c,hc⟩ := hf G
    refine ⟨c, fun H h => ?_⟩
    let H' : StateFiber G i j :=
      ⟨H, ((sameFiber_iff_key_eq i j hij G.val H.val).mp h).symm⟩
    let T : Assignment G.val i j := stateFiberEquiv G i j hij H'
    have hrecon : ((stateFiberEquiv G i j hij).symm T).val = H :=
      congrArg Subtype.val ((stateFiberEquiv G i j hij).symm_apply_apply H')
    have hT := hc T
    rw [hrecon] at hT
    by_cases ha : active i j k l G
    · have hz := centered_reconstruction G i j k l hij hkl ha T
      rw [hrecon] at hz
      simpa only [ite_eq_left ha, hz] using hT
    · simpa only [ite_eq_right ha] using hT

end Problem315.PairEquality

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairEqualitySlice.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairEqualityLocalization.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

def gatedCentered (i j k l : Fin n) : StateSpace n d :=
  WithLp.toLp 2 (fun G => if active i j k l G then centered i j k l G else 0)

theorem gatedCentered_mem (i j k l : Fin n) (hij : i ≠ j) :
    gatedCentered (d := d) i j k l ∈ equalitySpace i j k l := by
  intro G
  refine ⟨1, fun H h => ?_⟩
  have ha := active_sameFiber i j k l hij h
  change (if active i j k l H then _ else 0) = _
  simp only [one_mul, ha]

theorem restrictCell_mem (i j k l : Fin n)
    (C : GraphState n d → Prop) (hC : CellInvariant {i,j} C)
    (f : StateSpace n d) (hf : f ∈ equalitySpace i j k l) :
    restrictCell C f ∈ equalitySpace i j k l := by
  intro G
  obtain ⟨c,hc⟩ := hf G
  refine ⟨if C G then c else 0, fun H h => ?_⟩
  rw [restrictCell_apply, ← hC G H h]
  by_cases hG : C G
  · simpa only [ite_eq_left hG] using hc H h
  · simp only [ite_eq_right hG, zero_mul]

theorem fiberCell_invariant (a : Finset (Fin n)) (G : GraphState n d) :
    CellInvariant a (fun H : GraphState n d => SameFiber a G.val H.val) := by
  intro H K h
  exact ⟨fun hG => hG.trans h, fun hG => hG.trans h.symm⟩

def localizedVector (i j k l : Fin n) (G : GraphState n d) : StateSpace n d :=
  restrictCell (fun H => SameFiber {i,j} G.val H.val) (gatedCentered i j k l)

theorem localizedVector_mem (i j k l : Fin n) (hij : i ≠ j) (G : GraphState n d) :
    localizedVector i j k l G ∈ equalitySpace i j k l :=
  restrictCell_mem i j k l _ (fiberCell_invariant _ G) _
    (gatedCentered_mem i j k l hij)

theorem restrict_eq_smul_localizedVector (i j k l : Fin n) (hij : i ≠ j)
    (G : GraphState n d) (f : StateSpace n d) (hf : f ∈ equalitySpace i j k l) :
    ∃ c : ℝ, restrictCell (fun H => SameFiber {i,j} G.val H.val) f =
      c • localizedVector i j k l G := by
  obtain ⟨c,hc⟩ := hf G
  refine ⟨c, ?_⟩
  ext H
  by_cases h : SameFiber {i,j} G.val H.val
  · change (if SameFiber {i,j} G.val H.val then f H else 0) =
      c * (if SameFiber {i,j} G.val H.val then gatedCentered i j k l H else 0)
    rw [ite_eq_left h, ite_eq_left h, hc H h]
    change c * (if active i j k l G then _ else 0) =
      c * (if active i j k l H then _ else 0)
    rw [active_sameFiber i j k l hij h]
  · simp [restrictCell, localizedVector, h]

theorem projection_localization (i j k l : Fin n) (hij : i ≠ j)
    (G : GraphState n d) (f : StateSpace n d) :
    (Submodule.span ℝ {localizedVector i j k l G}).starProjection f =
      restrictCell (fun H => SameFiber {i,j} G.val H.val) (projection i j k l f) := by
  let z := localizedVector i j k l G
  let P := Submodule.span ℝ {z}
  have hz : z ∈ equalitySpace i j k l := localizedVector_mem i j k l hij G
  have hr : projection i j k l f ∈ equalitySpace i j k l :=
    (equalitySpace i j k l).starProjection_apply_mem f
  obtain ⟨c,hc⟩ := restrict_eq_smul_localizedVector i j k l hij G _ hr
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [hc]
    exact Submodule.smul_mem P c (Submodule.subset_span (Set.mem_singleton z))
  · intro w hw
    obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp hw
    rw [← ht, inner_smul_right]
    suffices hzero : ⟪f - restrictCell (fun H => SameFiber {i,j} G.val H.val)
        (projection i j k l f), z⟫ = 0 by rw [hzero, mul_zero]
    have horth := (equalitySpace i j k l).starProjection_inner_eq_zero f z hz
    change ⟪f - projection i j k l f, z⟫ = 0 at horth
    rw [← horth, state_inner, state_inner]
    apply Finset.sum_congr rfl
    intro H hH
    by_cases h : SameFiber {i,j} G.val H.val
    · simp [restrictCell, h]
    · simp [z, localizedVector, restrictCell, h]

end Problem315.PairEquality

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairEqualityLocalization.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairEqualityRestriction.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

abbrev AssignmentSpace (G : GraphState n d) (i j : Fin n) :=
  EuclideanSpace ℝ (Assignment G.val i j)

def assignmentRestriction (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) :
    StateSpace n d →ₗ[ℝ] AssignmentSpace G i j where
  toFun f := WithLp.toLp 2 (fun T => f ((stateFiberEquiv G i j hij).symm T).val)
  map_add' _ _ := by ext T; rfl
  map_smul' _ _ := by ext T; rfl

@[simp] theorem assignmentRestriction_apply (G : GraphState n d) (i j : Fin n)
    (hij : i ≠ j) (f : StateSpace n d) (T : Assignment G.val i j) :
    assignmentRestriction G i j hij f T = f ((stateFiberEquiv G i j hij).symm T).val := rfl

private theorem sum_assignment_reconstruct (G : GraphState n d) (i j : Fin n)
    (hij : i ≠ j) (f : GraphState n d → ℝ) :
    (∑ T : Assignment G.val i j, f ((stateFiberEquiv G i j hij).symm T).val) =
      ∑ H ∈ fiberStates {i,j} G, f H := by
  calc
    _ = ∑ H : ↥(fiberStates {i,j} G), f H.val :=
      (resamplingFiberEquiv G i j hij).symm.sum_comp (fun H => f H.val)
    _ = _ := Finset.sum_coe_sort _ f

theorem assignmentRestriction_inner_supported (G : GraphState n d) (i j : Fin n)
    (hij : i ≠ j) (f z : StateSpace n d)
    (hz : ∀ H : GraphState n d, ¬ SameFiber {i,j} G.val H.val → z H = 0) :
    ⟪assignmentRestriction G i j hij f, assignmentRestriction G i j hij z⟫ =
      ⟪f,z⟫ := by
  rw [state_inner]
  have hinner : ⟪assignmentRestriction G i j hij f, assignmentRestriction G i j hij z⟫ =
      ∑ T : Assignment G.val i j,
        f ((stateFiberEquiv G i j hij).symm T).val *
          z ((stateFiberEquiv G i j hij).symm T).val := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  rw [hinner, sum_assignment_reconstruct G i j hij (fun H => f H * z H)]
  unfold fiberStates
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro H hH
  by_cases h : SameFiber {i,j} G.val H.val
  · simp only [ite_eq_left h]
  · simp [h, hz H h]

def assignmentVector (G : GraphState n d) (i j k l : Fin n) : AssignmentSpace G i j :=
  WithLp.toLp 2 (fun T => if active i j k l G then
    SliceMoments.centeredEqual (singletonSet G.val i j) (leftSet G.val i j).card
      k l T.val else 0)

theorem restriction_localizedVector (G : GraphState n d) (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l) :
    assignmentRestriction G i j hij (localizedVector i j k l G) =
      assignmentVector G i j k l := by
  ext T
  rw [assignmentRestriction_apply]
  have h := reconstructed_sameFiber G i j hij T
  have ha := active_sameFiber i j k l hij h
  change (if SameFiber {i,j} G.val ((stateFiberEquiv G i j hij).symm T).val.val then
    (if active i j k l ((stateFiberEquiv G i j hij).symm T).val then
      centered i j k l ((stateFiberEquiv G i j hij).symm T).val else 0) else 0) = _
  rw [ite_eq_left h, ← ha]
  by_cases hA : active i j k l G
  · simpa only [assignmentVector, WithLp.toLp_ofLp, ite_eq_left hA] using
      centered_reconstruction G i j k l hij hkl hA T
  · simp [assignmentVector, hA]

theorem assignmentRestriction_projection (G : GraphState n d) (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l) (f : StateSpace n d) :
    assignmentRestriction G i j hij (projection i j k l f) =
      (Submodule.span ℝ {assignmentVector G i j k l}).starProjection
        (assignmentRestriction G i j hij f) := by
  let z := localizedVector i j k l G
  have hz : ∀ H : GraphState n d, ¬ SameFiber {i,j} G.val H.val → z H = 0 := by
    intro H hH
    simp [z, localizedVector, restrictCell, hH]
  have hlocal := projection_localization i j k l hij G f
  have hrestrict := congrArg (assignmentRestriction G i j hij) hlocal
  have hcell : assignmentRestriction G i j hij
      (restrictCell (fun H => SameFiber {i,j} G.val H.val) (projection i j k l f)) =
      assignmentRestriction G i j hij (projection i j k l f) := by
    ext T
    simp only [assignmentRestriction_apply, restrictCell_apply,
      ite_eq_left (reconstructed_sameFiber G i j hij T)]
  rw [hcell] at hrestrict
  rw [← hrestrict, Submodule.starProjection_singleton, map_smul,
    restriction_localizedVector G i j k l hij hkl, Submodule.starProjection_singleton]
  congr 1
  have hi := assignmentRestriction_inner_supported G i j hij f z hz
  have hn := assignmentRestriction_inner_supported G i j hij z z hz
  rw [restriction_localizedVector G i j k l hij hkl] at hi hn
  rw [real_inner_comm] at hi
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hn
  rw [hi, hn]
  congr 1
  exact real_inner_comm _ _

end Problem315.PairEquality

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairEqualityRestriction.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PermutationPathComparison.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PermutationPaths

theorem path_squared_difference_le {α : Type*} [Fintype α]
    (f : α → ℝ) (p : ℕ → α → α) (N : ℕ) :
    (∑ x, (f (p 0 x) - f (p N x)) ^ 2) ≤
      (N : ℝ) * ∑ i ∈ Finset.range N,
        ∑ x, (f (p i x) - f (p (i + 1) x)) ^ 2 := by
  have hpoint (x : α) : (f (p 0 x) - f (p N x)) ^ 2 ≤
      (N : ℝ) * ∑ i ∈ Finset.range N,
        (f (p i x) - f (p (i + 1) x)) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range N)
      (f := fun i => f (p i x) - f (p (i + 1) x))
    simpa only [Finset.sum_range_sub', Finset.card_range] using h
  calc
    (∑ x, (f (p 0 x) - f (p N x)) ^ 2)
        ≤ ∑ x, (N : ℝ) * ∑ i ∈ Finset.range N,
            (f (p i x) - f (p (i + 1) x)) ^ 2 :=
      Finset.sum_le_sum fun x _ => hpoint x
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

theorem permutation_path_energy_le {α : Type*} [Fintype α]
    (f : α → ℝ) (S : Finset (Equiv.Perm α))
    (p : ℕ → Equiv.Perm α) (N : ℕ)
    (hstep : ∀ i < N, ∃ s ∈ S, p (i + 1) = s * p i) :
    (∑ x, (f (p 0 x) - f (p N x)) ^ 2) ≤
      (N : ℝ) ^ 2 * ∑ s ∈ S, ∑ x, (f x - f (s x)) ^ 2 := by
  classical
  let B : ℝ := ∑ s ∈ S, ∑ x, (f x - f (s x)) ^ 2
  have hone (i : ℕ) (hi : i ∈ Finset.range N) :
      (∑ x, (f (p i x) - f (p (i + 1) x)) ^ 2) ≤ B := by
    obtain ⟨s, hs, hsi⟩ := hstep i (Finset.mem_range.mp hi)
    calc
      (∑ x, (f (p i x) - f (p (i + 1) x)) ^ 2)
          = ∑ x, (f x - f (s x)) ^ 2 := by
        apply Fintype.sum_equiv (p i)
        intro x
        rw [hsi, Equiv.Perm.mul_apply]
      _ ≤ B := by
        dsimp [B]
        exact Finset.single_le_sum
          (fun t _ => show 0 ≤ ∑ x, (f x - f (t x)) ^ 2 from
            Finset.sum_nonneg fun x _ => sq_nonneg _) hs
  calc
    (∑ x, (f (p 0 x) - f (p N x)) ^ 2)
        ≤ (N : ℝ) * ∑ i ∈ Finset.range N,
          ∑ x, (f (p i x) - f (p (i + 1) x)) ^ 2 :=
      path_squared_difference_le f (fun i => p i) N
    _ ≤ (N : ℝ) * ∑ _i ∈ Finset.range N, B := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hone) (Nat.cast_nonneg _)
    _ = (N : ℝ) ^ 2 * ∑ s ∈ S, ∑ x, (f x - f (s x)) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      dsimp [B]
      ring

theorem sum_group_apply_eq {α G : Type*} [Fintype α] [Nonempty α]
    [Group G] [Fintype G] (ρ : G →* Equiv.Perm α)
    (htrans : ∀ x y : α, ∃ g : G, ρ g x = y) (f : α → ℝ) (x : α) :
    (∑ g : G, f (ρ g x)) =
      (Fintype.card G : ℝ) / Fintype.card α * ∑ y, f y := by
  have hsame (y : α) : (∑ g : G, f (ρ g y)) = ∑ g : G, f (ρ g x) := by
    obtain ⟨h, rfl⟩ := htrans x y
    apply Fintype.sum_equiv (Equiv.mulRight h)
    intro g
    simp [map_mul, Equiv.Perm.mul_apply]
  have hsum (g : G) : (∑ y, f (ρ g y)) = ∑ y, f y := by
    exact Fintype.sum_equiv (ρ g) _ _ (fun _ => rfl)
  have hid : (Fintype.card α : ℝ) * (∑ g : G, f (ρ g x)) =
      (Fintype.card G : ℝ) * ∑ y, f y := by
    calc
      (Fintype.card α : ℝ) * (∑ g : G, f (ρ g x))
          = ∑ y : α, ∑ g : G, f (ρ g y) := by simp [hsame]
      _ = ∑ g : G, ∑ y : α, f (ρ g y) := Finset.sum_comm
      _ = _ := by simp [hsum]
  have hc : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hc).2
  simpa [mul_comm] using hid

theorem sum_pairwise_sq_eq {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) :
    (∑ x, ∑ y, (f x - f y) ^ 2) =
      2 * (Fintype.card α : ℝ) *
        ∑ x, (f x - (∑ y, f y) / Fintype.card α) ^ 2 := by
  let μ : ℝ := (∑ y, f y) / Fintype.card α
  have hc : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcenter : (∑ x, (f x - μ)) = 0 := by
    simp [μ, Finset.sum_sub_distrib, hc, mul_div_cancel₀]
  change _ = 2 * (Fintype.card α : ℝ) * ∑ x, (f x - μ) ^ 2
  calc
    (∑ x, ∑ y, (f x - f y) ^ 2) =
        ∑ x, ∑ y, ((f x - μ) ^ 2 + (f y - μ) ^ 2 -
          2 * (f x - μ) * (f y - μ)) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = _ := by
      simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hcenter]
      simp only [mul_zero, Finset.sum_const_zero, sub_zero, Finset.card_univ]
      rw [← Finset.mul_sum]
      ring

theorem sum_group_squared_difference_eq {α G : Type*} [Fintype α] [Nonempty α]
    [Group G] [Fintype G] (ρ : G →* Equiv.Perm α)
    (htrans : ∀ x y : α, ∃ g : G, ρ g x = y) (f : α → ℝ) :
    (∑ g : G, ∑ x, (f x - f (ρ g x)) ^ 2) =
      2 * (Fintype.card G : ℝ) *
        ∑ x, (f x - (∑ y, f y) / Fintype.card α) ^ 2 := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    (∑ g : G, ∑ x, (f x - f (ρ g x)) ^ 2)
        = ∑ x, ∑ g : G, (f x - f (ρ g x)) ^ 2 := Finset.sum_comm
    _ = ∑ x, (Fintype.card G : ℝ) / Fintype.card α *
        ∑ y, (f x - f y) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      exact sum_group_apply_eq ρ htrans (fun y => (f x - f y) ^ 2) x
    _ = (Fintype.card G : ℝ) / Fintype.card α *
        (∑ x, ∑ y, (f x - f y) ^ 2) := (Finset.mul_sum _ _ _).symm
    _ = _ := by
      rw [sum_pairwise_sq_eq f]
      field_simp

theorem variance_le_generator_energy {α G : Type*} [Fintype α] [Nonempty α]
    [Group G] [Fintype G] (ρ : G →* Equiv.Perm α)
    (htrans : ∀ x y : α, ∃ g : G, ρ g x = y)
    (S : Finset (Equiv.Perm α)) (N : ℕ)
    (hpaths : ∀ g : G, ∃ (p : ℕ → Equiv.Perm α) (L : ℕ),
      L ≤ N ∧ p 0 = 1 ∧ p L = ρ g ∧
        ∀ i < L, ∃ s ∈ S, p (i + 1) = s * p i)
    (f : α → ℝ) :
    (∑ x, (f x - (∑ y, f y) / Fintype.card α) ^ 2) ≤
      (N : ℝ) ^ 2 / 2 * ∑ s ∈ S, ∑ x, (f x - f (s x)) ^ 2 := by
  classical
  let B : ℝ := ∑ s ∈ S, ∑ x, (f x - f (s x)) ^ 2
  have hB : 0 ≤ B := Finset.sum_nonneg fun s _ =>
    Finset.sum_nonneg fun x _ => sq_nonneg _
  have hbound (g : G) : (∑ x, (f x - f (ρ g x)) ^ 2) ≤ (N : ℝ) ^ 2 * B := by
    obtain ⟨p, L, hLN, hzero, hend, hstep⟩ := hpaths g
    have hpath := permutation_path_energy_le f S p L hstep
    simp only [hzero, hend, Equiv.Perm.one_apply] at hpath
    calc
      (∑ x, (f x - f (ρ g x)) ^ 2) ≤ (L : ℝ) ^ 2 * B := hpath
      _ ≤ (N : ℝ) ^ 2 * B := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg L) (by exact_mod_cast hLN) 2) hB
  have hsum : 2 * (Fintype.card G : ℝ) *
      (∑ x, (f x - (∑ y, f y) / Fintype.card α) ^ 2) ≤
      (Fintype.card G : ℝ) * ((N : ℝ) ^ 2 * B) := by
    rw [← sum_group_squared_difference_eq ρ htrans f]
    calc
      _ ≤ ∑ _g : G, (N : ℝ) ^ 2 * B := Finset.sum_le_sum fun g _ => hbound g
      _ = _ := by simp
  have hG : 0 < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcancel : 2 * (∑ x, (f x - (∑ y, f y) / Fintype.card α) ^ 2) ≤
      (N : ℝ) ^ 2 * B := by
    apply (mul_le_mul_iff_right₀ hG).mp
    nlinarith [hsum]
  change _ ≤ (N : ℝ) ^ 2 / 2 * B
  linarith

theorem exists_path_of_word {α : Type*} (S : Finset (Equiv.Perm α))
    (l : List (Equiv.Perm α)) (hl : ∀ s ∈ l, s ∈ S) :
    ∃ p : ℕ → Equiv.Perm α, p 0 = 1 ∧ p l.length = l.prod ∧
      ∀ i < l.length, ∃ s ∈ S, p (i + 1) = s * p i := by
  classical
  induction l with
  | nil =>
      exact ⟨fun _ => 1, rfl, rfl, by simp⟩
  | cons s l ih =>
      obtain ⟨p, hp0, hpend, hpstep⟩ := ih (fun t ht => hl t (List.mem_cons_of_mem s ht))
      let q : ℕ → Equiv.Perm α := fun i => if i ≤ l.length then p i else s * p l.length
      refine ⟨q, ?_, ?_, ?_⟩
      · simp [q, hp0]
      · simp [q, hpend]
      · intro i hi
        simp only [List.length_cons] at hi
        by_cases hil : i < l.length
        · obtain ⟨t, ht, hti⟩ := hpstep i hil
          refine ⟨t, ht, ?_⟩
          simpa [q, Nat.le_of_lt hil, Nat.succ_le_of_lt hil] using hti
        · have hieq : i = l.length := by omega
          subst i
          refine ⟨s, hl s (List.mem_cons_self ..), ?_⟩
          simp [q]

theorem variance_le_generator_energy_of_words {α G : Type*}
    [Fintype α] [Nonempty α] [Group G] [Fintype G]
    (ρ : G →* Equiv.Perm α)
    (htrans : ∀ x y : α, ∃ g : G, ρ g x = y)
    (S : Finset (Equiv.Perm α)) (N : ℕ)
    (hwords : ∀ g : G, ∃ l : List (Equiv.Perm α),
      l.length ≤ N ∧ l.prod = ρ g ∧ ∀ s ∈ l, s ∈ S)
    (f : α → ℝ) :
    (∑ x, (f x - (∑ y, f y) / Fintype.card α) ^ 2) ≤
      (N : ℝ) ^ 2 / 2 * ∑ s ∈ S, ∑ x, (f x - f (s x)) ^ 2 := by
  apply variance_le_generator_energy ρ htrans S N ?_ f
  intro g
  obtain ⟨l, hlength, hprod, hletters⟩ := hwords g
  obtain ⟨p, hp0, hpend, hpstep⟩ := exists_path_of_word S l hletters
  exact ⟨p, l.length, hlength, hp0, hpend.trans hprod, hpstep⟩

end Problem315.PermutationPaths

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PermutationPathComparison.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PermutationFactors.lean -/
section

namespace OAI

noncomputable section
open Equiv

namespace Problem315.PermutationFactors

variable {α : Type*} [DecidableEq α]

theorem swapFactorsAux_length_le (l : List α) (σ : Perm α)
    (h : ∀ {x}, σ x ≠ x → x ∈ l) :
    (Perm.swapFactorsAux l σ h).val.length ≤ l.length := by
  induction l generalizing σ with
  | nil => simp [Perm.swapFactorsAux]
  | cons x l ih =>
    rw [Perm.swapFactorsAux]
    dsimp only
    split_ifs with hfix
    · have htail : ∀ {y}, σ y ≠ y → y ∈ l := by
        intro y hy
        exact List.mem_of_ne_of_mem (fun hyx => by simp [hyx, hfix.symm] at hy) (h hy)
      exact (ih σ htail).trans (Nat.le_succ _)
    · have htail : ∀ {y}, (swap x (σ x) * σ) y ≠ y → y ∈ l := by
        intro y hy
        have hh := Perm.ne_and_ne_of_swap_mul_apply_ne_self hy
        exact List.mem_of_ne_of_mem hh.2 (h hh.1)
      simpa only [List.length_cons] using
        Nat.succ_le_succ (ih (swap x (σ x) * σ) htail)

theorem exists_swap_factors_length_le [Fintype α] (σ : Perm α) :
    ∃ l : List (Perm α), l.prod = σ ∧
      (∀ τ ∈ l, Perm.IsSwap τ) ∧ l.length ≤ Fintype.card α := by
  classical
  let support : List α := Finset.univ.toList
  have hsupport : ∀ {x}, σ x ≠ x → x ∈ support := by
    intro x _
    simp [support]
  let factors := Perm.swapFactorsAux support σ hsupport
  refine ⟨factors.val, factors.property.1, factors.property.2, ?_⟩
  have h := swapFactorsAux_length_le support σ hsupport
  simpa only [factors, support, Finset.length_toList, Finset.card_univ] using h

theorem exists_swap_pairs_of_isSwap_list (l : List (Perm α))
    (hl : ∀ τ ∈ l, Perm.IsSwap τ) :
    ∃ v : List (α × α), v.map (fun ab => swap ab.1 ab.2) = l ∧
      v.length = l.length ∧ ∀ ab ∈ v, ab.1 ≠ ab.2 := by
  induction l with
  | nil => exact ⟨[], rfl, rfl, by simp⟩
  | cons τ l ih =>
    obtain ⟨a, b, hab, hτ⟩ := hl τ (by simp)
    obtain ⟨v, hv, hlen, hdistinct⟩ := ih (fun υ hυ => hl υ (List.mem_cons_of_mem τ hυ))
    refine ⟨(a, b) :: v, ?_, by simp [hlen], ?_⟩
    · simp [hv, hτ]
    · intro ab habv
      rcases List.mem_cons.mp habv with h | h
      · simpa [h] using hab
      · exact hdistinct ab h

theorem exists_swap_pair_factors_length_le [Fintype α] (σ : Perm α) :
    ∃ l : List (α × α), (l.map (fun ab => swap ab.1 ab.2)).prod = σ ∧
      l.length ≤ Fintype.card α ∧ ∀ ab ∈ l, ab.1 ≠ ab.2 := by
  obtain ⟨factors, hprod, hswap, hlen⟩ := exists_swap_factors_length_le σ
  obtain ⟨l, hl, hlen', hdistinct⟩ := exists_swap_pairs_of_isSwap_list factors hswap
  exact ⟨l, by rw [hl, hprod], hlen' ▸ hlen, hdistinct⟩

end Problem315.PermutationFactors

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PermutationFactors.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/TransitiveAverage.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.TransitiveAverage

variable {Γ X : Type*} [Group Γ] [Fintype Γ] [sectionFintypeX : Fintype X]
  [MulAction Γ X] [MulAction.IsPretransitive Γ X]

include sectionFintypeX in
theorem sum_smul_eq (f : X → ℝ) (x y : X) :
    (∑ g : Γ, f (g • x)) = ∑ g : Γ, f (g • y) := by
  have retainedsectionFintypeX := sectionFintypeX
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq Γ x y
  symm
  simp_rw [smul_smul]
  exact Equiv.sum_comp (Equiv.mulRight a) (fun g : Γ => f (g • x))

theorem card_mul_sum_smul (f : X → ℝ) (x : X) :
    (Fintype.card X : ℝ) * (∑ g : Γ, f (g • x)) =
      (Fintype.card Γ : ℝ) * (∑ y : X, f y) := by
  calc
    (Fintype.card X : ℝ) * (∑ g : Γ, f (g • x)) =
        ∑ _y : X, ∑ g : Γ, f (g • x) := by simp
    _ = ∑ y : X, ∑ g : Γ, f (g • y) := by
      apply Finset.sum_congr rfl
      intro y _
      exact sum_smul_eq f x y
    _ = ∑ g : Γ, ∑ y : X, f (g • y) := Finset.sum_comm
    _ = ∑ _g : Γ, ∑ y : X, f y := by
      apply Finset.sum_congr rfl
      intro g _
      exact Equiv.sum_comp (MulAction.toPerm g) f
    _ = (Fintype.card Γ : ℝ) * (∑ y : X, f y) := by simp

theorem average_smul_eq (f : X → ℝ) (x : X) :
    (∑ g : Γ, f (g • x)) / (Fintype.card Γ : ℝ) =
      (∑ y : X, f y) / (Fintype.card X : ℝ) := by
  have : Nonempty X := ⟨x⟩
  have hΓ : (Fintype.card Γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hX : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply (div_eq_div_iff hΓ hX).mpr
  simpa only [mul_comm] using card_mul_sum_smul (Γ := Γ) f x

theorem average_sum_sq_difference (f : X → ℝ) :
    (∑ g : Γ, ∑ x : X, (f x - f (g • x)) ^ 2) / (Fintype.card Γ : ℝ) =
      (∑ x : X, ∑ y : X, (f x - f y) ^ 2) / (Fintype.card X : ℝ) := by
  rw [Finset.sum_comm]
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  simpa only [Finset.sum_div] using
    average_smul_eq (Γ := Γ) (fun y => (f x - f y) ^ 2) x

end Problem315.TransitiveAverage

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/TransitiveAverage.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SlicePermutationAction.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SlicePermutationAction

variable {α : Type*} [sectionFintypeα : Fintype α] [sectionDecidableEqα : DecidableEq α]

theorem exists_perm_map_eq (s t : Finset α) (hcard : s.card = t.card) :
    ∃ σ : Equiv.Perm α, s.map σ.toEmbedding = t := by
  classical
  let e : s ≃ t := Fintype.equivOfCardEq (by simpa using hcard)
  let σ : Equiv.Perm α := e.extendSubtype
  refine ⟨σ, Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    exact e.extendSubtype_mem x hx
  · simpa using hcard.ge

abbrev Slice (α : Type*) (q : ℕ) := {s : Finset α // s.card = q}

def boundedSliceEquiv (U : Finset α) (q : ℕ) :
    {s : Finset α // s ⊆ U ∧ s.card = q} ≃ Slice U q where
  toFun s := ⟨s.val.subtype (fun x => x ∈ U), by
    rw [Finset.card_subtype, Finset.filter_eq_self.mpr s.property.1]
    exact s.property.2⟩
  invFun s := ⟨s.val.map (Function.Embedding.subtype (fun x => x ∈ U)),
    ⟨fun _ hx => Finset.property_of_mem_map_subtype _ hx, by simpa using s.property⟩⟩
  left_inv s := Subtype.ext (Finset.subtype_map_of_mem s.property.1)
  right_inv s := by
    apply Subtype.ext
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp (Finset.mem_subtype.mp hx)
      have heq : y = x := Subtype.ext hxy
      simpa [← heq] using hy
    · intro hx
      exact Finset.mem_subtype.mpr (Finset.mem_map.mpr ⟨x, hx, rfl⟩)

def relabel {q : ℕ} (σ : Equiv.Perm α) (s : Slice α q) : Slice α q :=
  ⟨s.val.map σ.toEmbedding, by simpa using s.property⟩

include sectionFintypeα sectionDecidableEqα in
@[simp] theorem relabel_one {q : ℕ} (s : Slice α q) : relabel 1 s = s := by
  have retainedsectionFintypeα := sectionFintypeα
  have retainedsectionDecidableEqα := sectionDecidableEqα
  apply Subtype.ext
  change s.val.map (Function.Embedding.refl α) = s.val
  exact Finset.map_refl

include sectionFintypeα sectionDecidableEqα in
@[simp] theorem relabel_mul {q : ℕ} (σ τ : Equiv.Perm α) (s : Slice α q) :
    relabel (σ * τ) s = relabel σ (relabel τ s) := by
  have retainedsectionFintypeα := sectionFintypeα
  have retainedsectionDecidableEqα := sectionDecidableEqα
  apply Subtype.ext
  simp only [relabel, Finset.map_map]
  rfl

def relabelEquiv {q : ℕ} (σ : Equiv.Perm α) : Equiv.Perm (Slice α q) where
  toFun := relabel σ
  invFun := relabel σ⁻¹
  left_inv s := by rw [← relabel_mul, inv_mul_cancel, relabel_one]
  right_inv s := by rw [← relabel_mul, mul_inv_cancel, relabel_one]

@[simp] theorem relabelEquiv_apply {q : ℕ} (σ : Equiv.Perm α) (s : Slice α q) :
    relabelEquiv σ s = relabel σ s := rfl

def relabelHom (q : ℕ) : Equiv.Perm α →* Equiv.Perm (Slice α q) where
  toFun := relabelEquiv
  map_one' := by apply Equiv.ext; intro s; exact relabel_one s
  map_mul' σ τ := by apply Equiv.ext; intro s; exact relabel_mul σ τ s

theorem sum_relabel {q : ℕ} (σ : Equiv.Perm α) (f : Slice α q → ℝ) :
    (∑ s : Slice α q, f (relabel σ s)) = ∑ s : Slice α q, f s :=
  Equiv.sum_comp (relabelEquiv σ) f

theorem relabelEquiv_list_prod {q : ℕ} (l : List (Equiv.Perm α)) :
    relabelEquiv (q := q) l.prod = (l.map relabelEquiv).prod :=
  map_list_prod (relabelHom q) l

@[reducible] def mulAction (q : ℕ) : MulAction (Equiv.Perm α) (Slice α q) where
  smul := relabel
  one_smul := relabel_one
  mul_smul := relabel_mul

theorem exists_relabel_eq {q : ℕ} (s t : Slice α q) :
    ∃ σ : Equiv.Perm α, relabel σ s = t := by
  obtain ⟨σ, hσ⟩ := exists_perm_map_eq s.val t.val (s.property.trans t.property.symm)
  exact ⟨σ, Subtype.ext hσ⟩

theorem average_relabel_eq {q : ℕ} (f : Slice α q → ℝ) (s : Slice α q) :
    (∑ σ : Equiv.Perm α, f (relabel σ s)) / (Fintype.card (Equiv.Perm α) : ℝ) =
      (∑ t : Slice α q, f t) / (Fintype.card (Slice α q) : ℝ) := by
  let := mulAction (α := α) q
  let : MulAction.IsPretransitive (Equiv.Perm α) (Slice α q) :=
    ⟨exists_relabel_eq⟩
  exact TransitiveAverage.average_smul_eq f s

theorem average_relabel_sq_difference {q : ℕ} (f : Slice α q → ℝ) :
    (∑ σ : Equiv.Perm α, ∑ s : Slice α q, (f s - f (relabel σ s)) ^ 2) /
        (Fintype.card (Equiv.Perm α) : ℝ) =
      (∑ s : Slice α q, ∑ t : Slice α q, (f s - f t) ^ 2) /
        (Fintype.card (Slice α q) : ℝ) := by
  let := mulAction (α := α) q
  let : MulAction.IsPretransitive (Equiv.Perm α) (Slice α q) :=
    ⟨exists_relabel_eq⟩
  exact TransitiveAverage.average_sum_sq_difference f

end Problem315.SlicePermutationAction

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SlicePermutationAction.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SlicePathComparison.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators
open Problem315.SlicePermutationAction

namespace Problem315.SlicePathComparison

variable {α : Type*} [Fintype α] [DecidableEq α]

def swaps : Finset (Equiv.Perm α) := by
  classical
  exact Finset.univ.filter Equiv.Perm.IsSwap

@[simp] theorem mem_swaps (σ : Equiv.Perm α) : σ ∈ swaps ↔ Equiv.Perm.IsSwap σ := by
  classical
  simp [swaps]

theorem variance_le_swap_squared_differences {q : ℕ} [Nonempty (Slice α q)]
    (f : Slice α q → ℝ) :
    (∑ s, (f s - (∑ t, f t) / (Fintype.card (Slice α q) : ℝ)) ^ 2) ≤
      (Fintype.card α : ℝ) ^ 2 / 2 *
        ∑ σ ∈ swaps, ∑ s, (f s - f (relabel σ s)) ^ 2 := by
  classical
  let S : Finset (Equiv.Perm (Slice α q)) := swaps.image relabelEquiv
  have hwords (σ : Equiv.Perm α) :
      ∃ l : List (Equiv.Perm (Slice α q)), l.length ≤ Fintype.card α ∧
        l.prod = relabelHom q σ ∧ ∀ τ ∈ l, τ ∈ S := by
    obtain ⟨l, hprod, hswap, hlen⟩ := PermutationFactors.exists_swap_factors_length_le σ
    refine ⟨l.map relabelEquiv, by simpa using hlen, ?_, ?_⟩
    · rw [← relabelEquiv_list_prod, hprod]
      rfl
    · intro τ hτ
      obtain ⟨υ, hυ, rfl⟩ := List.mem_map.mp hτ
      exact Finset.mem_image.mpr ⟨υ, (mem_swaps υ).mpr (hswap υ hυ), rfl⟩
  have h := PermutationPaths.variance_le_generator_energy_of_words
    (relabelHom q) (fun s t => exists_relabel_eq s t) S (Fintype.card α) hwords f
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact Finset.sum_image_le_of_nonneg (fun τ _ =>
    Finset.sum_nonneg fun s _ => sq_nonneg (f s - f (τ s)))

theorem relabel_displacement_eq_twice_energy {q : ℕ}
    (σ : Equiv.Perm α) (f : Slice α q → ℝ) :
    (∑ s, (f s - f (relabel σ s)) ^ 2) =
      2 * (∑ s, f s * (f s - f (relabel σ s))) := by
  have hnorm := sum_relabel σ (fun s => (f s) ^ 2)
  simp only [sub_sq, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum, ← sq]
  rw [hnorm]
  ring

theorem variance_le_card_sq_swap_energy {q : ℕ} [Nonempty (Slice α q)]
    (f : Slice α q → ℝ) :
    (∑ s, (f s - (∑ t, f t) / (Fintype.card (Slice α q) : ℝ)) ^ 2) ≤
      (Fintype.card α : ℝ) ^ 2 *
        ∑ s, f s * (∑ σ ∈ swaps, (f s - f (relabel σ s))) := by
  have h := variance_le_swap_squared_differences f
  simp_rw [relabel_displacement_eq_twice_energy] at h
  rw [← Finset.mul_sum] at h
  have hcomm : (∑ σ ∈ swaps, ∑ s, f s * (f s - f (relabel σ s))) =
      ∑ s, f s * (∑ σ ∈ swaps, (f s - f (relabel σ s))) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    exact (Finset.mul_sum _ _ _).symm
  rw [hcomm] at h
  nlinarith [h]

theorem uniform_variance_le_card_sq_swap_energy {q : ℕ} [Nonempty (Slice α q)]
    (f : Slice α q → ℝ) :
    (∑ s, (f s - (∑ t, f t) / (Fintype.card (Slice α q) : ℝ)) ^ 2) /
        (Fintype.card (Slice α q) : ℝ) ≤
      (Fintype.card α : ℝ) ^ 2 *
        ((∑ s, f s * (∑ σ ∈ swaps, (f s - f (relabel σ s)))) /
          (Fintype.card (Slice α q) : ℝ)) := by
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right
    (variance_le_card_sq_swap_energy f) (Nat.cast_nonneg (Fintype.card (Slice α q)))

theorem variance_le_card_sq_transport {q : ℕ} {X : Type*} [Fintype X] [Nonempty X]
    (e : X ≃ Slice α q) (f : X → ℝ) :
    (∑ x, (f x - (∑ y, f y) / (Fintype.card X : ℝ)) ^ 2) ≤
      (Fintype.card α : ℝ) ^ 2 *
        ∑ x, f x * (∑ σ ∈ swaps, (f x - f (e.symm (relabel σ (e x))))) := by
  classical
  let : Nonempty (Slice α q) := ⟨e (Classical.arbitrary X)⟩
  have hmean : (∑ s : Slice α q, f (e.symm s)) = ∑ x : X, f x :=
    Equiv.sum_comp e.symm f
  have hcard : Fintype.card (Slice α q) = Fintype.card X := Fintype.card_congr e.symm
  have h := variance_le_card_sq_swap_energy (fun s => f (e.symm s))
  rw [hmean, hcard] at h
  have hleft : (∑ s : Slice α q,
      (f (e.symm s) - (∑ y, f y) / (Fintype.card X : ℝ)) ^ 2) =
      ∑ x : X, (f x - (∑ y, f y) / (Fintype.card X : ℝ)) ^ 2 :=
    Equiv.sum_comp e.symm (fun x => (f x - (∑ y, f y) / (Fintype.card X : ℝ)) ^ 2)
  have hright : (∑ s : Slice α q, f (e.symm s) *
      (∑ σ ∈ swaps, (f (e.symm s) - f (e.symm (relabel σ s))))) =
      ∑ x : X, f x * (∑ σ ∈ swaps, (f x - f (e.symm (relabel σ (e x))))) := by
    apply Fintype.sum_equiv e.symm
    intro s
    simp
  rwa [hleft, hright] at h

end Problem315.SlicePathComparison

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SlicePathComparison.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairFiberSliceComparison.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairFiber

open SlicePermutationAction
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

def assignmentSliceEquiv (G : SimpleGraph V) (i j : V) :
    Assignment G i j ≃ Slice (singletonSet G i j) (leftSet G i j).card :=
  boundedSliceEquiv (singletonSet G i j) (leftSet G i j).card

def assignmentRelabel (G : SimpleGraph V) (i j : V)
    (σ : Equiv.Perm (singletonSet G i j)) (T : Assignment G i j) :
    Assignment G i j :=
  (assignmentSliceEquiv G i j).symm
    (relabel σ (assignmentSliceEquiv G i j T))

def assignmentRelabelEquiv (G : SimpleGraph V) (i j : V)
    (σ : Equiv.Perm (singletonSet G i j)) : Equiv.Perm (Assignment G i j) :=
  ((assignmentSliceEquiv G i j).trans (relabelEquiv σ)).trans
    (assignmentSliceEquiv G i j).symm

theorem assignmentRelabel_swap_val (G : SimpleGraph V) (i j : V)
    (x y : singletonSet G i j) (T : Assignment G i j) :
    (assignmentRelabel G i j (Equiv.swap x y) T).val =
      T.val.map (Equiv.swap x.val y.val).toEmbedding := by
  classical
  change ((T.val.subtype (fun z => z ∈ singletonSet G i j)).map
    (Equiv.swap x y).toEmbedding).map
      (Function.Embedding.subtype (fun z => z ∈ singletonSet G i j)) = _
  rw [Finset.map_map]
  have he : (Equiv.swap x y).toEmbedding.trans
      (Function.Embedding.subtype (fun z => z ∈ singletonSet G i j)) =
      (Function.Embedding.subtype (fun z => z ∈ singletonSet G i j)).trans
        (Equiv.swap x.val y.val).toEmbedding := by
    ext z
    exact Function.Injective.map_swap Subtype.val_injective x y z
  rw [he, ← Finset.map_map, Finset.subtype_map_of_mem T.property.1]

theorem assignment_variance_le_swap_energy (G : SimpleGraph V) (i j : V)
    (f : Assignment G i j → ℝ) :
    (∑ T, (f T - (∑ U, f U) / (Fintype.card (Assignment G i j) : ℝ)) ^ 2) ≤
      ((singletonSet G i j).card : ℝ) ^ 2 *
        ∑ T, f T * (∑ σ ∈ SlicePathComparison.swaps,
          (f T - f (assignmentRelabel G i j σ T))) := by
  classical
  let : Nonempty (Assignment G i j) :=
    ⟨⟨leftSet G i j, leftSet_subset_singletonSet G i j, rfl⟩⟩
  simpa only [Fintype.card_coe, assignmentRelabel] using
    SlicePathComparison.variance_le_card_sq_transport (assignmentSliceEquiv G i j) f

theorem assignment_displacement_eq_twice_energy (G : SimpleGraph V) (i j : V)
    (σ : Equiv.Perm (singletonSet G i j)) (f : Assignment G i j → ℝ) :
    (∑ T, (f T - f (assignmentRelabel G i j σ T)) ^ 2) =
      2 * (∑ T, f T * (f T - f (assignmentRelabel G i j σ T))) := by
  have hnorm : (∑ T, (f (assignmentRelabel G i j σ T)) ^ 2) = ∑ T, (f T)^2 :=
    Equiv.sum_comp (assignmentRelabelEquiv G i j σ) (fun T => (f T)^2)
  simp only [sub_sq, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum, ← sq]
  rw [hnorm]
  ring

theorem assignment_variance_le_swap_squared_differences (G : SimpleGraph V) (i j : V)
    (f : Assignment G i j → ℝ) :
    (∑ T, (f T - (∑ U, f U) / (Fintype.card (Assignment G i j) : ℝ)) ^ 2) ≤
      ((singletonSet G i j).card : ℝ) ^ 2 / 2 *
        ∑ T, ∑ σ ∈ SlicePathComparison.swaps,
          (f T - f (assignmentRelabel G i j σ T)) ^ 2 := by
  have h := assignment_variance_le_swap_energy G i j f
  have hs : (∑ T, ∑ σ ∈ SlicePathComparison.swaps,
      (f T - f (assignmentRelabel G i j σ T)) ^ 2) =
      2 * ∑ T, f T * (∑ σ ∈ SlicePathComparison.swaps,
        (f T - f (assignmentRelabel G i j σ T))) := by
    rw [Finset.sum_comm]
    simp_rw [assignment_displacement_eq_twice_energy]
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro T _
    exact (Finset.mul_sum _ _ _).symm
  rw [hs]
  nlinarith [h]

def resamplingFiberSliceEquiv {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) :
    (PairResampling.fiberStates {i, j} G) ≃
      Slice (singletonSet G.val i j) (leftSet G.val i j).card :=
  (resamplingFiberEquiv G i j hij).trans (assignmentSliceEquiv G.val i j)

theorem state_assignment_variance_le_swap_energy {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (f : GraphState n d → ℝ) :
    (∑ T : Assignment G.val i j,
      (f ((stateFiberEquiv G i j hij).symm T).val -
        (∑ U : Assignment G.val i j, f ((stateFiberEquiv G i j hij).symm U).val) /
          (Fintype.card (Assignment G.val i j) : ℝ)) ^ 2) ≤
      ((singletonSet G.val i j).card : ℝ) ^ 2 *
        ∑ T : Assignment G.val i j, f ((stateFiberEquiv G i j hij).symm T).val *
          (∑ σ ∈ SlicePathComparison.swaps,
            (f ((stateFiberEquiv G i j hij).symm T).val -
              f ((stateFiberEquiv G i j hij).symm (assignmentRelabel G.val i j σ T)).val)) :=
  assignment_variance_le_swap_energy G.val i j
    (fun T => f ((stateFiberEquiv G i j hij).symm T).val)

end Problem315.PairFiber

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairFiberSliceComparison.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairFiberTransport.lean -/
section

namespace OAI

noncomputable section
namespace Problem315.PairFiber

variable {V : Type*} [Fintype V]

theorem trade_eq_of_key_eq {G H : SimpleGraph V} {i j : V}
    (hij : i ≠ j) (hk : key i j G = key i j H) (T : Finset V)
    (hG : T ⊆ singletonSet G i j) (hH : T ⊆ singletonSet H i j) :
    trade G i j hij T hG = trade H i j hij T hH := by
  apply graph_eq_of_key_leftSet_eq
  · exact (key_trade G i j hij T hG).trans
      (hk.trans (key_trade H i j hij T hH).symm)
  · rw [leftSet_trade, leftSet_trade]

def assignmentEquivOfKeyEq {n : Nat} {d : Fin n → Nat}
    {G H : GraphState n d} {i j : Fin n} (hij : i ≠ j)
    (hk : key i j G.val = key i j H.val) :
    Assignment G.val i j ≃ Assignment H.val i j := by
  have hs := singletonSet_eq_of_key_eq hk
  have hc := (leftSet_card_eq_iff_degree_eq hij hk).mpr
    ((G.property i).trans (H.property i).symm)
  exact
    { toFun := fun T => ⟨T.val, by simpa only [← hs, ← hc] using T.property⟩
      invFun := fun T => ⟨T.val, by simpa only [hs, hc] using T.property⟩
      left_inv := fun T => by apply Subtype.ext; rfl
      right_inv := fun T => by apply Subtype.ext; rfl }

@[simp] theorem assignmentEquivOfKeyEq_val {n : Nat} {d : Fin n → Nat}
    {G H : GraphState n d} {i j : Fin n} (hij : i ≠ j)
    (hk : key i j G.val = key i j H.val) (T : Assignment G.val i j) :
    (assignmentEquivOfKeyEq hij hk T).val = T.val := rfl

theorem stateFiberEquiv_symm_eq_of_key_eq {n : Nat} {d : Fin n → Nat}
    {G H : GraphState n d} {i j : Fin n} (hij : i ≠ j)
    (hk : key i j G.val = key i j H.val) (T : Assignment G.val i j) :
    ((stateFiberEquiv G i j hij).symm T).val =
      ((stateFiberEquiv H i j hij).symm (assignmentEquivOfKeyEq hij hk T)).val := by
  apply Subtype.ext
  exact trade_eq_of_key_eq hij hk T.val T.property.1
    (assignmentEquivOfKeyEq hij hk T).property.1

theorem stateFiberEquiv_symm_leftSet {n : Nat} {d : Fin n → Nat}
    {G H : GraphState n d} {i j : Fin n} (hij : i ≠ j)
    (hk : key i j H.val = key i j G.val) :
    ((stateFiberEquiv G i j hij).symm
      (stateFiberEquiv G i j hij ⟨H, hk⟩)).val = H := by
  exact congrArg Subtype.val ((stateFiberEquiv G i j hij).symm_apply_apply ⟨H, hk⟩)

theorem singletonSet_card_le (G : SimpleGraph V) (i j : V) :
    (singletonSet G i j).card ≤ Fintype.card V := Finset.card_le_univ _

theorem trade_leftSet_of_key_eq {G H : SimpleGraph V} {i j : V} (hij : i ≠ j)
    (hk : key i j G = key i j H)
    (hT : leftSet H i j ⊆ singletonSet G i j) :
    trade G i j hij (leftSet H i j) hT = H := by
  rw [trade_eq_of_key_eq hij hk _ hT (leftSet_subset_singletonSet H i j)]
  exact trade_original H i j hij

def assignmentEquivOfKeyCardEq {G H : SimpleGraph V} {i j : V}
    (hk : key i j G = key i j H)
    (hc : (leftSet G i j).card = (leftSet H i j).card) :
    Assignment G i j ≃ Assignment H i j where
  toFun T := ⟨T.val, by
    constructor
    · rw [← singletonSet_eq_of_key_eq hk]
      exact T.property.1
    · exact T.property.2.trans hc⟩
  invFun T := ⟨T.val, by
    constructor
    · rw [singletonSet_eq_of_key_eq hk]
      exact T.property.1
    · exact T.property.2.trans hc.symm⟩
  left_inv T := by apply Subtype.ext; rfl
  right_inv T := by apply Subtype.ext; rfl

@[simp] theorem assignmentEquivOfKeyCardEq_val {G H : SimpleGraph V} {i j : V}
    (hk : key i j G = key i j H)
    (hc : (leftSet G i j).card = (leftSet H i j).card)
    (T : Assignment G i j) : (assignmentEquivOfKeyCardEq hk hc T).val = T.val := rfl

def stateAssignmentEquiv {n : Nat} {d : Fin n → Nat}
    (G H : GraphState n d) {i j : Fin n} (hij : i ≠ j)
    (hk : key i j G.val = key i j H.val) :
    Assignment G.val i j ≃ Assignment H.val i j :=
  assignmentEquivOfKeyEq hij hk

@[simp] theorem stateAssignmentEquiv_val {n : Nat} {d : Fin n → Nat}
    (G H : GraphState n d) {i j : Fin n} (hij : i ≠ j)
    (hk : key i j G.val = key i j H.val) (T : Assignment G.val i j) :
    (stateAssignmentEquiv G H hij hk T).val = T.val := rfl

theorem stateFiberEquiv_symm_val_eq {n : Nat} {d : Fin n → Nat}
    (G H : GraphState n d) {i j : Fin n} (hij : i ≠ j)
    (hk : key i j G.val = key i j H.val) (T : Assignment G.val i j) :
    ((stateFiberEquiv G i j hij).symm T).val =
      ((stateFiberEquiv H i j hij).symm (stateAssignmentEquiv G H hij hk T)).val :=
  stateFiberEquiv_symm_eq_of_key_eq hij hk T

end Problem315.PairFiber

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairFiberTransport.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairCrossToggleTransport.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairFiber

variable {n : ℕ} {d : Fin n → ℕ}
attribute [local instance] Classical.propDecidable

def fiberSwapEquiv (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) : Equiv.Perm (StateFiber G i j) :=
  ((stateFiberEquiv G i j hij).trans
    (assignmentRelabelEquiv G.val i j (Equiv.swap x y))).trans
      (stateFiberEquiv G i j hij).symm

theorem fiberSwapEquiv_apply (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (H : StateFiber G i j) :
    fiberSwapEquiv G i j hij x y H =
      (stateFiberEquiv G i j hij).symm
        (assignmentRelabel G.val i j (Equiv.swap x y)
          (stateFiberEquiv G i j hij H)) := rfl

theorem fiberSwapEquiv_leftSet (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (H : StateFiber G i j) :
    leftSet (fiberSwapEquiv G i j hij x y H).val.val i j =
      (leftSet H.val.val i j).map (Equiv.swap x.val y.val).toEmbedding := by
  rw [fiberSwapEquiv_apply]
  rw [stateFiberEquiv_symm_apply, leftSet_trade, assignmentRelabel_swap_val]
  rfl

theorem fiberSwapEquiv_eq_of_key_leftSet
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (H : StateFiber G i j)
    (K : GraphState n d)
    (hkey : key i j K.val = key i j H.val.val)
    (hleft : leftSet K.val i j =
      (leftSet H.val.val i j).map (Equiv.swap x.val y.val).toEmbedding) :
    (fiberSwapEquiv G i j hij x y H).val = K := by
  apply Subtype.ext
  apply graph_eq_of_key_leftSet_eq
  · exact (fiberSwapEquiv G i j hij x y H).property.trans
      (hkey.trans H.property).symm
  · exact (fiberSwapEquiv_leftSet G i j hij x y H).trans hleft.symm

theorem fiberSwapEquiv_involutive
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) :
    Function.Involutive (fiberSwapEquiv G i j hij x y) := by
  intro H
  apply Subtype.ext
  apply Subtype.ext
  apply graph_eq_of_key_leftSet_eq
  · exact (fiberSwapEquiv G i j hij x y
      (fiberSwapEquiv G i j hij x y H)).property.trans H.property.symm
  · rw [fiberSwapEquiv_leftSet, fiberSwapEquiv_leftSet, Finset.map_map]
    have he : (Equiv.swap x.val y.val).toEmbedding.trans
        (Equiv.swap x.val y.val).toEmbedding = Function.Embedding.refl (Fin n) := by
      apply Function.Embedding.ext
      intro z
      exact Equiv.swap_apply_self x.val y.val z
    rw [he, Finset.map_refl]

theorem fiberSwap_squared_displacement
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (f : GraphState n d → ℝ) :
    (∑ H : StateFiber G i j,
      (f H.val - f (fiberSwapEquiv G i j hij x y H).val) ^ 2) =
    ∑ T : Assignment G.val i j,
      (f ((stateFiberEquiv G i j hij).symm T).val -
       f ((stateFiberEquiv G i j hij).symm
         (assignmentRelabel G.val i j (Equiv.swap x y) T)).val) ^ 2 := by
  let e := stateFiberEquiv G i j hij
  apply Fintype.sum_equiv e
  intro H
  simp only [e, Equiv.symm_apply_apply, fiberSwapEquiv_apply]

theorem toggle_squared_displacement_eq_assignment_swap
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (toggle : GraphState n d → GraphState n d)
    (hkey : ∀ H : StateFiber G i j,
      key i j (toggle H.val).val = key i j H.val.val)
    (hleft : ∀ H : StateFiber G i j,
      leftSet (toggle H.val).val i j =
        (leftSet H.val.val i j).map (Equiv.swap x.val y.val).toEmbedding)
    (f : GraphState n d → ℝ) :
    (∑ H : StateFiber G i j, (f H.val - f (toggle H.val)) ^ 2) =
    ∑ T : Assignment G.val i j,
      (f ((stateFiberEquiv G i j hij).symm T).val -
       f ((stateFiberEquiv G i j hij).symm
         (assignmentRelabel G.val i j (Equiv.swap x y) T)).val) ^ 2 := by
  rw [← fiberSwap_squared_displacement G i j hij x y f]
  apply Finset.sum_congr rfl
  intro H _
  rw [fiberSwapEquiv_eq_of_key_leftSet G i j hij x y H
    (toggle H.val) (hkey H) (hleft H)]

end Problem315.PairFiber

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairCrossToggleTransport.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SliceEquality.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceEquality

def equalityIndicator {α : Type*} (x : α → ℝ) (i j : α) : ℝ := by
  classical
  exact if x i = x j then 1 else 0

def centeredEquality {α : Type*} (x : α → ℝ) (p : ℝ) (i j : α) : ℝ :=
  equalityIndicator x i j - p

def offDiagonal {α : Type*} [DecidableEq α] (z : α → α → ℝ) (i j : α) : ℝ :=
  if i = j then 0 else z i j

theorem equalityIndicator_polynomial
    {α : Type*} (x : α → ℝ) (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (i j : α) :
    equalityIndicator x i j = 1 - x i - x j + 2 * x i * x j := by
  rcases hbinary i with hi | hi <;> rcases hbinary j with hj | hj <;>
    norm_num [equalityIndicator, hi, hj]

theorem centeredEquality_polynomial
    {α : Type*} (x : α → ℝ) (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (p : ℝ) (i j : α) :
    centeredEquality x p i j = (1 - p - x i) - x j + (2 * x i) * x j := by
  rw [centeredEquality, equalityIndicator_polynomial x hbinary]
  ring

theorem centeredEquality_symmetric
    {α : Type*} (x : α → ℝ) (p : ℝ) (i j : α) :
    centeredEquality x p i j = centeredEquality x p j i := by
  simp [centeredEquality, equalityIndicator, eq_comm]

theorem offDiagonal_symmetric
    {α : Type*} [DecidableEq α] (z : α → α → ℝ)
    (hsymm : ∀ i j, z i j = z j i) (i j : α) :
    offDiagonal z i j = offDiagonal z j i := by
  simp [offDiagonal, eq_comm, hsymm]

theorem sum_offDiagonal
    {α : Type*} [Fintype α] [DecidableEq α] (z : α → α → ℝ) (i : α) :
    (∑ j, offDiagonal z i j) = (∑ j, z i j) - z i i := by
  have hterm (j : α) : offDiagonal z i j = z i j - if i = j then z i i else 0 := by
    by_cases hij : i = j
    · subst j
      simp [offDiagonal]
    · simp [offDiagonal, hij]
  simp_rw [hterm]
  simp [Finset.sum_sub_distrib]

theorem centeredEquality_row_sum
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (q p : ℝ) (hsum : ∑ j, x j = q) (i : α) :
    (∑ j, offDiagonal (centeredEquality x p) i j) =
      ((Fintype.card α : ℝ) - q - 1) - ((Fintype.card α : ℝ) - 1) * p +
        (2 * q - (Fintype.card α : ℝ)) * x i := by
  rw [sum_offDiagonal]
  have hdiag : centeredEquality x p i i = 1 - p := by
    simp [centeredEquality, equalityIndicator]
  rw [hdiag]
  simp_rw [centeredEquality_polynomial x hbinary]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, hsum]
  ring

theorem additive_coeff_pairing
    {α : Type*} [Fintype α]
    (u : α → ℝ) (z : α → α → ℝ) (hsymm : ∀ i j, z i j = z j i) :
    (1 / 2 : ℝ) * (∑ i, ∑ j, (u i + u j) * z i j) =
      ∑ i, u i * (∑ j, z i j) := by
  have htranspose : (∑ i, ∑ j, u j * z i j) = ∑ i, ∑ j, u i * z i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsymm j i]
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [htranspose]
  simp_rw [← Finset.mul_sum]
  ring

theorem additive_centeredEquality_image
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (q p : ℝ) (hsum : ∑ j, x j = q)
    (u : α → ℝ) (hu : ∑ i, u i = 0) :
    (1 / 2 : ℝ) *
      (∑ i, ∑ j, (u i + u j) * offDiagonal (centeredEquality x p) i j) =
      (2 * q - (Fintype.card α : ℝ)) * (∑ i, u i * x i) := by
  rw [additive_coeff_pairing u _
    (offDiagonal_symmetric _ (centeredEquality_symmetric x p))]
  simp_rw [centeredEquality_row_sum x hbinary q p hsum]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hu, zero_mul, zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem centeredEquality_total
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (q p : ℝ) (hsum : ∑ j, x j = q) :
    (∑ i, ∑ j, offDiagonal (centeredEquality x p) i j) =
      q * (q - 1) + ((Fintype.card α : ℝ) - q) * ((Fintype.card α : ℝ) - q - 1) -
        (Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1) * p := by
  simp_rw [centeredEquality_row_sum x hbinary q p hsum]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum, hsum]
  ring

theorem centeredEquality_total_zero
    {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : 2 ≤ Fintype.card α)
    (x : α → ℝ) (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (q : ℝ) (hsum : ∑ j, x j = q) :
    (∑ i, ∑ j, offDiagonal
      (centeredEquality x
        ((q * (q - 1) + ((Fintype.card α : ℝ) - q) * ((Fintype.card α : ℝ) - q - 1)) /
          ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1)))) i j) = 0 := by
  rw [centeredEquality_total x hbinary q _ hsum]
  have hc : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hcard
  have hn : (Fintype.card α : ℝ) ≠ 0 := by linarith
  have hm : (Fintype.card α : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

theorem row_zero_centeredEquality_image
    {α : Type*} [Fintype α]
    (x : α → ℝ) (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (p : ℝ) (c : α → α → ℝ)
    (hrow : ∀ i, ∑ j, c i j = 0) (hcol : ∀ j, ∑ i, c i j = 0) :
    (∑ i, ∑ j, c i j * centeredEquality x p i j) =
      2 * (∑ i, ∑ j, c i j * (x i * x j)) := by
  have hconstant : (∑ i, ∑ j, c i j * (1 - p)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [← Finset.sum_mul, hrow, zero_mul]
  have hleft : (∑ i, ∑ j, c i j * x i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [← Finset.sum_mul, hrow, zero_mul]
  have hright : (∑ i, ∑ j, c i j * x j) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j hj
    rw [← Finset.sum_mul, hcol, zero_mul]
  calc
    _ = ∑ i, ∑ j,
        (c i j * (1 - p) - c i j * x i - c i j * x j +
          2 * (c i j * (x i * x j))) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [centeredEquality_polynomial x hbinary]
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hconstant, hleft, hright]
      ring

theorem row_zero_offDiagonal_centeredEquality_image
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (p : ℝ) (c : α → α → ℝ) (hdiag : ∀ i, c i i = 0)
    (hrow : ∀ i, ∑ j, c i j = 0) (hcol : ∀ j, ∑ i, c i j = 0) :
    (1 / 2 : ℝ) * (∑ i, ∑ j, c i j * offDiagonal (centeredEquality x p) i j) =
      ∑ i, ∑ j, c i j * (x i * x j) := by
  have hterm (i j : α) :
      c i j * offDiagonal (centeredEquality x p) i j =
        c i j * centeredEquality x p i j := by
    by_cases hij : i = j
    · subst j
      simp [hdiag]
    · simp [offDiagonal, hij]
  simp_rw [hterm]
  rw [row_zero_centeredEquality_image x hbinary p c hrow hcol]
  ring

end Problem315.SliceEquality

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SliceEquality.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SliceNormalizedFamily.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceNormalized

variable {V : Type*} [Fintype V] [sectionDecidableEqV : DecidableEq V]

abbrev State (V : Type*) [Fintype V] (q : ℕ) :=
  ↥((Finset.univ : Finset V).powersetCard q)

abbrev Space (V : Type*) [Fintype V] (q : ℕ) := EuclideanSpace ℝ (State V q)

def raw (q : ℕ) (i j : V) : Space V q :=
  WithLp.toLp 2 (fun S => if i = j then 0 else
    SliceMoments.centeredEqual Finset.univ q i j S.val)

def denominator (V : Type*) [Fintype V] (q : ℕ) : ℝ :=
  Real.sqrt (2 * (Nat.choose (Fintype.card V) q : ℝ) *
    SliceMoments.equalMean (Finset.univ : Finset V) q *
      (1 - SliceMoments.equalMean (Finset.univ : Finset V) q))

def column (q : ℕ) (i j : V) : Space V q :=
  (denominator V q)⁻¹ • raw q i j

@[simp] theorem raw_diag (q : ℕ) (i : V) : raw q i i = 0 := by
  ext S
  simp [raw]

@[simp] theorem column_diag (q : ℕ) (i : V) : column q i i = 0 := by
  simp [column]

theorem raw_symmetric (q : ℕ) (i j : V) : raw q i j = raw q j i := by
  ext S
  simp [raw, SliceMoments.centeredEqual, SliceMoments.equalIndicator, eq_comm, iff_comm]

theorem column_symmetric (q : ℕ) (i j : V) : column q i j = column q j i := by
  rw [column, column, raw_symmetric q i j]

theorem coord_sum (q : ℕ) (S : State V q) :
    ∑ i, SliceMoments.coord i S.val = (q : ℝ) := by
  have hcard := (Finset.mem_powersetCard.mp S.property).2
  simp [SliceMoments.coord, ← hcard]

theorem centered_eq_binary (q : ℕ) (S : State V q) (i j : V) :
    SliceEquality.centeredEquality (fun k => SliceMoments.coord k S.val)
      (SliceMoments.equalMean (Finset.univ : Finset V) q) i j =
    SliceMoments.centeredEqual Finset.univ q i j S.val := by
  unfold SliceEquality.centeredEquality SliceEquality.equalityIndicator
    SliceMoments.centeredEqual SliceMoments.equalIndicator SliceMoments.coord
  by_cases hi : i ∈ S.val <;> by_cases hj : j ∈ S.val <;> simp [hi, hj]

theorem raw_total (q : ℕ) (hN : 2 ≤ Fintype.card V) :
    (∑ i, ∑ j, raw q i j : Space V q) = 0 := by
  ext S
  have hb (i : V) : SliceMoments.coord i S.val = 0 ∨
      SliceMoments.coord i S.val = 1 := by
    by_cases hi : i ∈ S.val <;> simp [SliceMoments.coord, hi]
  have ht := SliceEquality.centeredEquality_total_zero hN
    (fun i => SliceMoments.coord i S.val) hb (q : ℝ) (coord_sum q S)
  have hp : SliceMoments.equalMean (Finset.univ : Finset V) q =
      ((q : ℝ) * (q - 1) + ((Fintype.card V : ℝ) - q) *
        ((Fintype.card V : ℝ) - q - 1)) /
        ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) := by
    simp [SliceMoments.equalMean]
  rw [← hp] at ht
  simp_rw [SliceEquality.offDiagonal, centered_eq_binary q S] at ht
  simpa [raw, SliceEquality.offDiagonal] using ht

theorem column_total (q : ℕ) (hN : 2 ≤ Fintype.card V) :
    (∑ i, ∑ j, column q i j : Space V q) = 0 := by
  simp only [column, ← Finset.smul_sum, raw_total q hN, smul_zero]

theorem raw_inner (q : ℕ) (hq : q ≤ Fintype.card V)
    (i j k l : V) (hij : i ≠ j) (hkl : k ≠ l) :
    ⟪raw q i j, raw q k l⟫ = (Nat.choose (Fintype.card V) q : ℝ) *
      SliceMoments.average Finset.univ q (fun S =>
        SliceMoments.centeredEqual Finset.univ q i j S *
        SliceMoments.centeredEqual Finset.univ q k l S) := by
  have hc : (Nat.choose (Fintype.card V) q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hq).ne'
  simp only [raw, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    star_trivial, hij, hkl, ite_false]
  change (∑ S : ↥((Finset.univ : Finset V).powersetCard q),
    SliceMoments.centeredEqual Finset.univ q k l S.val *
    SliceMoments.centeredEqual Finset.univ q i j S.val) = _
  rw [Finset.sum_coe_sort ((Finset.univ : Finset V).powersetCard q)
    (fun S => SliceMoments.centeredEqual Finset.univ q k l S *
      SliceMoments.centeredEqual Finset.univ q i j S)]
  simp only [SliceMoments.average, Finset.card_univ]
  field_simp
  simp only [mul_comm]

theorem raw_norm_sq (q : ℕ) (hq : q ≤ Fintype.card V)
    (i j : V) (hij : i ≠ j) :
    ‖raw q i j‖ ^ 2 = (Nat.choose (Fintype.card V) q : ℝ) *
      (SliceMoments.equalMean (Finset.univ : Finset V) q *
        (1 - SliceMoments.equalMean (Finset.univ : Finset V) q)) := by
  rw [← real_inner_self_eq_norm_sq, raw_inner q hq i j i j hij hij]
  simp_rw [← pow_two]
  rw [SliceMoments.average_centeredEqual_sq Finset.univ q
    (by simpa using hq) i j (Finset.mem_univ i) (Finset.mem_univ j) hij]

include sectionDecidableEqV in
theorem denominator_sq (q : ℕ)
    (hp : 0 ≤ SliceMoments.equalMean (Finset.univ : Finset V) q)
    (hp1 : SliceMoments.equalMean (Finset.univ : Finset V) q ≤ 1) :
    denominator V q ^ 2 = 2 * (Nat.choose (Fintype.card V) q : ℝ) *
      SliceMoments.equalMean (Finset.univ : Finset V) q *
        (1 - SliceMoments.equalMean (Finset.univ : Finset V) q) := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  apply Real.sq_sqrt
  exact mul_nonneg (mul_nonneg (by positivity) hp) (sub_nonneg.mpr hp1)

theorem column_inner_unsimplified (q : ℕ) (hq : q ≤ Fintype.card V)
    (i j k l : V) (hij : i ≠ j) (hkl : k ≠ l) :
    ⟪column q i j, column q k l⟫ =
      ((Nat.choose (Fintype.card V) q : ℝ) / denominator V q ^ 2) *
      SliceMoments.average Finset.univ q (fun S =>
        SliceMoments.centeredEqual Finset.univ q i j S *
        SliceMoments.centeredEqual Finset.univ q k l S) := by
  rw [column, column, inner_smul_left, inner_smul_right,
    raw_inner q hq i j k l hij hkl]
  simp only [RCLike.conj_to_real]
  ring

theorem column_inner (q : ℕ) (hq : q ≤ Fintype.card V)
    (hp : 0 < SliceMoments.equalMean (Finset.univ : Finset V) q)
    (hp1 : SliceMoments.equalMean (Finset.univ : Finset V) q < 1)
    (i j k l : V) (hij : i ≠ j) (hkl : k ≠ l) :
    ⟪column q i j, column q k l⟫ =
      SliceMoments.average Finset.univ q (fun S =>
        SliceMoments.centeredEqual Finset.univ q i j S *
        SliceMoments.centeredEqual Finset.univ q k l S) /
      (2 * SliceMoments.equalMean (Finset.univ : Finset V) q *
        (1 - SliceMoments.equalMean (Finset.univ : Finset V) q)) := by
  rw [column_inner_unsimplified q hq i j k l hij hkl,
    denominator_sq q hp.le hp1.le]
  have hc : (Nat.choose (Fintype.card V) q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hq).ne'
  have hpc : 1 - SliceMoments.equalMean (Finset.univ : Finset V) q ≠ 0 := by
    linarith
  field_simp

theorem column_norm_sq (q : ℕ) (hq : q ≤ Fintype.card V)
    (hp : 0 < SliceMoments.equalMean (Finset.univ : Finset V) q)
    (hp1 : SliceMoments.equalMean (Finset.univ : Finset V) q < 1)
    (i j : V) (hij : i ≠ j) : ‖column q i j‖ ^ 2 = (1 / 2 : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, column_inner q hq hp hp1 i j i j hij hij]
  simp_rw [← pow_two]
  rw [SliceMoments.average_centeredEqual_sq Finset.univ q
    (by simpa using hq) i j (Finset.mem_univ i) (Finset.mem_univ j) hij]
  have hpc : 1 - SliceMoments.equalMean (Finset.univ : Finset V) q ≠ 0 := by
    linarith
  field_simp

end Problem315.SliceNormalized

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SliceNormalizedFamily.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairFiberEqualityTransport.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairFiber

attribute [local instance] Classical.propDecidable

def cardSliceEquivPowerset {V : Type*} [Fintype V] (q : ℕ) :
    SlicePermutationAction.Slice V q ≃ SliceNormalized.State V q where
  toFun S := ⟨S.val, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, S.property⟩⟩
  invFun S := ⟨S.val, (Finset.mem_powersetCard.mp S.property).2⟩
  left_inv S := by apply Subtype.ext; rfl
  right_inv S := by apply Subtype.ext; rfl

def stateFiberNormalizedEquiv {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) :
    StateFiber G i j ≃
      SliceNormalized.State (singletonSet G.val i j) (leftSet G.val i j).card :=
  ((stateFiberEquiv G i j hij).trans (assignmentSliceEquiv G.val i j)).trans
    (cardSliceEquivPowerset _)

theorem stateFiberNormalizedEquiv_mem {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (H : StateFiber G i j) (x : singletonSet G.val i j) :
    x ∈ (stateFiberNormalizedEquiv G i j hij H).val ↔
      H.val.val.Adj i x.val := by
  change x ∈ (leftSet H.val.val i j).subtype
    (fun z => z ∈ singletonSet G.val i j) ↔ _
  rw [Finset.mem_subtype, mem_leftSet]
  have hx : x.val ∈ singletonSet H.val.val i j := by
    rw [singletonSet_eq_of_key_eq H.property]
    exact x.property
  obtain ⟨hxo, hxor⟩ := (mem_singletonSet H.val.val i j x.val).mp hx
  rcases hxor with ht | ht <;> simp_all

theorem raw_stateFiberNormalizedEquiv {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (H : StateFiber G i j) :
    SliceNormalized.raw (leftSet G.val i j).card x y
      (stateFiberNormalizedEquiv G i j hij H) =
      if x = y then 0 else
        (if H.val.val.Adj i x.val ↔ H.val.val.Adj i y.val then (1 : ℝ) else 0) -
          SliceMoments.equalMean (Finset.univ : Finset (singletonSet G.val i j))
            (leftSet G.val i j).card := by
  simp only [SliceNormalized.raw,
    SliceMoments.centeredEqual, SliceMoments.equalIndicator,
    stateFiberNormalizedEquiv_mem]

theorem equalIndicator_stateFiberNormalizedEquiv {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (H : StateFiber G i j) :
    SliceMoments.equalIndicator x y (stateFiberNormalizedEquiv G i j hij H).val =
      if H.val.val.Adj i x.val ↔ H.val.val.Adj i y.val then (1 : ℝ) else 0 := by
  simp only [SliceMoments.equalIndicator, stateFiberNormalizedEquiv_mem]

theorem stateFiber_average_equality {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (hxy : x ≠ y) :
    (∑ H : StateFiber G i j,
      if H.val.val.Adj i x.val ↔ H.val.val.Adj i y.val then (1 : ℝ) else 0) /
        (Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card : ℝ) =
      SliceMoments.equalMean (Finset.univ : Finset (singletonSet G.val i j))
        (leftSet G.val i j).card := by
  let e := stateFiberNormalizedEquiv G i j hij
  have hs : (∑ H : StateFiber G i j,
      if H.val.val.Adj i x.val ↔ H.val.val.Adj i y.val then (1 : ℝ) else 0) =
      ∑ S : SliceNormalized.State (singletonSet G.val i j) (leftSet G.val i j).card,
        SliceMoments.equalIndicator x y S.val := by
    apply Fintype.sum_equiv e
    intro H
    exact (equalIndicator_stateFiberNormalizedEquiv G i j hij x y H).symm
  rw [hs]
  have hq : (leftSet G.val i j).card ≤
      (Finset.univ : Finset (singletonSet G.val i j)).card := by
    simpa using Finset.card_le_card (leftSet_subset_singletonSet G.val i j)
  have hm := SliceMoments.average_equalIndicator
    (Finset.univ : Finset (singletonSet G.val i j)) (leftSet G.val i j).card hq
    x y (Finset.mem_univ x) (Finset.mem_univ y) hxy
  simpa only [SliceMoments.average, Finset.sum_coe_sort, Finset.card_univ,
    Fintype.card_coe] using hm

theorem stateFiber_sum_eq_fiberStates {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (f : GraphState n d → ℝ) :
    (∑ H : StateFiber G i j, f H.val) =
      ∑ H ∈ PairResampling.fiberStates {i, j} G, f H := by
  let e : StateFiber G i j ≃ PairResampling.fiberStates {i, j} G :=
    { toFun H := ⟨H.val, (PairResampling.mem_fiberStates {i, j} G H.val).mpr
        ((sameFiber_iff_key_eq i j hij G.val H.val.val).mpr H.property.symm)⟩
      invFun H := ⟨H.val, ((sameFiber_iff_key_eq i j hij G.val H.val.val).mp
        ((PairResampling.mem_fiberStates {i, j} G H.val).mp H.property)).symm⟩
      left_inv H := by apply Subtype.ext; rfl
      right_inv H := by apply Subtype.ext; rfl }
  calc
    _ = ∑ H : PairResampling.fiberStates {i, j} G, f (e.symm H).val :=
      (Equiv.sum_comp e.symm (fun H : StateFiber G i j => f H.val)).symm
    _ = ∑ H : PairResampling.fiberStates {i, j} G, f H.val := rfl
    _ = _ := Finset.sum_coe_sort _ _

theorem expectation_eq_equalMean_of_fiber {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (hxy : x ≠ y)
    (f : PairResampling.StateSpace n d)
    (hf : ∀ H : StateFiber G i j, f H.val =
      if H.val.val.Adj i x.val ↔ H.val.val.Adj i y.val then (1 : ℝ) else 0) :
    PairResampling.expectation n d {i, j} f G =
      SliceMoments.equalMean (Finset.univ : Finset (singletonSet G.val i j))
        (leftSet G.val i j).card := by
  rw [PairResampling.expectation_eq_average, fiberStates_card G i j hij,
    ← stateFiber_sum_eq_fiberStates G i j hij]
  simp_rw [hf]
  exact stateFiber_average_equality G i j hij x y hxy

theorem fluctuation_eq_raw_of_fiber {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (hxy : x ≠ y)
    (f : PairResampling.StateSpace n d)
    (hf : ∀ H : StateFiber G i j, f H.val =
      if H.val.val.Adj i x.val ↔ H.val.val.Adj i y.val then (1 : ℝ) else 0)
    (H : StateFiber G i j) :
    PairResampling.fluctuation n d {i, j} f H.val =
      SliceNormalized.raw (leftSet G.val i j).card x y
        (stateFiberNormalizedEquiv G i j hij H) := by
  have hexp : PairResampling.expectation n d {i, j} f H.val =
      PairResampling.expectation n d {i, j} f G :=
    PairResampling.expectation_mem {i, j} f H.val G
      ((sameFiber_iff_key_eq i j hij H.val.val G.val).mpr H.property)
  rw [PairResampling.fluctuation_eq_sub]
  change f H.val - PairResampling.expectation n d {i, j} f H.val = _
  rw [hexp, expectation_eq_equalMean_of_fiber G i j hij x y hxy f hf,
    hf H, raw_stateFiberNormalizedEquiv]
  simp only [hxy, ite_false]

end Problem315.PairFiber

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairFiberEqualityTransport.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairFiberEnergy.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
attribute [local instance] Classical.propDecidable

namespace Problem315.PairResampling

variable {n : Nat} {d : Fin n → Nat}

theorem sum_expectation (a : Finset (Fin n)) (f : StateSpace n d) :
    (∑ G, expectation n d a f G) = ∑ G, f G := by
  let one : StateSpace n d := WithLp.toLp 2 (fun _ => 1)
  have hone : expectation n d a one = one :=
    (expectation_eq_self_iff a one).mpr (constant_mem a 1)
  have h := expectation_isSymmetric a f one
  change inner ℝ (expectation n d a f) one = inner ℝ f (expectation n d a one) at h
  rw [hone, state_inner, state_inner] at h
  simpa [one] using h

theorem sum_fiber_average (a : Finset (Fin n)) (g : GraphState n d → ℝ) :
    (∑ G, (∑ H ∈ fiberStates a G, g H) / (fiberStates a G).card) = ∑ G, g G := by
  let f : StateSpace n d := WithLp.toLp 2 g
  have h := sum_expectation a f
  simpa only [expectation_eq_average, f] using h

theorem inner_fluctuation_eq_sum_fiber_variance (a : Finset (Fin n))
    (f : StateSpace n d) :
    inner ℝ f (fluctuation n d a f) =
      ∑ G, (∑ H ∈ fiberStates a G,
        (f H - expectation n d a f G) ^ 2) / (fiberStates a G).card := by
  have heq : ∀ G H, H ∈ fiberStates a G →
      expectation n d a f H = expectation n d a f G := by
    intro G H hH
    exact (expectation_mem a f) H G ((mem_fiberStates a G H).mp hH).symm
  calc
    inner ℝ f (fluctuation n d a f) =
        inner ℝ (fluctuation n d a f) (fluctuation n d a f) := by
      rw [inner_fluctuation, real_inner_self_eq_norm_sq]
    _ = ∑ G, (f G - expectation n d a f G) ^ 2 := by
      rw [state_inner, fluctuation_eq_sub]
      apply Finset.sum_congr rfl
      intro G hG
      change (f G - expectation n d a f G) * (f G - expectation n d a f G) = _
      ring
    _ = ∑ G, (∑ H ∈ fiberStates a G,
        (f H - expectation n d a f H) ^ 2) / (fiberStates a G).card :=
      (sum_fiber_average a (fun H => (f H - expectation n d a f H) ^ 2)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro G hG
      congr 1
      apply Finset.sum_congr rfl
      intro H hH
      rw [heq G H hH]

theorem inner_fluctuation_le_of_fiber_variance_bound
    (a : Finset (Fin n)) (f : StateSpace n d) (e : GraphState n d → ℝ) (C : ℝ)
    (hlocal : ∀ G : GraphState n d,
      (∑ H ∈ fiberStates a G, (f H - expectation n d a f G) ^ 2) /
          (fiberStates a G).card ≤
        C * ((∑ H ∈ fiberStates a G, e H) / (fiberStates a G).card)) :
    inner ℝ f (fluctuation n d a f) ≤ C * ∑ G, e G := by
  rw [inner_fluctuation_eq_sum_fiber_variance]
  calc
    _ ≤ ∑ G, C * ((∑ H ∈ fiberStates a G, e H) / (fiberStates a G).card) :=
      Finset.sum_le_sum (fun G _ => hlocal G)
    _ = _ := by rw [← Finset.mul_sum, sum_fiber_average]

end Problem315.PairResampling

namespace Problem315.PairFiber

variable {n : Nat} {d : Fin n → Nat}

theorem assignment_average_eq_fiber_average
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) (g : GraphState n d → ℝ) :
    (∑ T : Assignment G.val i j, g ((stateFiberEquiv G i j hij).symm T).val) /
        (Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card : ℝ) =
      (∑ H ∈ PairResampling.fiberStates {i, j} G, g H) /
        (PairResampling.fiberStates {i, j} G).card := by
  let f : PairResampling.StateSpace n d := WithLp.toLp 2 g
  have h := expectation_eq_assignment_average G i j hij f
  rw [PairResampling.expectation_eq_average] at h
  exact h.symm

theorem inner_fluctuation_le_of_assignment_variance_bound
    (i j : Fin n) (hij : i ≠ j) (f : PairResampling.StateSpace n d)
    (e : GraphState n d → ℝ) (C : ℝ)
    (hlocal : ∀ G : GraphState n d,
      (∑ T : Assignment G.val i j,
        (f ((stateFiberEquiv G i j hij).symm T).val -
          PairResampling.expectation n d {i, j} f G) ^ 2) /
          (Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card : ℝ) ≤
        C * ((∑ T : Assignment G.val i j, e ((stateFiberEquiv G i j hij).symm T).val) /
          (Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card : ℝ))) :
    inner ℝ f (PairResampling.fluctuation n d {i, j} f) ≤ C * ∑ G, e G := by
  apply PairResampling.inner_fluctuation_le_of_fiber_variance_bound {i, j} f e C
  intro G
  rw [← assignment_average_eq_fiber_average G i j hij
      (fun H => (f H - PairResampling.expectation n d {i, j} f G) ^ 2),
    ← assignment_average_eq_fiber_average G i j hij e]
  exact hlocal G

theorem inner_fluctuation_le_of_assignment_sum_bound
    (i j : Fin n) (hij : i ≠ j) (f : PairResampling.StateSpace n d)
    (e : GraphState n d → ℝ) (C : ℝ)
    (hlocal : ∀ G : GraphState n d,
      (∑ T : Assignment G.val i j,
        (f ((stateFiberEquiv G i j hij).symm T).val -
          PairResampling.expectation n d {i, j} f G) ^ 2) ≤
        C * (∑ T : Assignment G.val i j, e ((stateFiberEquiv G i j hij).symm T).val)) :
    inner ℝ f (PairResampling.fluctuation n d {i, j} f) ≤ C * ∑ G, e G := by
  apply inner_fluctuation_le_of_assignment_variance_bound i j hij f e C
  intro G
  simpa only [mul_div_assoc] using
    div_le_div_of_nonneg_right (hlocal G)
      (show (0 : ℝ) ≤ Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card by
        positivity)

end Problem315.PairFiber

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairFiberEnergy.lean -/
