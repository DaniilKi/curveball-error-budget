import AnalyticSliceSynthesis

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairOrbit.lean -/
section

namespace OAI

noncomputable section

namespace Problem315.PairOrbit

variable {α : Type*} [sectionFintypeα : Fintype α] [DecidableEq α]

def membershipColor (S T : Finset α) (a : α) : Bool × Bool :=
  (decide (a ∈ S), decide (a ∈ T))

theorem color_filter (S T : Finset α) (b c : Bool) :
    (Finset.univ.filter fun a => membershipColor S T a = (b,c)) =
      if b then (if c then S ∩ T else S \ T)
      else (if c then T \ S else Finset.univ \ (S ∪ T)) := by
  cases b <;> cases c <;> ext a <;>
    simp [membershipColor, not_or, and_comm]

theorem membershipColor_fiber_card
    (S T U V : Finset α)
    (hS : S.card = U.card) (hT : T.card = V.card)
    (hI : (S ∩ T).card = (U ∩ V).card) (b : Bool × Bool) :
    Fintype.card {a // membershipColor S T a = b} =
      Fintype.card {a // membershipColor U V a = b} := by
  have hdiff : (S \ T).card = (U \ V).card := by
    have ha := Finset.card_sdiff_add_card_inter S T
    have hb := Finset.card_sdiff_add_card_inter U V
    omega
  have hdiff' : (T \ S).card = (V \ U).card := by
    have ha := Finset.card_sdiff_add_card_inter T S
    have hb := Finset.card_sdiff_add_card_inter V U
    have hI' : (T ∩ S).card = (V ∩ U).card := by simpa [Finset.inter_comm] using hI
    omega
  have hunion : (S ∪ T).card = (U ∪ V).card := by
    have ha := Finset.card_union_add_card_inter S T
    have hb := Finset.card_union_add_card_inter U V
    omega
  have hcompl : (Finset.univ \ (S ∪ T)).card = (Finset.univ \ (U ∪ V)).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_sdiff_of_subset (Finset.subset_univ _), hunion]
  rcases b with ⟨b,c⟩
  rw [Fintype.card_subtype, Fintype.card_subtype, color_filter, color_filter]
  cases b <;> cases c <;> simp [hI, hdiff, hdiff', hcompl]

theorem exists_perm_membership
    (S T U V : Finset α)
    (hS : S.card = U.card) (hT : T.card = V.card)
    (hI : (S ∩ T).card = (U ∩ V).card) :
    ∃ e : Equiv.Perm α,
      (∀ a, a ∈ S ↔ e a ∈ U) ∧ (∀ a, a ∈ T ↔ e a ∈ V) := by
  let ef : ∀ b : Bool × Bool,
      {a // membershipColor S T a = b} ≃ {a // membershipColor U V a = b} :=
    fun b => Fintype.equivOfCardEq (membershipColor_fiber_card S T U V hS hT hI b)
  let e : Equiv.Perm α := Equiv.ofFiberEquiv ef
  have hc (a : α) : membershipColor U V (e a) = membershipColor S T a :=
    Equiv.ofFiberEquiv_map ef a
  refine ⟨e, ?_, ?_⟩
  · intro a
    have hh := congrArg Prod.fst (hc a)
    simpa [membershipColor, eq_comm] using hh
  · intro a
    have hh := congrArg Prod.snd (hc a)
    simpa [membershipColor, eq_comm] using hh

include sectionFintypeα in
theorem image_eq_of_membership (S U : Finset α) (e : Equiv.Perm α)
    (h : ∀ a, a ∈ S ↔ e a ∈ U) : S.image e = U := by
  have retainedsectionFintypeα := sectionFintypeα
  ext b
  constructor
  · intro hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact (h a).mp ha
  · intro hb
    apply Finset.mem_image.mpr
    refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
    apply (h (e.symm b)).mpr
    simpa using hb

theorem exists_perm_image
    (S T U V : Finset α)
    (hS : S.card = U.card) (hT : T.card = V.card)
    (hI : (S ∩ T).card = (U ∩ V).card) :
    ∃ e : Equiv.Perm α, S.image e = U ∧ T.image e = V := by
  obtain ⟨e, heS, heT⟩ := exists_perm_membership S T U V hS hT hI
  exact ⟨e, image_eq_of_membership S U e heS, image_eq_of_membership T V e heT⟩

theorem invariant_kernel_eq_of_card
    {β : Type*} (K : Finset α → Finset α → β)
    (hinv : ∀ (e : Equiv.Perm α) S T, K (S.image e) (T.image e) = K S T)
    (S T U V : Finset α)
    (hS : S.card = U.card) (hT : T.card = V.card)
    (hI : (S ∩ T).card = (U ∩ V).card) : K S T = K U V := by
  obtain ⟨e, heS, heT⟩ := exists_perm_image S T U V hS hT hI
  simpa only [heS, heT] using (hinv e S T).symm

theorem invariant_pair_kernel_eq_of_intersection
    {β : Type*} (K : Finset α → Finset α → β)
    (hinv : ∀ (e : Equiv.Perm α) S T, K (S.image e) (T.image e) = K S T)
    (S T U V : Finset α)
    (hS : S.card = 2) (hT : T.card = 2) (hU : U.card = 2) (hV : V.card = 2)
    (hI : (S ∩ T).card = (U ∩ V).card) : K S T = K U V := by
  exact invariant_kernel_eq_of_card K hinv S T U V (hS.trans hU.symm)
    (hT.trans hV.symm) hI

include sectionFintypeα in
theorem gram_invariant
    {Ω : Type*} [Fintype Ω]
    (action : Equiv.Perm α → Equiv.Perm Ω)
    (z : Finset α → Ω → ℝ)
    (hz : ∀ (e : Equiv.Perm α) S ω, z (S.image e) (action e ω) = z S ω)
    (e : Equiv.Perm α) (S T : Finset α) :
    (∑ ω, z (S.image e) ω * z (T.image e) ω) = ∑ ω, z S ω * z T ω := by
  have retainedsectionFintypeα := sectionFintypeα
  rw [← Equiv.sum_comp (action e) (fun ω => z (S.image e) ω * z (T.image e) ω)]
  simp_rw [hz]

theorem gram_eq_of_intersection
    {Ω : Type*} [Fintype Ω]
    (action : Equiv.Perm α → Equiv.Perm Ω)
    (z : Finset α → Ω → ℝ)
    (hz : ∀ (e : Equiv.Perm α) S ω, z (S.image e) (action e ω) = z S ω)
    (S T U V : Finset α)
    (hS : S.card = U.card) (hT : T.card = V.card)
    (hI : (S ∩ T).card = (U ∩ V).card) :
    (∑ ω, z S ω * z T ω) = ∑ ω, z U ω * z V ω := by
  exact invariant_kernel_eq_of_card (fun S T => ∑ ω, z S ω * z T ω)
    (gram_invariant action z hz) S T U V hS hT hI

end Problem315.PairOrbit

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairOrbit.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SliceGramOrbit.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceGramOrbit

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem average_relabel (q : ℕ) (e : Equiv.Perm α) (f : Finset α → ℝ) :
    SliceMoments.average Finset.univ q (fun S => f (S.image e)) =
      SliceMoments.average Finset.univ q f := by
  unfold SliceMoments.average
  congr 1
  apply Finset.sum_bij (fun S _ => S.image e)
  · intro S hS
    have hc := (Finset.mem_powersetCard.mp hS).2
    simp [Finset.mem_powersetCard, Finset.card_image_of_injective S e.injective, hc]
  · intro S hS T hT hST
    have hh := congrArg (Finset.image e.symm) hST
    simpa [Finset.image_image] using hh
  · intro T hT
    refine ⟨T.image e.symm, ?_, ?_⟩
    · have hc := (Finset.mem_powersetCard.mp hT).2
      simp [Finset.mem_powersetCard, Finset.card_image_of_injective T e.symm.injective, hc]
    · simp [Finset.image_image]
  · intro S hS
    rfl

def pairEquality (P S : Finset α) : ℝ :=
  if (P ∩ S).card = 0 ∨ (P ∩ S).card = 2 then 1 else 0

omit [Fintype α] in
theorem pairEquality_relabel (e : Equiv.Perm α) (P S : Finset α) :
    pairEquality (P.image e) (S.image e) = pairEquality P S := by
  unfold pairEquality
  rw [← Finset.image_inter P S e.injective, Finset.card_image_of_injective _ e.injective]

omit [Fintype α] in
theorem pairEquality_pair (i j : α) (hij : i ≠ j) (S : Finset α) :
    pairEquality {i,j} S = SliceMoments.equalIndicator i j S := by
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    simp [pairEquality, SliceMoments.equalIndicator, hi, hj, hij]

def centeredPair (q : ℕ) (P S : Finset α) : ℝ :=
  pairEquality P S - SliceMoments.equalMean (Finset.univ : Finset α) q

theorem centeredPair_relabel (q : ℕ) (e : Equiv.Perm α) (P S : Finset α) :
    centeredPair q (P.image e) (S.image e) = centeredPair q P S := by
  simp only [centeredPair, pairEquality_relabel]

theorem centeredPair_pair (q : ℕ) (i j : α) (hij : i ≠ j) (S : Finset α) :
    centeredPair q {i,j} S = SliceMoments.centeredEqual Finset.univ q i j S := by
  simp only [centeredPair, SliceMoments.centeredEqual, pairEquality_pair i j hij]

def gram (q : ℕ) (P Q : Finset α) : ℝ :=
  SliceMoments.average Finset.univ q (fun S => centeredPair q P S * centeredPair q Q S)

theorem gram_relabel (q : ℕ) (e : Equiv.Perm α) (P Q : Finset α) :
    gram q (P.image e) (Q.image e) = gram q P Q := by
  unfold gram
  rw [← average_relabel q e (fun S =>
    centeredPair q (P.image e) S * centeredPair q (Q.image e) S)]
  simp_rw [centeredPair_relabel]

theorem gram_eq_of_intersection (q : ℕ) (P Q R T : Finset α)
    (hP : P.card = 2) (hQ : Q.card = 2) (hR : R.card = 2) (hT : T.card = 2)
    (hI : (P ∩ Q).card = (R ∩ T).card) :
    gram q P Q = gram q R T := by
  exact PairOrbit.invariant_pair_kernel_eq_of_intersection (gram q) (gram_relabel q)
    P Q R T hP hQ hR hT hI

theorem centeredEqual_gram_eq_of_intersection (q : ℕ)
    (i j k l a b c d : α)
    (hij : i ≠ j) (hkl : k ≠ l) (hab : a ≠ b) (hcd : c ≠ d)
    (hI : (({i,j} : Finset α) ∩ {k,l}).card = (({a,b} : Finset α) ∩ {c,d}).card) :
    SliceMoments.average Finset.univ q (fun S =>
      SliceMoments.centeredEqual Finset.univ q i j S *
      SliceMoments.centeredEqual Finset.univ q k l S) =
    SliceMoments.average Finset.univ q (fun S =>
      SliceMoments.centeredEqual Finset.univ q a b S *
      SliceMoments.centeredEqual Finset.univ q c d S) := by
  have h := gram_eq_of_intersection q {i,j} {k,l} {a,b} {c,d}
    (by simp [hij]) (by simp [hkl]) (by simp [hab]) (by simp [hcd]) hI
  simpa only [gram, centeredPair_pair q i j hij, centeredPair_pair q k l hkl,
    centeredPair_pair q a b hab, centeredPair_pair q c d hcd] using h

end Problem315.SliceGramOrbit

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SliceGramOrbit.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SliceGramAction.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceCoefficients

variable {V : Type*} [Fintype V] [DecidableEq V]

def orbitKernel (a b d : ℝ) (i j k l : V) : ℝ :=
  if (k = i ∧ l = j) ∨ (k = j ∧ l = i) then a
  else if k = i ∨ k = j ∨ l = i ∨ l = j then b else d

theorem sum_two_and_outside (f : V → ℝ) {i j : V} (hij : i ≠ j) :
    (∑ k, f k) = f i + f j + ∑ k ∈ outside i j, f k := by
  have h := sum_outside f hij
  linarith

theorem half_sum_orbitKernel (a b d : ℝ) (c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    {i j : V} (hij : i ≠ j) :
    (∑ k, ∑ l, orbitKernel a b d i j k l * c k l) / 2 =
      intersectionAction a b d c i j := by
  have hji : j ≠ i := Ne.symm hij
  have hout (k : V) (hk : k ∈ outside i j) : k ≠ i ∧ k ≠ j := by
    simpa [outside, and_comm] using hk
  have hfirst : (∑ l, orbitKernel a b d i j i l * c i l) =
      a * c i j + b * ∑ l ∈ outside i j, c i l := by
    rw [sum_two_and_outside _ hij]
    have hrest : (∑ l ∈ outside i j, orbitKernel a b d i j i l * c i l) =
        b * ∑ l ∈ outside i j, c i l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      obtain ⟨hli, hlj⟩ := hout l hl
      simp [orbitKernel, hij, hli, hlj]
    rw [hrest]
    simp [orbitKernel, hij, hji, hdiag]
  have hsecond : (∑ l, orbitKernel a b d i j j l * c j l) =
      a * c i j + b * ∑ l ∈ outside i j, c j l := by
    rw [sum_two_and_outside _ hij]
    have hrest : (∑ l ∈ outside i j, orbitKernel a b d i j j l * c j l) =
        b * ∑ l ∈ outside i j, c j l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      obtain ⟨hli, hlj⟩ := hout l hl
      simp [orbitKernel, hji, hli, hlj]
    rw [hrest]
    simp [orbitKernel, hij, hji, hdiag, hsym j i]
  have hrest (k : V) (hk : k ∈ outside i j) :
      (∑ l, orbitKernel a b d i j k l * c k l) =
        b * (c i k + c j k) + d * ∑ l ∈ outside i j, c k l := by
    obtain ⟨hki, hkj⟩ := hout k hk
    rw [sum_two_and_outside _ hij]
    have hinner : (∑ l ∈ outside i j, orbitKernel a b d i j k l * c k l) =
        d * ∑ l ∈ outside i j, c k l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      obtain ⟨hli, hlj⟩ := hout l hl
      simp [orbitKernel, hki, hkj, hli, hlj]
    rw [hinner]
    simp only [orbitKernel, hki, hkj, false_and, or_false,
      and_false, hij, hji, ite_false, or_true, ite_true,
      hsym k i, hsym k j]
    ring
  rw [sum_two_and_outside _ hij, hfirst, hsecond]
  have houter : (∑ k ∈ outside i j, ∑ l, orbitKernel a b d i j k l * c k l) =
      b * meetingSum c i j + 2 * d * disjointSum c i j := by
    rw [Finset.sum_congr rfl hrest]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, meetingSum, disjointSum]
    ring
  rw [houter]
  simp only [intersectionAction, hij, ite_false, meetingSum, Finset.sum_add_distrib]
  ring

omit [Fintype V] in

theorem orbitKernel_eq_intersection_card (a b d : ℝ) (i j k l : V)
    (hij : i ≠ j) (hkl : k ≠ l) :
    orbitKernel a b d i j k l =
      if (({i, j} : Finset V) ∩ {k, l}).card = 2 then a
      else if (({i, j} : Finset V) ∩ {k, l}).card = 1 then b else d := by
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    by_cases hli : l = i <;> by_cases hlj : l = j <;>
    simp_all [orbitKernel, Finset.inter_insert, eq_comm]

theorem half_sum_kernel_eq_intersectionAction (a b d : ℝ) (K c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    {i j : V} (hij : i ≠ j)
    (hK : ∀ k l, k ≠ l → K k l = orbitKernel a b d i j k l) :
    (∑ k, ∑ l, K k l * c k l) / 2 = intersectionAction a b d c i j := by
  rw [← half_sum_orbitKernel a b d c hsym hdiag hij]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hkl : k = l
  · subst l; simp [hdiag]
  · rw [hK k l hkl]

theorem half_sum_kernel_of_intersection_card (a b d : ℝ) (K c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    {i j : V} (hij : i ≠ j)
    (hK : ∀ k l, k ≠ l → K k l =
      if (({i, j} : Finset V) ∩ {k, l}).card = 2 then a
      else if (({i, j} : Finset V) ∩ {k, l}).card = 1 then b else d) :
    (∑ k, ∑ l, K k l * c k l) / 2 = intersectionAction a b d c i j := by
  apply half_sum_kernel_eq_intersectionAction a b d K c hsym hdiag hij
  intro k l hkl
  rw [hK k l hkl, orbitKernel_eq_intersection_card a b d i j k l hij hkl]

theorem half_sum_kernel_linearPair (a b d : ℝ) (K : V → V → ℝ)
    (u : V → ℝ) (hu : ∑ i, u i = 0) {i j : V} (hij : i ≠ j)
    (hK : ∀ k l, k ≠ l → K k l = orbitKernel a b d i j k l) :
    (∑ k, ∑ l, K k l * linearPair u k l) / 2 =
      (a + ((Fintype.card V : ℝ) - 4) * b -
        ((Fintype.card V : ℝ) - 3) * d) * linearPair u i j := by
  rw [half_sum_kernel_eq_intersectionAction a b d K (linearPair u)
    (linearPair_symmetric u) (linearPair_diag u) hij hK,
    intersectionAction_linearPair a b d u hu]

theorem half_sum_kernel_rowZero (a b d : ℝ) (K c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    (hrow : ∀ i, rowSum c i = 0) {i j : V} (hij : i ≠ j)
    (hK : ∀ k l, k ≠ l → K k l = orbitKernel a b d i j k l) :
    (∑ k, ∑ l, K k l * c k l) / 2 = (a - 2 * b + d) * c i j := by
  rw [half_sum_kernel_eq_intersectionAction a b d K c hsym hdiag hij hK,
    intersectionAction_rowZero a b d c hsym hdiag hrow]

end Problem315.SliceCoefficients

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SliceGramAction.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SliceGramProfile.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceGramProfile

variable {V : Type*} [Fintype V] [DecidableEq V]

def profile (q t : ℕ) : ℝ :=
  if h : ∃ p : Finset V × Finset V,
      p.1.card = 2 ∧ p.2.card = 2 ∧ (p.1 ∩ p.2).card = t then
    SliceGramOrbit.gram q h.choose.1 h.choose.2
  else 0

theorem gram_eq_profile (q : ℕ) (P Q : Finset V)
    (hP : P.card = 2) (hQ : Q.card = 2) :
    SliceGramOrbit.gram q P Q = profile (V := V) q (P ∩ Q).card := by
  unfold profile
  split_ifs with h
  · exact SliceGramOrbit.gram_eq_of_intersection q P Q h.choose.1 h.choose.2
      hP hQ h.choose_spec.1 h.choose_spec.2.1 h.choose_spec.2.2.symm
  · exact False.elim (h ⟨(P,Q), hP, hQ, rfl⟩)

theorem twice_column_inner (q : ℕ) (hq : q ≤ Fintype.card V)
    (hp : 0 < SliceMoments.equalMean (Finset.univ : Finset V) q)
    (hp1 : SliceMoments.equalMean (Finset.univ : Finset V) q < 1)
    (i j k l : V) (hij : i ≠ j) (hkl : k ≠ l) :
    2 * ⟪SliceNormalized.column q i j, SliceNormalized.column q k l⟫ =
      SliceGramOrbit.gram q {i,j} {k,l} /
        (SliceMoments.equalMean (Finset.univ : Finset V) q *
          (1 - SliceMoments.equalMean (Finset.univ : Finset V) q)) := by
  rw [SliceNormalized.column_inner q hq hp hp1 i j k l hij hkl]
  simp only [SliceGramOrbit.gram, SliceGramOrbit.centeredPair_pair q i j hij,
    SliceGramOrbit.centeredPair_pair q k l hkl]
  have hp0 := hp.ne'
  have hc : 1 - SliceMoments.equalMean (Finset.univ : Finset V) q ≠ 0 := by linarith
  field_simp

theorem gram_of_intersection_two (q : ℕ) (hq : q ≤ Fintype.card V)
    (i j k l : V) (hij : i ≠ j) (hkl : k ≠ l)
    (hI : (({i,j} : Finset V) ∩ {k,l}).card = 2) :
    SliceGramOrbit.gram q {i,j} {k,l} =
      SliceMoments.equalMean (Finset.univ : Finset V) q *
        (1 - SliceMoments.equalMean (Finset.univ : Finset V) q) := by
  have hg := SliceGramOrbit.gram_eq_of_intersection q {i,j} {k,l} {i,j} {i,j}
    (by simp [hij]) (by simp [hkl]) (by simp [hij]) (by simp [hij])
    (by simpa [hij] using hI)
  rw [hg]
  simp only [SliceGramOrbit.gram, SliceGramOrbit.centeredPair_pair q i j hij,
    ← pow_two]
  exact SliceMoments.average_centeredEqual_sq Finset.univ q (by simpa using hq)
    i j (Finset.mem_univ i) (Finset.mem_univ j) hij

theorem exists_normalized_orbit_entries (q : ℕ) (hq : q ≤ Fintype.card V)
    (hp : 0 < SliceMoments.equalMean (Finset.univ : Finset V) q)
    (hp1 : SliceMoments.equalMean (Finset.univ : Finset V) q < 1) :
    ∃ b d : ℝ, ∀ i j : V, i ≠ j → ∀ k l : V, k ≠ l →
      2 * ⟪SliceNormalized.column q i j, SliceNormalized.column q k l⟫ =
        SliceCoefficients.orbitKernel 1 b d i j k l := by
  let v := SliceMoments.equalMean (Finset.univ : Finset V) q *
    (1 - SliceMoments.equalMean (Finset.univ : Finset V) q)
  have hv : v ≠ 0 := mul_ne_zero hp.ne' (by linarith)
  refine ⟨profile (V := V) q 1 / v, profile (V := V) q 0 / v, ?_⟩
  intro i j hij k l hkl
  rw [twice_column_inner q hq hp hp1 i j k l hij hkl,
    SliceCoefficients.orbitKernel_eq_intersection_card _ _ _ i j k l hij hkl]
  change SliceGramOrbit.gram q {i,j} {k,l} / v = _
  by_cases h2 : (({i,j} : Finset V) ∩ {k,l}).card = 2
  · rw [ite_eq_left h2, gram_of_intersection_two q hq i j k l hij hkl h2]
    exact div_self hv
  · rw [ite_eq_right h2, gram_eq_profile q {i,j} {k,l} (by simp [hij]) (by simp [hkl])]
    by_cases h1 : (({i,j} : Finset V) ∩ {k,l}).card = 1
    · rw [ite_eq_left h1, h1]
    · rw [ite_eq_right h1]
      have hle : (({i,j} : Finset V) ∩ {k,l}).card ≤ 2 := by
        calc
          _ ≤ ({i,j} : Finset V).card := Finset.card_le_card Finset.inter_subset_left
          _ = 2 := by simp [hij]
      have h0 : (({i,j} : Finset V) ∩ {k,l}).card = 0 := by omega
      rw [h0]

end Problem315.SliceGramProfile

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SliceGramProfile.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SliceSynthesisAction.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceSynthesis
open SliceCoefficients

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem gram_action_of_orbit_entries (z : V → V → E) (a b d : ℝ)
    (hzdiag : ∀ i, z i i = 0)
    (hgram : ∀ i j, i ≠ j → ∀ k l, k ≠ l →
      2 * ⟪z i j,z k l⟫ = orbitKernel a b d i j k l)
    (c : V → V → ℝ) (hsym : ∀ i j, c i j = c j i)
    (hdiag : ∀ i, c i i = 0) :
    LinearMap.adjoint (synthesis z) (synthesis z (ofMatrix c)) =
      ofMatrix (intersectionAction a b d c) := by
  ext p
  rcases p with ⟨i,j⟩
  rw [gram_synthesis_apply, ofMatrix_apply]
  simp only [ofMatrix_apply]
  by_cases hij : i=j
  · subst j
    simp [hzdiag, intersectionAction]
  · have h := half_sum_kernel_eq_intersectionAction a b d
      (fun k l => 2 * ⟪z i j,z k l⟫) c hsym hdiag hij (hgram i j hij)
    have hsum : (∑ k, ∑ l, (2 * ⟪z i j,z k l⟫) * c k l) =
        2 * (∑ k, ∑ l, c k l * ⟪z i j,z k l⟫) := by
      simp_rw [show ∀ k l, (2 * ⟪z i j,z k l⟫) * c k l =
        2 * (c k l * ⟪z i j,z k l⟫) by intros; ring]
      simp only [← Finset.mul_sum]
    rw [hsum] at h
    linarith

theorem gram_linear_of_orbit_entries (z : V → V → E) (a b d : ℝ)
    (hzdiag : ∀ i, z i i = 0)
    (hgram : ∀ i j, i ≠ j → ∀ k l, k ≠ l →
      2 * ⟪z i j,z k l⟫ = orbitKernel a b d i j k l)
    (u : V → ℝ) (hu : (∑ i, u i) = 0) :
    LinearMap.adjoint (synthesis z) (synthesis z (ofMatrix (linearPair u))) =
      (a + ((Fintype.card V : ℝ)-4)*b - ((Fintype.card V : ℝ)-3)*d) •
        ofMatrix (linearPair u) := by
  rw [gram_action_of_orbit_entries z a b d hzdiag hgram _
    (linearPair_symmetric u) (linearPair_diag u)]
  ext p
  exact intersectionAction_linearPair a b d u hu p.1 p.2

theorem gram_rowZero_of_orbit_entries (z : V → V → E) (a b d : ℝ)
    (hzdiag : ∀ i, z i i = 0)
    (hgram : ∀ i j, i ≠ j → ∀ k l, k ≠ l →
      2 * ⟪z i j,z k l⟫ = orbitKernel a b d i j k l)
    (c : V → V → ℝ) (hsym : ∀ i j, c i j = c j i)
    (hdiag : ∀ i, c i i = 0) (hrow : ∀ i, rowSum c i = 0) :
    LinearMap.adjoint (synthesis z) (synthesis z (ofMatrix c)) =
      (a-2*b+d) • ofMatrix c := by
  rw [gram_action_of_orbit_entries z a b d hzdiag hgram c hsym hdiag]
  ext p
  exact intersectionAction_rowZero a b d c hsym hdiag hrow p.1 p.2

end Problem315.SliceSynthesis

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SliceSynthesisAction.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SliceGramScalars.lean -/
section

namespace OAI

namespace Problem315.SliceGram

theorem eigenvalue_relation (N b d mu₁ mu₂ : ℝ)
    (hconstant : 1 + 2 * (N - 2) * b + ((N - 2) * (N - 3) / 2) * d = 0)
    (hmu₁ : mu₁ = 1 + (N - 4) * b - (N - 3) * d)
    (hmu₂ : mu₂ = 1 - 2 * b + d) :
    N * (N - 3) * mu₂ = (N - 1) * (N - 2 * mu₁) := by
  rw [hmu₁, hmu₂]
  nlinarith [hconstant]

theorem degree_two_eigenvalue_le (N b d mu₁ mu₂ : ℝ) (hN : 4 ≤ N)
    (hconstant : 1 + 2 * (N - 2) * b + ((N - 2) * (N - 3) / 2) * d = 0)
    (hmu₁ : mu₁ = 1 + (N - 4) * b - (N - 3) * d)
    (hmu₂ : mu₂ = 1 - 2 * b + d) (hpos : 0 ≤ mu₁) :
    mu₂ ≤ (N - 1) / (N - 3) := by
  have hrel := eigenvalue_relation N b d mu₁ mu₂ hconstant hmu₁ hmu₂
  have hfactor : 0 < N * (N - 3) := mul_pos (by linarith) (by linarith)
  apply (mul_le_mul_iff_right₀ hfactor).mp
  have hden : N - 3 ≠ 0 := by linarith
  calc
    N * (N - 3) * mu₂ = (N - 1) * (N - 2 * mu₁) := hrel
    _ ≤ (N - 1) * N := by nlinarith
    _ = N * (N - 3) * ((N - 1) / (N - 3)) := by field_simp

theorem degree_two_eigenvalue_le_johnson (N b d mu₁ mu₂ : ℝ) (hN : 4 ≤ N)
    (hconstant : 1 + 2 * (N - 2) * b + ((N - 2) * (N - 3) / 2) * d = 0)
    (hmu₁ : mu₁ = 1 + (N - 4) * b - (N - 3) * d)
    (hmu₂ : mu₂ = 1 - 2 * b + d) (hpos : 0 ≤ mu₁) :
    mu₂ ≤ N - 1 := by
  apply (degree_two_eigenvalue_le N b d mu₁ mu₂ hN hconstant hmu₁ hmu₂ hpos).trans
  apply (div_le_iff₀ (by linarith : 0 < N - 3)).mpr
  nlinarith

end Problem315.SliceGram

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SliceGramScalars.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SliceGramConstant.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceCoefficients

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem constantPair_meetingSum (c : ℝ) {i j : V} (hij : i ≠ j) :
    meetingSum (constantPair c) i j = 2 * ((Fintype.card V : ℝ) - 2) * c := by
  rw [meetingSum_eq _ (constantPair_symmetric c) (constantPair_diag c) hij,
    constantPair_rowSum, constantPair_rowSum]
  simp only [constantPair, hij, ite_false]
  ring

theorem constantPair_disjointSum (c : ℝ) {i j : V} (hij : i ≠ j) :
    disjointSum (constantPair c) i j =
      (((Fintype.card V : ℝ) - 2) * ((Fintype.card V : ℝ) - 3) / 2) * c := by
  unfold disjointSum
  rw [double_outside_eq _ (constantPair_symmetric c) (constantPair_diag c) hij]
  simp only [constantPair_rowSum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    constantPair, hij, ite_false]
  ring

theorem intersectionAction_constantPair (a b d c : ℝ) (i j : V) :
    intersectionAction a b d (constantPair c) i j =
      (a + 2 * ((Fintype.card V : ℝ) - 2) * b +
        (((Fintype.card V : ℝ) - 2) * ((Fintype.card V : ℝ) - 3) / 2) * d) *
      constantPair c i j := by
  by_cases hij : i = j
  · subst j
    simp [intersectionAction]
  · simp only [intersectionAction, hij, ite_false,
      constantPair_meetingSum c hij, constantPair_disjointSum c hij,
      constantPair]
    ring

theorem constant_relation_of_intersectionAction_eq_zero [Nontrivial V] (b d : ℝ)
    (hzero : ∀ i j : V, intersectionAction 1 b d (constantPair 1) i j = 0) :
    1 + 2 * ((Fintype.card V : ℝ) - 2) * b +
      (((Fintype.card V : ℝ) - 2) * ((Fintype.card V : ℝ) - 3) / 2) * d = 0 := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne V
  have h := hzero i j
  rw [intersectionAction_constantPair] at h
  simpa [constantPair, hij] using h

theorem degree_two_bound_of_intersectionAction_eq_zero [Nontrivial V]
    (hcard : 4 ≤ Fintype.card V) (b d : ℝ)
    (hzero : ∀ i j : V, intersectionAction 1 b d (constantPair 1) i j = 0)
    (hpositive : 0 ≤ 1 + ((Fintype.card V : ℝ) - 4) * b -
      ((Fintype.card V : ℝ) - 3) * d) :
    1 - 2 * b + d ≤ (Fintype.card V : ℝ) - 1 := by
  apply Problem315.SliceGram.degree_two_eigenvalue_le_johnson
    (Fintype.card V : ℝ) b d
    (1 + ((Fintype.card V : ℝ) - 4) * b - ((Fintype.card V : ℝ) - 3) * d)
    (1 - 2 * b + d) (by exact_mod_cast hcard)
    (constant_relation_of_intersectionAction_eq_zero b d hzero) rfl rfl hpositive

end Problem315.SliceCoefficients

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SliceGramConstant.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SliceSynthesisBounds.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceSynthesis
open SliceCoefficients

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem intersectionAction_constant_zero_of_total (z : V → V → E) (b d : ℝ)
    (hzdiag : ∀ i, z i i = 0) (hztotal : (∑ i, ∑ j, z i j) = 0)
    (hgram : ∀ i j, i ≠ j → ∀ k l, k ≠ l →
      2 * ⟪z i j,z k l⟫ = orbitKernel 1 b d i j k l) :
    ∀ i j : V, intersectionAction 1 b d (constantPair 1) i j = 0 := by
  have h := gram_action_of_orbit_entries z 1 b d hzdiag hgram
    (constantPair 1) (constantPair_symmetric 1) (constantPair_diag 1)
  rw [synthesis_constant z hzdiag hztotal, map_zero] at h
  intro i j
  have he := congrArg (fun c : Coeff V => c (i,j)) h
  simpa only [ofMatrix_apply, PiLp.zero_apply] using he.symm

theorem constant_relation_of_orbit_entries [Nontrivial V]
    (z : V → V → E) (b d : ℝ)
    (hzdiag : ∀ i, z i i = 0) (hztotal : (∑ i, ∑ j, z i j) = 0)
    (hgram : ∀ i j, i ≠ j → ∀ k l, k ≠ l →
      2 * ⟪z i j,z k l⟫ = orbitKernel 1 b d i j k l) :
    1 + 2 * ((Fintype.card V : ℝ) - 2) * b +
      (((Fintype.card V : ℝ) - 2) * ((Fintype.card V : ℝ) - 3) / 2) * d = 0 := by
  exact constant_relation_of_intersectionAction_eq_zero b d
    (intersectionAction_constant_zero_of_total z b d hzdiag hztotal hgram)

theorem degree_two_bound_of_orbit_entries
    (hcard : 4 ≤ Fintype.card V) (z : V → V → E) (b d : ℝ)
    (hzdiag : ∀ i, z i i = 0) (hztotal : (∑ i, ∑ j, z i j) = 0)
    (hgram : ∀ i j, i ≠ j → ∀ k l, k ≠ l →
      2 * ⟪z i j,z k l⟫ = orbitKernel 1 b d i j k l)
    (hpositive : 0 ≤ 1 + ((Fintype.card V : ℝ) - 4) * b -
      ((Fintype.card V : ℝ) - 3) * d) :
    1 - 2 * b + d ≤ (Fintype.card V : ℝ) - 1 := by
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exact degree_two_bound_of_intersectionAction_eq_zero hcard b d
    (intersectionAction_constant_zero_of_total z b d hzdiag hztotal hgram) hpositive

end Problem315.SliceSynthesis

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SliceSynthesisBounds.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SliceOperatorComparison.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceNormalized
open SliceSynthesis SliceCoefficients

variable {V : Type*} [Fintype V] [DecidableEq V]

 theorem exists_nonzero_linear_coeff (hN : 3 ≤ Fintype.card V) :
    ∃ u : V → ℝ, (∑ i, u i) = 0 ∧ ofMatrix (linearPair u) ≠ 0 := by
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨i,j,hij⟩ := exists_pair_ne V
  let u : V → ℝ := Pi.single i 1 - Pi.single j 1
  have hu : ∑ k, u k = 0 := by simp [u, Finset.sum_sub_distrib]
  have hui : u i = 1 := by simp [u, hij]
  refine ⟨u, hu, ?_⟩
  intro hc
  have hz : rowSum (linearPair u) i = 0 := by
    unfold rowSum
    apply Finset.sum_eq_zero
    intro k _
    have hh := congrArg (fun c : Coeff V => c (i,k)) hc
    simpa only [ofMatrix_apply, PiLp.zero_apply] using hh
  rw [linearPair_rowSum u hu, hui, mul_one] at hz
  have hNR : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hN
  linarith

 theorem linear_orbit_scalar_eq (q : ℕ) (hN : 3 ≤ Fintype.card V)
    (hq0 : 0 < q) (hqN : q < Fintype.card V) (b d : ℝ)
    (hgram : ∀ i j : V, i ≠ j → ∀ k l : V, k ≠ l →
      2 * ⟪column q i j, column q k l⟫ = orbitKernel 1 b d i j k l) :
    1 + ((Fintype.card V : ℝ)-4)*b - ((Fintype.card V : ℝ)-3)*d =
      SliceImageNorm.linearGramScalar (α := V) q := by
  obtain ⟨u,hu,hc⟩ := exists_nonzero_linear_coeff (V := V) hN
  have hg := gram_linear_of_orbit_entries (column q) 1 b d
    (column_diag q) hgram u hu
  have hn := synthesis_linear_norm_sq q hN hq0 hqN u hu
  have hi := (synthesis (column q)).adjoint_inner_right
    (ofMatrix (linearPair u)) (synthesis (column q) (ofMatrix (linearPair u)))
  rw [hg, inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq] at hi
  apply mul_right_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hc))
  linarith

 theorem rowZero_eq_zero_of_card_le_three (hN : Fintype.card V ≤ 3)
    (c : V → V → ℝ) (hrow : ∀ i, rowSum c i = 0)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0) : c = 0 := by
  funext i j
  by_cases hij : i = j
  · subst j
    exact hdiag i
  · have hout : ∀ k ∈ outside i j, ∀ l ∈ outside i j, k = l := by
      intro k hk l hl
      by_contra hkl
      have hk' : k ≠ j ∧ k ≠ i := by simpa [outside] using hk
      have hl' : l ≠ j ∧ l ≠ i := by simpa [outside] using hl
      have hc := Finset.card_le_card (Finset.subset_univ ({i,j,k,l} : Finset V))
      have hfour : ({i,j,k,l} : Finset V).card = 4 := by
        simp [hij, hkl, Ne.symm hk'.1,
          Ne.symm hk'.2, Ne.symm hl'.1, Ne.symm hl'.2]
      rw [hfour, Finset.card_univ] at hc
      omega
    have hz : disjointSum c i j = 0 := by
      unfold disjointSum
      have hs : (∑ k ∈ outside i j, ∑ l ∈ outside i j, c k l) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        apply Finset.sum_eq_zero
        intro l hl
        rw [hout k hk l hl]
        exact hdiag l
      rw [hs, zero_div]
    rw [rowZero_disjointSum c hsym hdiag hrow hij] at hz
    exact hz

 theorem column_eq_zero_of_boundary (q : ℕ) (hq : q ≤ Fintype.card V)
    (hb : q = 0 ∨ q = Fintype.card V ∨ Fintype.card V ≤ 2) (i j : V) :
    column q i j = 0 := by
  by_cases hij : i = j
  · subst j; exact column_diag q i
  · have hr : raw q i j = 0 := by
      ext S
      change (if i = j then 0 else SliceMoments.centeredEqual Finset.univ q i j S.val) = 0
      rw [ite_eq_right hij]
      exact SliceMoments.centeredEqual_eq_zero_of_boundary Finset.univ q
        (by simpa using hq) i j (Finset.mem_univ i) (Finset.mem_univ j) hij
        (by simpa using hb) S.val S.property
    simp [column, hr]

 theorem operator_comparison_nontrivial (q : ℕ) (hN : 3 ≤ Fintype.card V)
    (hq0 : 0 < q) (hqN : q < Fintype.card V) (f : Space V q) :
    ⟪f, synthesis (column q) (LinearMap.adjoint (synthesis (column q)) f)⟫ ≤
      ⟪f, SliceEuclideanGenerator.generator q f⟫ := by
  have hp := SliceImageNorm.equalMean_pos hN q
  have hp1 := SliceImageNorm.equalMean_lt_one (by omega : 2 ≤ Fintype.card V) q hq0 hqN
  obtain ⟨b,d,hgram⟩ := SliceGramProfile.exists_normalized_orbit_entries
    (V := V) q hqN.le hp hp1
  let μ₁ : ℝ := 1 + ((Fintype.card V : ℝ)-4)*b - ((Fintype.card V : ℝ)-3)*d
  let μ₂ : ℝ := if 4 ≤ Fintype.card V then 1-2*b+d else 0
  have hμ₁ : μ₁ = SliceImageNorm.linearGramScalar (α := V) q :=
    linear_orbit_scalar_eq q hN hq0 hqN b d hgram
  have hμ₁pos : 0 ≤ μ₁ := by
    rw [hμ₁]
    unfold SliceImageNorm.linearGramScalar
    have hNR : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hN
    apply div_nonneg (sq_nonneg _)
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hp.le
  have hb₁ : μ₁ ≤ (Fintype.card V : ℝ)/2 := by
    rw [hμ₁]
    exact SliceImageNorm.linearGramScalar_le hN q hq0 hqN
  have hb₂ : μ₂ ≤ (Fintype.card V : ℝ)-1 := by
    dsimp only [μ₂]
    split_ifs with h4
    · exact degree_two_bound_of_orbit_entries h4 (column q) b d
        (column_diag q) (column_total q (by omega)) hgram hμ₁pos
    · have hNR : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hN
      linarith
  refine Analytic.gram_comparison_of_two_blocks_without_signs
    (E := Space V q) (F := Coeff V) (synthesis (column q)) (SliceEuclideanGenerator.generator q)
    (SliceEuclideanGenerator.generator_symmetric q)
    (SliceEuclideanGenerator.generator_positive q) μ₁ μ₂
    ((Fintype.card V : ℝ)/2) ((Fintype.card V : ℝ)-1) hb₁ hb₂ ?_ f
  intro c
  obtain ⟨u,v,hu,hvrow,hvsym,hvdiag,hdec,horth⟩ :=
    exists_synthesis_decomposition hN (column q) (column_symmetric q)
      (column_diag q) (column_total q (by omega)) c
  refine ⟨ofMatrix (linearPair u),ofMatrix v,hdec,horth,?_,?_,?_,?_⟩
  · exact gram_linear_of_orbit_entries (column q) 1 b d (column_diag q) hgram u hu
  · by_cases h4 : 4 ≤ Fintype.card V
    · simpa only [μ₂, ite_eq_left h4] using gram_rowZero_of_orbit_entries
        (column q) 1 b d (column_diag q) hgram v hvsym hvdiag hvrow
    · have hv := rowZero_eq_zero_of_card_le_three (by omega) v hvrow hvsym hvdiag
      subst v
      simp [ofMatrix, synthesis, μ₂, h4]
  · exact generator_synthesis_linear q u hu
  · exact generator_synthesis_rowZero q v hvrow hvsym hvdiag

 theorem operator_comparison (q : ℕ) (hq : q ≤ Fintype.card V) (f : Space V q) :
    ⟪f, synthesis (column q) (LinearMap.adjoint (synthesis (column q)) f)⟫ ≤
      ⟪f, SliceEuclideanGenerator.generator q f⟫ := by
  by_cases hb : q = 0 ∨ q = Fintype.card V ∨ Fintype.card V ≤ 2
  · have hz : synthesis (column (V := V) q) = 0 := by
      ext c S
      simp [synthesis, column_eq_zero_of_boundary q hq hb]
    rw [hz]
    simpa using SliceEuclideanGenerator.generator_positive q f
  · apply operator_comparison_nontrivial
    · omega
    · omega
    · omega

end Problem315.SliceNormalized

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SliceOperatorComparison.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/FrameSynthesis.lean -/
section

namespace OAI


noncomputable section

open scoped BigOperators

namespace Problem315.FrameSynthesis

variable {ι E : Type*} [Fintype ι] [sectionDecidableEqι : DecidableEq ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

def synthesis (z : ι → E) : EuclideanSpace ℝ ι →ₗ[ℝ] E where
  toFun c := ∑ i, c i • z i
  map_add' c d := by
    simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

include sectionDecidableEqι in
@[simp] theorem synthesis_apply (z : ι → E) (c : EuclideanSpace ℝ ι) :
    synthesis z c = ∑ i, c i • z i := by
  have retainedsectionDecidableEqι := sectionDecidableEqι
  exact rfl

@[simp] theorem synthesis_single (z : ι → E) (i : ι) (a : ℝ) :
    synthesis z (EuclideanSpace.single i a) = a • z i := by
  classical
  simp [synthesis, EuclideanSpace.single]

section Adjoint
variable [FiniteDimensional ℝ E]

@[simp] theorem adjoint_synthesis_apply (z : ι → E) (f : E) (i : ι) :
    (synthesis z).adjoint f i = ⟪z i, f⟫ := by
  classical
  have h := (synthesis z).adjoint_inner_right (EuclideanSpace.single i 1) f
  simpa [EuclideanSpace.inner_single_left] using h

theorem synthesis_adjoint_apply (z : ι → E) (f : E) :
    synthesis z ((synthesis z).adjoint f) = ∑ i, ⟪z i, f⟫ • z i := by
  simp only [synthesis_apply, adjoint_synthesis_apply]

theorem gram_apply (z : ι → E) (c : EuclideanSpace ℝ ι) (i : ι) :
    (synthesis z).adjoint (synthesis z c) i = ∑ j, c j * ⟪z i, z j⟫ := by
  rw [adjoint_synthesis_apply, synthesis_apply, inner_sum]
  simp only [inner_smul_right]

theorem frame_energy (z : ι → E) (f : E) :
    ⟪f, synthesis z ((synthesis z).adjoint f)⟫ = ∑ i, ⟪z i, f⟫ ^ 2 := by
  rw [synthesis_adjoint_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_smul_right, real_inner_comm f (z i)]
  ring

end Adjoint

def normalized (z : E) : E := ‖z‖⁻¹ • z

theorem normalized_rank_one_eq_projection (z f : E) :
    ⟪normalized z, f⟫ • normalized z = (ℝ ∙ z).starProjection f := by
  rw [Submodule.starProjection_singleton ℝ]
  simp only [normalized, inner_smul_left, RCLike.conj_to_real, smul_smul]
  congr 1
  change (‖z‖⁻¹ * ⟪z, f⟫) * ‖z‖⁻¹ = ⟪z, f⟫ / ‖z‖ ^ 2
  ring

theorem normalized_inner (z w : E) :
    ⟪normalized z, normalized w⟫ = ⟪z, w⟫ / (‖z‖ * ‖w‖) := by
  simp only [normalized, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  ring

variable [FiniteDimensional ℝ E]

theorem normalized_frame_apply (z : ι → E) (f : E) :
    synthesis (fun i => normalized (z i))
      ((synthesis (fun i => normalized (z i))).adjoint f) =
        ∑ i, (ℝ ∙ z i).starProjection f := by
  rw [synthesis_adjoint_apply]
  simp_rw [normalized_rank_one_eq_projection]

theorem normalized_frame_eq_sum_projection (z : ι → E) :
    (synthesis (fun i => normalized (z i))).comp
        (synthesis (fun i => normalized (z i))).adjoint =
      ∑ i, ((ℝ ∙ z i).starProjection : E →L[ℝ] E).toLinearMap := by
  ext f
  simpa using normalized_frame_apply z f

theorem normalized_gram_apply (z : ι → E) (c : EuclideanSpace ℝ ι) (i : ι) :
    (synthesis (fun j => normalized (z j))).adjoint
        (synthesis (fun j => normalized (z j)) c) i =
      ∑ j, c j * (⟪z i, z j⟫ / (‖z i‖ * ‖z j‖)) := by
  rw [gram_apply]
  simp_rw [normalized_inner]

theorem normalized_frame_energy (z : ι → E) (f : E) :
    ⟪f, synthesis (fun i => normalized (z i))
      ((synthesis (fun i => normalized (z i))).adjoint f)⟫ =
        ∑ i, ‖(ℝ ∙ z i).starProjection f‖ ^ 2 := by
  rw [normalized_frame_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have h := (ℝ ∙ z i).re_inner_starProjection_eq_normSq f
  simpa only [RCLike.re_to_real, real_inner_comm,
    Submodule.starProjection_apply, Submodule.norm_coe] using h

theorem scaled_frame_apply (a : ℝ) (z : ι → E) (f : E) :
    synthesis (fun i => a • z i) ((synthesis (fun i => a • z i)).adjoint f) =
      a ^ 2 • synthesis z ((synthesis z).adjoint f) := by
  rw [synthesis_adjoint_apply, synthesis_adjoint_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [inner_smul_left, RCLike.conj_to_real, smul_smul]
  congr 1
  ring

theorem scaled_normalized_frame_apply (a : ℝ) (z : ι → E) (f : E) :
    synthesis (fun i => a • normalized (z i))
      ((synthesis (fun i => a • normalized (z i))).adjoint f) =
        a ^ 2 • ∑ i, (ℝ ∙ z i).starProjection f := by
  rw [scaled_frame_apply, normalized_frame_apply]

theorem scaled_normalized_frame_energy (a : ℝ) (z : ι → E) (f : E) :
    ⟪f, synthesis (fun i => a • normalized (z i))
      ((synthesis (fun i => a • normalized (z i))).adjoint f)⟫ =
        a ^ 2 * ∑ i, ‖(ℝ ∙ z i).starProjection f‖ ^ 2 := by
  rw [scaled_frame_apply, inner_smul_right, normalized_frame_energy]

theorem half_normalized_frame_energy (z : ι → E) (f : E) :
    ⟪f, synthesis (fun i => (Real.sqrt 2)⁻¹ • normalized (z i))
      ((synthesis (fun i => (Real.sqrt 2)⁻¹ • normalized (z i))).adjoint f)⟫ =
        (1 / 2 : ℝ) * ∑ i, ‖(ℝ ∙ z i).starProjection f‖ ^ 2 := by
  rw [scaled_normalized_frame_energy]
  have hsq : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [hsq]

theorem frame_apply_of_common_norm_sq (z : ι → E) (a : ℝ)
    (hz : ∀ i, z i = 0 ∨ ‖z i‖ ^ 2 = a) (f : E) :
    synthesis z ((synthesis z).adjoint f) = a • ∑ i, (ℝ ∙ z i).starProjection f := by
  rw [synthesis_adjoint_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rcases hz i with hzero | hnorm
  · simp [hzero]
  · rw [← Submodule.smul_starProjection_singleton ℝ f]
    change ‖z i‖ ^ 2 • (ℝ ∙ z i).starProjection f = _
    rw [hnorm]

theorem frame_energy_of_common_norm_sq (z : ι → E) (a : ℝ)
    (hz : ∀ i, z i = 0 ∨ ‖z i‖ ^ 2 = a) (f : E) :
    ⟪f, synthesis z ((synthesis z).adjoint f)⟫ =
      a * ∑ i, ‖(ℝ ∙ z i).starProjection f‖ ^ 2 := by
  rw [frame_apply_of_common_norm_sq z a hz, inner_smul_right, inner_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have h := (ℝ ∙ z i).re_inner_starProjection_eq_normSq f
  simpa only [RCLike.re_to_real, real_inner_comm,
    Submodule.starProjection_apply, Submodule.norm_coe] using h


end Problem315.FrameSynthesis

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/FrameSynthesis.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SliceFrameProjection.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceSynthesis

variable {V E : Type*} [Fintype V] [sectionDecidableEqV : DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

include sectionDecidableEqV in
theorem synthesis_eq_frame (z : V → V → E) :
    synthesis z = FrameSynthesis.synthesis (fun p : V × V => z p.1 p.2) := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  apply LinearMap.ext
  intro c
  simp [synthesis, FrameSynthesis.synthesis, Fintype.sum_prod_type]

variable [FiniteDimensional ℝ E]

theorem half_projection_frame_apply (z : V → V → E)
    (hzdiag : ∀ i, z i i = 0)
    (hznorm : ∀ i j, i ≠ j → ‖z i j‖ ^ 2 = (1 / 2 : ℝ)) (x : E) :
    synthesis z ((synthesis z).adjoint x) =
      (1 / 2 : ℝ) • ∑ i, ∑ j, (ℝ ∙ z i j).starProjection x := by
  rw [synthesis_eq_frame]
  have hz (p : V × V) : z p.1 p.2 = 0 ∨ ‖z p.1 p.2‖ ^ 2 = (1 / 2 : ℝ) := by
    by_cases h : p.1 = p.2
    · exact Or.inl (by rw [h, hzdiag])
    · exact Or.inr (hznorm p.1 p.2 h)
  simpa only [Fintype.sum_prod_type] using
    FrameSynthesis.frame_apply_of_common_norm_sq
      (fun p : V × V => z p.1 p.2) (1 / 2) hz x

theorem half_projection_frame_energy (z : V → V → E)
    (hzdiag : ∀ i, z i i = 0)
    (hznorm : ∀ i j, i ≠ j → ‖z i j‖ ^ 2 = (1 / 2 : ℝ)) (x : E) :
    ⟪x, synthesis z ((synthesis z).adjoint x)⟫ =
      (1 / 2 : ℝ) * ∑ i, ∑ j, ‖(ℝ ∙ z i j).starProjection x‖ ^ 2 := by
  rw [synthesis_eq_frame]
  have hz (p : V × V) : z p.1 p.2 = 0 ∨ ‖z p.1 p.2‖ ^ 2 = (1 / 2 : ℝ) := by
    by_cases h : p.1 = p.2
    · exact Or.inl (by rw [h, hzdiag])
    · exact Or.inr (hznorm p.1 p.2 h)
  simpa only [Fintype.sum_prod_type] using
    FrameSynthesis.frame_energy_of_common_norm_sq
      (fun p : V × V => z p.1 p.2) (1 / 2) hz x

end Problem315.SliceSynthesis

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SliceFrameProjection.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SliceProjectionComparison.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceNormalized
open SliceSynthesis

variable {V : Type*} [Fintype V] [DecidableEq V]

 theorem raw_eq_zero_of_boundary (q : ℕ) (hq : q ≤ Fintype.card V)
    (hb : q = 0 ∨ q = Fintype.card V ∨ Fintype.card V ≤ 2) (i j : V) :
    raw q i j = 0 := by
  by_cases hij : i = j
  · subst j; exact raw_diag q i
  · ext S
    change (if i = j then 0 else SliceMoments.centeredEqual Finset.univ q i j S.val) = 0
    rw [ite_eq_right hij]
    exact SliceMoments.centeredEqual_eq_zero_of_boundary Finset.univ q
      (by simpa using hq) i j (Finset.mem_univ i) (Finset.mem_univ j) hij
      (by simpa using hb) S.val S.property

 theorem denominator_pos (q : ℕ) (hN : 3 ≤ Fintype.card V)
    (hq0 : 0 < q) (hqN : q < Fintype.card V) : 0 < denominator V q := by
  apply Real.sqrt_pos.2
  have hc : (0 : ℝ) < Nat.choose (Fintype.card V) q := by
    exact_mod_cast Nat.choose_pos hqN.le
  have hp := SliceImageNorm.equalMean_pos hN q
  have hp1 := SliceImageNorm.equalMean_lt_one (by omega : 2 ≤ Fintype.card V) q hq0 hqN
  exact mul_pos (mul_pos (mul_pos (by norm_num) hc) hp) (sub_pos.mpr hp1)

 theorem column_span_eq_raw_span (q : ℕ) (hq : q ≤ Fintype.card V) (i j : V) :
    (ℝ ∙ column q i j) = (ℝ ∙ raw q i j) := by
  by_cases hb : q = 0 ∨ q = Fintype.card V ∨ Fintype.card V ≤ 2
  · rw [column_eq_zero_of_boundary q hq hb, raw_eq_zero_of_boundary q hq hb]
  · unfold column
    apply Submodule.span_singleton_smul_eq
    exact isUnit_iff_ne_zero.mpr (inv_ne_zero (denominator_pos q (by omega)
      (by omega) (by omega)).ne')

 theorem column_zero_or_norm_sq (q : ℕ) (hq : q ≤ Fintype.card V) (i j : V) :
    column q i j = 0 ∨ ‖column q i j‖ ^ 2 = (1/2 : ℝ) := by
  by_cases hij : i = j
  · subst j; exact Or.inl (column_diag q i)
  by_cases hb : q = 0 ∨ q = Fintype.card V ∨ Fintype.card V ≤ 2
  · exact Or.inl (column_eq_zero_of_boundary q hq hb i j)
  · right
    exact column_norm_sq q hq (SliceImageNorm.equalMean_pos (by omega) q)
      (SliceImageNorm.equalMean_lt_one (by omega) q (by omega) (by omega)) i j hij

 theorem raw_projection_frame_energy (q : ℕ) (hq : q ≤ Fintype.card V)
    (f : Space V q) :
    ⟪f, synthesis (column q) (LinearMap.adjoint (synthesis (column q)) f)⟫ =
      (1/2 : ℝ) * ∑ i, ∑ j, ‖(ℝ ∙ raw q i j).starProjection f‖ ^ 2 := by
  rw [synthesis_eq_frame]
  have h := FrameSynthesis.frame_energy_of_common_norm_sq
    (fun p : V × V => column q p.1 p.2) (1/2)
    (fun p => column_zero_or_norm_sq q hq p.1 p.2) f
  simpa only [Fintype.sum_prod_type, column_span_eq_raw_span q hq] using h

 theorem projection_comparison (q : ℕ) (hq : q ≤ Fintype.card V) (f : Space V q) :
    (1/2 : ℝ) * ∑ i, ∑ j, ‖(ℝ ∙ raw q i j).starProjection f‖ ^ 2 ≤
      ⟪f, SliceEuclideanGenerator.generator q f⟫ := by
  rw [← raw_projection_frame_energy q hq f]
  exact operator_comparison q hq f

 theorem projection_energy_le_swap_energy (q : ℕ) (hq : q ≤ Fintype.card V)
    (f : Space V q) :
    (1/2 : ℝ) * ∑ i, ∑ j, ‖(ℝ ∙ raw q i j).starProjection f‖ ^ 2 ≤
      (1/8 : ℝ) * ∑ i, ∑ j,
        ‖f - SliceEuclideanGenerator.moveOperator q i j f‖ ^ 2 := by
  rw [← SliceEuclideanGenerator.generator_energy]
  exact projection_comparison q hq f

end Problem315.SliceNormalized

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SliceProjectionComparison.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SliceReindexedComparison.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceNormalized

variable {V Ω : Type*} [Fintype V] [sectionDecidableEqV : DecidableEq V] [sectionFintypeΩ : Fintype Ω]

def pullback {q : ℕ} (e : Ω ≃ State V q) :
    Space V q ≃ₗᵢ[ℝ] EuclideanSpace ℝ Ω :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm

include sectionDecidableEqV in
@[simp] theorem pullback_apply {q : ℕ} (e : Ω ≃ State V q)
    (f : Space V q) (ω : Ω) : pullback e f ω = f (e ω) := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  exact rfl

def reindexedRaw {q : ℕ} (e : Ω ≃ State V q) (i j : V) :
    EuclideanSpace ℝ Ω := pullback e (raw q i j)

@[simp] theorem reindexedRaw_apply {q : ℕ} (e : Ω ≃ State V q)
    (i j : V) (ω : Ω) :
    reindexedRaw e i j ω = if i = j then 0 else
      SliceMoments.centeredEqual Finset.univ q i j (e ω).val := rfl

def reindexedMove {q : ℕ} (e : Ω ≃ State V q) (i j : V)
    (f : EuclideanSpace ℝ Ω) : EuclideanSpace ℝ Ω :=
  WithLp.toLp 2 (fun ω => f (e.symm (SliceEuclideanGenerator.swapState q i j (e ω))))

include sectionFintypeΩ in
@[simp] theorem reindexedMove_apply {q : ℕ} (e : Ω ≃ State V q)
    (i j : V) (f : EuclideanSpace ℝ Ω) (ω : Ω) :
    reindexedMove e i j f ω =
      f (e.symm (SliceEuclideanGenerator.swapState q i j (e ω))) := by
  have retainedsectionFintypeΩ := sectionFintypeΩ
  exact rfl

 theorem pullback_move {q : ℕ} (e : Ω ≃ State V q) (i j : V) (f : Space V q) :
    pullback e (SliceEuclideanGenerator.moveOperator q i j f) =
      reindexedMove e i j (pullback e f) := by
  ext ω
  simp

include sectionDecidableEqV in
 theorem norm_projection_pullback {q : ℕ} (e : Ω ≃ State V q)
    (z f : Space V q) :
    ‖(ℝ ∙ pullback e z).starProjection (pullback e f)‖ =
      ‖(ℝ ∙ z).starProjection f‖ := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  rw [Submodule.starProjection_singleton, Submodule.starProjection_singleton]
  simp only [norm_smul, (pullback e).inner_map_map, (pullback e).norm_map]

 theorem reindexed_projection_energy_le_swap_energy {q : ℕ}
    (e : Ω ≃ State V q) (hq : q ≤ Fintype.card V) (f : EuclideanSpace ℝ Ω) :
    (1/2 : ℝ) * ∑ i, ∑ j, ‖(ℝ ∙ reindexedRaw e i j).starProjection f‖ ^ 2 ≤
      (1/8 : ℝ) * ∑ i, ∑ j, ‖f - reindexedMove e i j f‖ ^ 2 := by
  let g : Space V q := (pullback e).symm f
  have hfg : pullback e g = f := (pullback e).apply_symm_apply f
  have hp (i j : V) : ‖(ℝ ∙ reindexedRaw e i j).starProjection f‖ ^ 2 =
      ‖(ℝ ∙ raw q i j).starProjection g‖ ^ 2 := by
    rw [← hfg]
    exact congrArg (fun t : ℝ => t^2) (norm_projection_pullback e (raw q i j) g)
  have hm (i j : V) : ‖f - reindexedMove e i j f‖ ^ 2 =
      ‖g - SliceEuclideanGenerator.moveOperator q i j g‖ ^ 2 := by
    rw [← hfg, ← pullback_move, ← map_sub, (pullback e).norm_map]
  simp_rw [hp, hm]
  exact projection_energy_le_swap_energy q hq g

 theorem reindexed_projection_energy_le_swap_sum {q : ℕ}
    (e : Ω ≃ State V q) (hq : q ≤ Fintype.card V) (f : EuclideanSpace ℝ Ω) :
    (1/2 : ℝ) * ∑ i, ∑ j, ‖(ℝ ∙ reindexedRaw e i j).starProjection f‖ ^ 2 ≤
      (1/8 : ℝ) * ∑ i, ∑ j, ∑ ω : Ω,
        (f ω - f (e.symm (SliceEuclideanGenerator.swapState q i j (e ω)))) ^ 2 := by
  have h := reindexed_projection_energy_le_swap_energy e hq f
  simpa only [EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply, reindexedMove_apply] using h

end Problem315.SliceNormalized

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SliceReindexedComparison.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SliceCardEncoding.lean -/
section

namespace OAI

noncomputable section

namespace Problem315.SliceNormalized

variable {V Ω : Type*} [Fintype V] [sectionDecidableEqV : DecidableEq V] [sectionFintypeΩ : Fintype Ω]

def cardSliceEquiv (q : ℕ) : State V q ≃ SlicePermutationAction.Slice V q where
  toFun S := ⟨S.val, (Finset.mem_powersetCard.mp S.property).2⟩
  invFun S := ⟨S.val, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, S.property⟩⟩
  left_inv S := by apply Subtype.ext; rfl
  right_inv S := by apply Subtype.ext; rfl

include sectionDecidableEqV in
@[simp] theorem cardSliceEquiv_val (q : ℕ) (S : State V q) :
    (cardSliceEquiv q S).val = S.val := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  exact rfl

include sectionDecidableEqV in
@[simp] theorem cardSliceEquiv_symm_val (q : ℕ) (S : SlicePermutationAction.Slice V q) :
    ((cardSliceEquiv q).symm S).val = S.val := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  exact rfl

 theorem cardSliceEquiv_relabel (q : ℕ) (σ : Equiv.Perm V) (S : State V q) :
    cardSliceEquiv q (SliceEuclideanGenerator.relabel q σ S) =
      SlicePermutationAction.relabel σ (cardSliceEquiv q S) := by
  apply Subtype.ext
  simp [SlicePermutationAction.relabel, Finset.map_eq_image]

 theorem cardSliceEquiv_swap (q : ℕ) (i j : V) (S : State V q) :
    cardSliceEquiv q (SliceEuclideanGenerator.swapState q i j S) =
      SlicePermutationAction.relabel (Equiv.swap i j) (cardSliceEquiv q S) :=
  cardSliceEquiv_relabel q (Equiv.swap i j) S

include sectionFintypeΩ in
 theorem conjugated_swap_cardSlice {q : ℕ} (e : Ω ≃ SlicePermutationAction.Slice V q)
    (i j : V) (ω : Ω) :
    (e.trans (cardSliceEquiv q).symm).symm
      (SliceEuclideanGenerator.swapState q i j ((e.trans (cardSliceEquiv q).symm) ω)) =
      e.symm (SlicePermutationAction.relabel (Equiv.swap i j) (e ω)) := by
  have retainedsectionFintypeΩ := sectionFintypeΩ
  change e.symm (cardSliceEquiv q (SliceEuclideanGenerator.swapState q i j
    ((cardSliceEquiv q).symm (e ω)))) = _
  rw [cardSliceEquiv_swap, Equiv.apply_symm_apply]

end Problem315.SliceNormalized

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SliceCardEncoding.lean -/
