import AnalyticEncoding

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/EnergyTransfer.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.EnergyTransfer

theorem norm_sq_le_of_intertwining_energy_bound
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (A : E →ₗ[ℝ] F) (J : E →ₗ[ℝ] E) (K : F →ₗ[ℝ] F)
    (hJ : ∀ x : E, x ≠ 0 → 0 < ⟪x, J x⟫)
    (hinter : ∀ x : E, K (A x) = A (J x))
    (c : ℝ) (henergy : ∀ x : E, ⟪A x, K (A x)⟫ ≤ c * ⟪x, J x⟫)
    (x : E) : ‖A x‖ ^ 2 ≤ c * ‖x‖ ^ 2 := by
  classical
  let B : E →ₗ[ℝ] E := A.adjoint.comp A
  have hB : B.IsSymmetric := A.isPositive_adjoint_comp_self.isSymmetric
  let b := hB.eigenvectorBasis rfl
  let ev := hB.eigenvalues rfl
  have hbe (i : Fin (Module.finrank ℝ E)) : B (b i) = ev i • b i :=
    hB.apply_eigenvectorBasis rfl i
  have hev (i : Fin (Module.finrank ℝ E)) : ev i ≤ c := by
    have he := henergy (b i)
    rw [hinter] at he
    have hid : ⟪A (b i), A (J (b i))⟫ = ⟪B (b i), J (b i)⟫ :=
      (A.adjoint_inner_left (J (b i)) (A (b i))).symm
    rw [hid, hbe, inner_smul_left] at he
    simp only [RCLike.conj_to_real] at he
    have hp : 0 < ⟪b i, J (b i)⟫ := hJ (b i) (b.toBasis.ne_zero i)
    exact (mul_le_mul_iff_left₀ hp).mp (by simpa [mul_comm] using he)
  have hnorm : ‖A x‖ ^ 2 = ⟪x, B x⟫ := by
    change ‖A x‖ ^ 2 = ⟪x, A.adjoint (A x)⟫
    rw [A.adjoint_inner_right, real_inner_self_eq_norm_sq]
  rw [hnorm, ← b.sum_sq_inner_right x, Finset.mul_sum,
    ← b.sum_inner_mul_inner x (B x)]
  apply Finset.sum_le_sum
  intro i hi
  have hcoord : ⟪b i, B x⟫ = ev i * ⟪b i, x⟫ := by
    rw [← hB (b i) x, hbe, inner_smul_left]
    simp
  rw [hcoord, real_inner_comm x (b i)]
  nlinarith [mul_le_mul_of_nonneg_right (hev i) (sq_nonneg ⟪x, b i⟫)]

theorem norm_sum_sq_le_of_invariant_energy_bound
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (V : ι → Submodule ℝ E) (J : E →ₗ[ℝ] E)
    (hinv : ∀ i x, x ∈ V i → J x ∈ V i)
    (hpos : ∀ i x, x ∈ V i → x ≠ 0 → 0 < ⟪x, J x⟫)
    (c : ℝ)
    (henergy : ∀ f : ι → E, (∀ i, f i ∈ V i) →
      ⟪∑ i, f i, J (∑ i, f i)⟫ ≤ c * ∑ i, ⟪f i, J (f i)⟫)
    (f : ι → E) (hf : ∀ i, f i ∈ V i) :
    ‖∑ i, f i‖ ^ 2 ≤ c * ∑ i, ‖f i‖ ^ 2 := by
  classical
  let D := PiLp 2 (fun i => V i)
  let A : D →ₗ[ℝ] E :=
    { toFun := fun x => ∑ i, (x i : E)
      map_add' := by intro x y; simp [D, Finset.sum_add_distrib]
      map_smul' := by intro r x; simp [D, Finset.smul_sum] }
  let L : D →ₗ[ℝ] D :=
    { toFun := fun x => WithLp.toLp 2 (fun i => ⟨J (x i), hinv i _ (x i).property⟩)
      map_add' := by intro x y; ext i; simp [D]
      map_smul' := by intro r x; ext i; simp [D] }
  have hL (x : D) (hx : x ≠ 0) : 0 < ⟪x, L x⟫ := by
    have hnonneg (i : ι) : 0 ≤ ⟪(x i : E), J (x i)⟫ := by
      by_cases hz : (x i : E) = 0
      · simp [hz]
      · exact (hpos i _ (x i).property hz).le
    have hex : ∃ i, (x i : E) ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hx
      ext i
      exact hn i
    obtain ⟨i, hi⟩ := hex
    change 0 < ∑ j, ⟪(x j : E), J (x j)⟫
    exact Finset.sum_pos' (fun j _ => hnonneg j)
      ⟨i, Finset.mem_univ i, hpos i _ (x i).property hi⟩
  have hinter (x : D) : J (A x) = A (L x) := by
    change J (∑ i, (x i : E)) = ∑ i, J (x i)
    exact map_sum J _ _
  have hEn (x : D) : ⟪A x, J (A x)⟫ ≤ c * ⟪x, L x⟫ := by
    exact henergy (fun i => (x i : E)) (fun i => (x i).property)
  have h := norm_sq_le_of_intertwining_energy_bound A L J hL hinter c hEn
    (WithLp.toLp 2 (fun i => (⟨f i, hf i⟩ : V i)))
  simpa [D, A, PiLp.norm_sq_eq_of_L2] using h

end Problem315.EnergyTransfer

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/EnergyTransfer.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PermutationGenerator.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PermutationGenerator

variable {Ω S : Type*} [Fintype Ω] [Fintype S]

def apply (τ : S → Equiv.Perm Ω) (f : Ω → ℝ) (x : Ω) : ℝ :=
  ∑ s, (f x - f (τ s x))

def operator (τ : S → Equiv.Perm Ω) :
    EuclideanSpace ℝ Ω →ₗ[ℝ] EuclideanSpace ℝ Ω where
  toFun f := WithLp.toLp 2 (apply τ f)
  map_add' f g := by
    ext x
    change (∑ s, ((f x + g x) - (f (τ s x) + g (τ s x)))) =
      (∑ s, (f x - f (τ s x))) + ∑ s, (g x - g (τ s x))
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  map_smul' c f := by
    ext x
    change (∑ s, (c * f x - c * f (τ s x))) = c * ∑ s, (f x - f (τ s x))
    simp only [mul_sub, Finset.mul_sum]

omit [Fintype Ω] in
@[simp] theorem operator_apply (τ : S → Equiv.Perm Ω)
    (f : EuclideanSpace ℝ Ω) (x : Ω) : operator τ f x = apply τ f x := rfl

theorem sum_apply (τ : S → Equiv.Perm Ω) (f : Ω → ℝ) :
    ∑ x, apply τ f x = 0 := by
  unfold apply
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro s hs
  rw [Finset.sum_sub_distrib, Equiv.sum_comp (τ s)]
  exact sub_self _

theorem inner_operator (τ : S → Equiv.Perm Ω) (f : EuclideanSpace ℝ Ω) :
    ⟪f, operator τ f⟫ = (1 / 2 : ℝ) * ∑ s, ∑ x, (f x - f (τ s x)) ^ 2 := by
  have hsingle (s : S) :
      (∑ x, f x * (f x - f (τ s x))) =
        (1 / 2 : ℝ) * ∑ x, (f x - f (τ s x)) ^ 2 := by
    have heq : (∑ x, (f (τ s x)) ^ 2) = ∑ x, (f x) ^ 2 :=
      Equiv.sum_comp (τ s) (fun x => (f x) ^ 2)
    have hexpand : (∑ x, (f x - f (τ s x)) ^ 2) =
        (∑ x, (f x) ^ 2) + (∑ x, (f (τ s x)) ^ 2) -
          2 * ∑ x, f x * f (τ s x) := by
      simp only [Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [hexpand, heq]
    simp only [mul_sub, ← pow_two, Finset.sum_sub_distrib]
    ring
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, operator_apply, apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  simpa only [Finset.mul_sum, mul_comm] using hsingle s

theorem inner_operator_nonneg (τ : S → Equiv.Perm Ω) (f : EuclideanSpace ℝ Ω) :
    0 ≤ ⟪f, operator τ f⟫ := by
  rw [inner_operator]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem inner_operator_eq_zero_iff (τ : S → Equiv.Perm Ω) (f : EuclideanSpace ℝ Ω) :
    ⟪f, operator τ f⟫ = 0 ↔ ∀ s x, f (τ s x) = f x := by
  rw [inner_operator]
  constructor
  · intro hz s x
    have hall : (∑ s, ∑ x, (f x - f (τ s x)) ^ 2) = 0 := by linarith
    have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun s _ =>
      Finset.sum_nonneg (fun x _ => sq_nonneg (f x - f (τ s x))))).mp hall s (Finset.mem_univ s)
    have hx := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
      sq_nonneg (f x - f (τ s x)))).mp hs x (Finset.mem_univ x)
    nlinarith
  · intro h
    simp [h]

theorem inner_operator_pos_of_centered [Nonempty Ω]
    (τ : S → Equiv.Perm Ω)
    (hconn : ∀ f : Ω → ℝ, (∀ s x, f (τ s x) = f x) → ∀ x y, f x = f y)
    (f : EuclideanSpace ℝ Ω) (hcenter : ∑ x, f x = 0) (hf : f ≠ 0) :
    0 < ⟪f, operator τ f⟫ := by
  have hnonneg := inner_operator_nonneg τ f
  apply lt_of_le_of_ne hnonneg
  intro he
  have hinv := (inner_operator_eq_zero_iff τ f).mp he.symm
  obtain ⟨a⟩ := ‹Nonempty Ω›
  have hc := hconn f hinv
  have hfa : f a = 0 := by
    have heq : (∑ x, f x) = (Fintype.card Ω : ℝ) * f a := by
      simp [fun x => hc x a]
    have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    rw [heq] at hcenter
    exact (mul_eq_zero.mp hcenter).resolve_left hcard
  apply hf
  ext x
  change f x = 0
  rw [hc x a, hfa]

theorem energy_sum_le_of_local_bound
    {ι : Type*} [Fintype ι] (τ : S → Equiv.Perm Ω)
    (f : ι → EuclideanSpace ℝ Ω) (c : ℝ)
    (hlocal : ∀ s x,
      (∑ i, (f i x - f i (τ s x))) ^ 2 ≤
        c * ∑ i, (f i x - f i (τ s x)) ^ 2) :
    ⟪∑ i, f i, operator τ (∑ i, f i)⟫ ≤ c * ∑ i, ⟪f i, operator τ (f i)⟫ := by
  simp_rw [inner_operator]
  have heval (x : Ω) : (∑ i, f i) x = ∑ i, f i x := by simp
  simp_rw [heval, ← Finset.sum_sub_distrib]
  calc
    (1 / 2 : ℝ) * ∑ s, ∑ x, (∑ i, (f i x - f i (τ s x))) ^ 2
        ≤ (1 / 2 : ℝ) * ∑ s, ∑ x, c * ∑ i, (f i x - f i (τ s x)) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun x _ => hlocal s x
    _ = c * ∑ i, (1 / 2 : ℝ) * ∑ s, ∑ x, (f i x - f i (τ s x)) ^ 2 := by
      simp_rw [← Finset.mul_sum]
      have heq : (∑ s, ∑ x, ∑ i, (f i x - f i (τ s x)) ^ 2) =
          ∑ i, ∑ s, ∑ x, (f i x - f i (τ s x)) ^ 2 := by
        calc
          _ = ∑ s, ∑ i, ∑ x, (f i x - f i (τ s x)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro s hs
            rw [Finset.sum_comm]
          _ = _ := Finset.sum_comm
      rw [heq]
      ring

theorem norm_sum_sq_le_of_invariant_moves [Nonempty Ω]
    {ι : Type*} [Fintype ι] (τ : S → Equiv.Perm Ω)
    (hconn : ∀ f : Ω → ℝ, (∀ s x, f (τ s x) = f x) → ∀ x y, f x = f y)
    (V : ι → Submodule ℝ (EuclideanSpace ℝ Ω))
    (hcenter : ∀ i f, f ∈ V i → ∑ x, f x = 0)
    (hinv : ∀ i f, f ∈ V i → operator τ f ∈ V i)
    (c : ℝ)
    (hlocal : ∀ f : ι → EuclideanSpace ℝ Ω, (∀ i, f i ∈ V i) → ∀ s x,
      (∑ i, (f i x - f i (τ s x))) ^ 2 ≤ c * ∑ i, (f i x - f i (τ s x)) ^ 2)
    (f : ι → EuclideanSpace ℝ Ω) (hf : ∀ i, f i ∈ V i) :
    ‖∑ i, f i‖ ^ 2 ≤ c * ∑ i, ‖f i‖ ^ 2 := by
  apply EnergyTransfer.norm_sum_sq_le_of_invariant_energy_bound V (operator τ) hinv
    (fun i g hg hne => inner_operator_pos_of_centered τ hconn g (hcenter i g hg) hne)
    c _ f hf
  intro g hg
  exact energy_sum_le_of_local_bound τ g c (hlocal g hg)

end Problem315.PermutationGenerator

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PermutationGenerator.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/FixedBlockVariance.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.FixedBlockVariance
open FixedBlock

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable (p q : Fin 3 → ℕ)

abbrev State := Partition (α := α) p × Partition (α := β) q

def relabelPerm (σ : Equiv.Perm α) : Equiv.Perm (Partition (α := α) p) where
  toFun := relabel σ
  invFun := relabel σ.symm
  left_inv c := by
    apply Subtype.ext
    funext a
    simp [relabel]
  right_inv c := by
    apply Subtype.ext
    funext a
    simp [relabel]

def move : (α × α) ⊕ (β × β) → Equiv.Perm (State (α := α) (β := β) p q)
  | Sum.inl ab => Equiv.prodCongr (relabelPerm p (Equiv.swap ab.1 ab.2)) (Equiv.refl _)
  | Sum.inr ab => Equiv.prodCongr (Equiv.refl _) (relabelPerm q (Equiv.swap ab.1 ab.2))

def key (i : Fin 3) (x : State (α := α) (β := β) p q) : Finset α × Finset β :=
  (row x.1.val i, row x.2.val i)

theorem key_move_eq (i : Fin 3) (s : (α × α) ⊕ (β × β))
    (x y : State (α := α) (β := β) p q) (h : key p q i x = key p q i y) :
    key p q i (move p q s x) = key p q i (move p q s y) := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  change row x.1.val i = row y.1.val i at h1
  change row x.2.val i = row y.2.val i at h2
  cases s with
  | inl ab =>
      change (row (fun a => x.1.val ((Equiv.swap ab.1 ab.2).symm a)) i, row x.2.val i) =
        (row (fun a => y.1.val ((Equiv.swap ab.1 ab.2).symm a)) i, row y.2.val i)
      rw [row_relabel, row_relabel, h1, h2]
  | inr ab =>
      change (row x.1.val i, row (fun b => x.2.val ((Equiv.swap ab.1 ab.2).symm b)) i) =
        (row y.1.val i, row (fun b => y.2.val ((Equiv.swap ab.1 ab.2).symm b)) i)
      rw [row_relabel, row_relabel, h1, h2]

theorem constant_of_move_invariant
    (f : State (α := α) (β := β) p q → ℝ)
    (hf : ∀ s x, f (move p q s x) = f x)
    (x y : State (α := α) (β := β) p q) : f x = f y := by
  have hleft (d : Partition (α := β) q) (c e : Partition (α := α) p) :
      f (c, d) = f (e, d) := by
    apply eq_of_swap_invariant (fun c => f (c, d)) _ c e
    intro a b c
    exact hf (Sum.inl (a, b)) (c, d)
  have hright (c : Partition (α := α) p) (d e : Partition (α := β) q) :
      f (c, d) = f (c, e) := by
    apply eq_of_swap_invariant (fun d => f (c, d)) _ d e
    intro a b d
    exact hf (Sum.inr (a, b)) (c, d)
  exact (hleft x.2 x.1 y.1).trans (hright y.1 x.2 y.2)

def rowSpace (i : Fin 3) : Submodule ℝ (EuclideanSpace ℝ (State (α := α) (β := β) p q)) where
  carrier := {f | (∑ x, f x = 0) ∧ ∀ x y, key p q i x = key p q i y → f x = f y}
  zero_mem' := by simp
  add_mem' := by
    rintro f g ⟨hfc, hfk⟩ ⟨hgc, hgk⟩
    constructor
    · simp only [PiLp.add_apply, Finset.sum_add_distrib, hfc, hgc, zero_add]
    · intro x y h
      simp only [PiLp.add_apply, hfk x y h, hgk x y h]
  smul_mem' := by
    rintro c f ⟨hfc, hfk⟩
    constructor
    · simp only [PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum, hfc, mul_zero]
    · intro x y h
      simp only [PiLp.smul_apply, hfk x y h]

theorem rowSpace_invariant (i : Fin 3)
    (f : EuclideanSpace ℝ (State (α := α) (β := β) p q))
    (hf : f ∈ rowSpace p q i) :
    PermutationGenerator.operator (move p q) f ∈ rowSpace p q i := by
  constructor
  · exact PermutationGenerator.sum_apply (move p q) f
  · intro x y h
    change (∑ s, (f x - f (move p q s x))) = ∑ s, (f y - f (move p q s y))
    apply Finset.sum_congr rfl
    intro s hs
    rw [hf.2 x y h, hf.2 _ _ (key_move_eq p q i s x y h)]

theorem local_energy_bound
    (f : Fin 3 → EuclideanSpace ℝ (State (α := α) (β := β) p q))
    (hf : ∀ i, f i ∈ rowSpace p q i)
    (s : (α × α) ⊕ (β × β)) (x : State (α := α) (β := β) p q) :
    (∑ i, (f i x - f i (move p q s x))) ^ 2 ≤
      2 * ∑ i, (f i x - f i (move p q s x)) ^ 2 := by
  cases s with
  | inl ab =>
      obtain ⟨i, hia, hib⟩ := exists_unused_color (x.1.val ab.1) (x.1.val ab.2)
      apply three_sum_sq_le_twice _ i
      have hk : key p q i (move p q (Sum.inl ab) x) = key p q i x := by
        change (row (fun a => x.1.val ((Equiv.swap ab.1 ab.2).symm a)) i, row x.2.val i) =
          (row x.1.val i, row x.2.val i)
        rw [row_swap_unchanged _ _ _ _ (Ne.symm hia) (Ne.symm hib)]
      rw [(hf i).2 _ _ hk, sub_self]
  | inr ab =>
      obtain ⟨i, hia, hib⟩ := exists_unused_color (x.2.val ab.1) (x.2.val ab.2)
      apply three_sum_sq_le_twice _ i
      have hk : key p q i (move p q (Sum.inr ab) x) = key p q i x := by
        change (row x.1.val i, row (fun b => x.2.val ((Equiv.swap ab.1 ab.2).symm b)) i) =
          (row x.1.val i, row x.2.val i)
        rw [row_swap_unchanged _ _ _ _ (Ne.symm hia) (Ne.symm hib)]
      rw [(hf i).2 _ _ hk, sub_self]

theorem centered_row_norm_bound [Nonempty (State (α := α) (β := β) p q)]
    (f : Fin 3 → EuclideanSpace ℝ (State (α := α) (β := β) p q))
    (hf : ∀ i, f i ∈ rowSpace p q i) :
    ‖∑ i, f i‖ ^ 2 ≤ 2 * ∑ i, ‖f i‖ ^ 2 := by
  exact PermutationGenerator.norm_sum_sq_le_of_invariant_moves (move p q)
    (constant_of_move_invariant p q) (rowSpace p q)
    (fun i f hf => hf.1) (rowSpace_invariant p q) 2
    (local_energy_bound p q) f hf

def average (f : State (α := α) (β := β) p q → ℝ) : ℝ :=
  (∑ x, f x) / (Fintype.card (State (α := α) (β := β) p q) : ℝ)

def variance (f : State (α := α) (β := β) p q → ℝ) : ℝ :=
  (∑ x, (f x - average p q f) ^ 2) /
    (Fintype.card (State (α := α) (β := β) p q) : ℝ)

theorem sum_sub_average [Nonempty (State (α := α) (β := β) p q)]
    (f : State (α := α) (β := β) p q → ℝ) :
    ∑ x, (f x - average p q f) = 0 := by
  have hc : (Fintype.card (State (α := α) (β := β) p q) : ℝ) ≠ 0 :=
    by exact_mod_cast Fintype.card_ne_zero
  simp only [average, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

theorem average_sum (f : Fin 3 → State (α := α) (β := β) p q → ℝ) :
    average p q (fun x => ∑ i, f i x) = ∑ i, average p q (f i) := by
  unfold average
  rw [Finset.sum_comm, Finset.sum_div]

theorem row_variance_bound [Nonempty (State (α := α) (β := β) p q)]
    (f : Fin 3 → State (α := α) (β := β) p q → ℝ)
    (hf : ∀ i x y, key p q i x = key p q i y → f i x = f i y) :
    variance p q (fun x => ∑ i, f i x) ≤ 2 * ∑ i, variance p q (f i) := by
  let g : Fin 3 → EuclideanSpace ℝ (State (α := α) (β := β) p q) :=
    fun i => WithLp.toLp 2 (fun x => f i x - average p q (f i))
  have hg (i : Fin 3) : g i ∈ rowSpace p q i := by
    constructor
    · exact sum_sub_average p q (f i)
    · intro x y h
      change f i x - average p q (f i) = f i y - average p q (f i)
      rw [hf i x y h]
  have h := centered_row_norm_bound p q g hg
  have htotal : ‖∑ i, g i‖ ^ 2 =
      ∑ x, ((∑ i, f i x) - average p q (fun y => ∑ i, f i y)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro x hx
    have he : (∑ i, g i) x = ∑ i, (f i x - average p q (f i)) := by simp [g]
    rw [he, Finset.sum_sub_distrib, average_sum]
  have heach (i : Fin 3) : ‖g i‖ ^ 2 = ∑ x, (f i x - average p q (f i)) ^ 2 := by
    exact EuclideanSpace.real_norm_sq_eq (g i)
  rw [htotal] at h
  simp_rw [heach] at h
  unfold variance
  rw [← Finset.sum_div, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right h (Nat.cast_nonneg _)

theorem variance_sum_row_functions [Nonempty (State (α := α) (β := β) p q)]
    (g : Fin 3 → Finset α → Finset β → ℝ) :
    variance p q (fun x => ∑ i, g i (row x.1.val i) (row x.2.val i)) ≤
      2 * ∑ i, variance p q (fun x => g i (row x.1.val i) (row x.2.val i)) := by
  apply row_variance_bound p q
  intro i x y h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  change row x.1.val i = row y.1.val i at h1
  change row x.2.val i = row y.2.val i at h2
  rw [h1, h2]

end Problem315.FixedBlockVariance

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/FixedBlockVariance.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/FixedBlockMarginal.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.FixedBlockMarginal
open FixedBlock

def average {X : Type*} [Fintype X] (f : X → ℝ) : ℝ :=
  (∑ x, f x) / (Fintype.card X : ℝ)

theorem average_congr {X : Type*} [Fintype X] {f g : X → ℝ}
    (h : ∀ x, f x = g x) : average f = average g := by
  simp only [average]
  congr 1
  exact Finset.sum_congr rfl (fun x _ => h x)

theorem average_const {X : Type*} [Fintype X] [Nonempty X] (c : ℝ) :
    average (fun _ : X => c) = c := by
  have hc : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [average, hc]

theorem average_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (f : Y → ℝ) : average (fun x => f (e x)) = average f := by
  simp only [average, e.sum_comp, Fintype.card_congr e]

theorem average_comm {X Y : Type*} [Fintype X] [Fintype Y] (f : X → Y → ℝ) :
    average (fun x => average (fun y => f x y)) =
      average (fun y => average (fun x => f x y)) := by
  simp only [average, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

theorem average_prod {X Y : Type*} [Fintype X] [Fintype Y] (f : X × Y → ℝ) :
    average f = average (fun x => average (fun y => f (x, y))) := by
  simp only [average, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

variable {α : Type*} [sectionFintypeα : Fintype α] [sectionDecidableEqα : DecidableEq α]

theorem permutation_average_eq {p : Fin 3 → ℕ}
    (f : Partition (α := α) p → ℝ) (c d : Partition (α := α) p) :
    average (fun σ : Equiv.Perm α => f (relabel σ c)) =
      average (fun σ : Equiv.Perm α => f (relabel σ d)) := by
  obtain ⟨τ, rfl⟩ := exists_relabel c d
  symm
  calc
    average (fun σ : Equiv.Perm α => f (relabel σ (relabel τ c))) =
        average (fun σ : Equiv.Perm α => f (relabel (σ * τ) c)) := by
      apply average_congr
      intro σ
      rw [relabel_mul]
    _ = _ := by
      simpa using average_equiv (Equiv.mulRight τ) (fun σ : Equiv.Perm α => f (relabel σ c))

theorem average_eq_permutation_average {p : Fin 3 → ℕ}
    (f : Partition (α := α) p → ℝ) (c : Partition (α := α) p) :
    average f = average (fun σ : Equiv.Perm α => f (relabel σ c)) := by
  let : Nonempty (Partition (α := α) p) := ⟨c⟩
  calc
    average f = average (fun _ : Equiv.Perm α => average f) := (average_const _).symm
    _ = average (fun σ : Equiv.Perm α =>
        average (fun d : Partition (α := α) p => f (relabel σ d))) := by
      apply average_congr
      intro σ
      exact (average_equiv (FixedBlockVariance.relabelPerm p σ) f).symm
    _ = average (fun d : Partition (α := α) p =>
        average (fun σ : Equiv.Perm α => f (relabel σ d))) := average_comm _
    _ = average (fun _ : Partition (α := α) p =>
        average (fun σ : Equiv.Perm α => f (relabel σ c))) := by
      apply average_congr
      intro d
      exact permutation_average_eq f d c
    _ = _ := average_const _

theorem exists_perm_map (s t : Finset α) (h : s.card = t.card) :
    ∃ σ : Equiv.Perm α, s.map σ.toEmbedding = t := by
  let e : {a : α // a ∈ s} ≃ {a : α // a ∈ t} :=
    Fintype.equivOfCardEq (by simpa using h)
  refine ⟨e.extendSubtype, ?_⟩
  ext a
  constructor
  · intro ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
    exact e.extendSubtype_mem b hb
  · intro ha
    let b := e.extendSubtype.symm a
    have hb : b ∈ s := by
      by_contra hn
      have hh := e.extendSubtype_not_mem b hn
      exact hh (by simpa [b] using ha)
    exact Finset.mem_map.mpr ⟨b, hb, e.extendSubtype.apply_symm_apply a⟩

theorem average_row_eq {p p' : Fin 3 → ℕ} (i : Fin 3) (h : p i = p' i)
    (c : Partition (α := α) p) (d : Partition (α := α) p') (g : Finset α → ℝ) :
    average (fun x : Partition (α := α) p => g (row x.val i)) =
      average (fun x : Partition (α := α) p' => g (row x.val i)) := by
  have hcard : (row c.val i).card = (row d.val i).card :=
    (c.property i).trans (h.trans (d.property i).symm)
  obtain ⟨τ, hτ⟩ := exists_perm_map (row c.val i) (row d.val i) hcard
  have hrow : row (relabel τ c).val i = row d.val i := by
    change row (fun a => c.val (τ.symm a)) i = row d.val i
    rw [row_relabel, hτ]
  rw [average_eq_permutation_average _ (relabel τ c),
    average_eq_permutation_average _ d]
  apply average_congr
  intro σ
  change g (row (fun a => (relabel τ c).val (σ.symm a)) i) =
    g (row (fun a => d.val (σ.symm a)) i)
  rw [row_relabel, row_relabel, hrow]

variable {β : Type*} [Fintype β] [DecidableEq β]

theorem row_function_average_eq
    {p q p' q' : Fin 3 → ℕ} (i : Fin 3) (hp : p i = p' i) (hq : q i = q' i)
    (c : Partition (α := α) p) (c' : Partition (α := α) p')
    (d : Partition (α := β) q) (d' : Partition (α := β) q')
    (g : Finset α → Finset β → ℝ) :
    FixedBlockVariance.average p q (fun x => g (row x.1.val i) (row x.2.val i)) =
      FixedBlockVariance.average p' q' (fun x => g (row x.1.val i) (row x.2.val i)) := by
  change average (fun x : Partition (α := α) p × Partition (α := β) q =>
      g (row x.1.val i) (row x.2.val i)) =
    average (fun x : Partition (α := α) p' × Partition (α := β) q' =>
      g (row x.1.val i) (row x.2.val i))
  rw [average_prod, average_prod]
  calc
    _ = average (fun x : Partition (α := α) p =>
        average (fun y : Partition (α := β) q' => g (row x.val i) (row y.val i))) := by
      apply average_congr
      intro x
      exact average_row_eq i hq d d' (g (row x.val i))
    _ = _ := average_row_eq i hp c c'
      (fun s => average (fun y : Partition (α := β) q' => g s (row y.val i)))

abbrev Subsets (k : ℕ) := {s : Finset α // s.card = k}

def subsetPerm (k : ℕ) (σ : Equiv.Perm α) : Equiv.Perm (Subsets (α := α) k) where
  toFun s := ⟨s.val.map σ.toEmbedding, by simpa using s.property⟩
  invFun s := ⟨s.val.map σ.symm.toEmbedding, by simpa using s.property⟩
  left_inv s := by
    apply Subtype.ext
    ext a
    simp
  right_inv s := by
    apply Subtype.ext
    ext a
    simp

include sectionFintypeα sectionDecidableEqα in
theorem subsetPerm_mul (k : ℕ) (σ τ : Equiv.Perm α) (s : Subsets (α := α) k) :
    subsetPerm k (σ * τ) s = subsetPerm k σ (subsetPerm k τ s) := by
  have retainedsectionFintypeα := sectionFintypeα
  have retainedsectionDecidableEqα := sectionDecidableEqα
  apply Subtype.ext
  ext a
  simp [subsetPerm]
  rfl

theorem subset_permutation_average_eq (k : ℕ) (g : Subsets (α := α) k → ℝ)
    (s t : Subsets (α := α) k) :
    average (fun σ : Equiv.Perm α => g (subsetPerm k σ s)) =
      average (fun σ : Equiv.Perm α => g (subsetPerm k σ t)) := by
  obtain ⟨τ, hτ⟩ := exists_perm_map s.val t.val (s.property.trans t.property.symm)
  have ht : subsetPerm k τ s = t := Subtype.ext hτ
  rw [← ht]
  symm
  calc
    _ = average (fun σ : Equiv.Perm α => g (subsetPerm k (σ * τ) s)) := by
      apply average_congr
      intro σ
      rw [subsetPerm_mul]
    _ = _ := by
      simpa using average_equiv (Equiv.mulRight τ)
        (fun σ : Equiv.Perm α => g (subsetPerm k σ s))

theorem subset_average_eq_permutation_average (k : ℕ)
    (g : Subsets (α := α) k → ℝ) (s : Subsets (α := α) k) :
    average g = average (fun σ : Equiv.Perm α => g (subsetPerm k σ s)) := by
  let : Nonempty (Subsets (α := α) k) := ⟨s⟩
  calc
    average g = average (fun _ : Equiv.Perm α => average g) := (average_const _).symm
    _ = average (fun σ : Equiv.Perm α =>
        average (fun t : Subsets (α := α) k => g (subsetPerm k σ t))) := by
      apply average_congr
      intro σ
      exact (average_equiv (subsetPerm k σ) g).symm
    _ = average (fun t : Subsets (α := α) k =>
        average (fun σ : Equiv.Perm α => g (subsetPerm k σ t))) := average_comm _
    _ = average (fun _ : Subsets (α := α) k =>
        average (fun σ : Equiv.Perm α => g (subsetPerm k σ s))) := by
      apply average_congr
      intro t
      exact subset_permutation_average_eq k g t s
    _ = _ := average_const _

theorem average_row_eq_subset_average {p : Fin 3 → ℕ} (i : Fin 3)
    (c : Partition (α := α) p) (g : Finset α → ℝ) :
    average (fun x : Partition (α := α) p => g (row x.val i)) =
      average (fun s : Subsets (α := α) (p i) => g s.val) := by
  rw [average_eq_permutation_average _ c,
    subset_average_eq_permutation_average _ _ ⟨row c.val i, c.property i⟩]
  apply average_congr
  intro σ
  change g (row (fun a => c.val (σ.symm a)) i) = g ((row c.val i).map σ.toEmbedding)
  rw [row_relabel]

theorem row_function_average_eq_subset_average {p q : Fin 3 → ℕ} (i : Fin 3)
    (c : Partition (α := α) p) (d : Partition (α := β) q)
    (g : Finset α → Finset β → ℝ) :
    FixedBlockVariance.average p q (fun x => g (row x.1.val i) (row x.2.val i)) =
      average (fun x : Subsets (α := α) (p i) × Subsets (α := β) (q i) =>
        g x.1.val x.2.val) := by
  change average (fun x : Partition (α := α) p × Partition (α := β) q =>
      g (row x.1.val i) (row x.2.val i)) = _
  rw [average_prod, average_prod]
  calc
    _ = average (fun x : Partition (α := α) p =>
        average (fun y : Subsets (α := β) (q i) => g (row x.val i) y.val)) := by
      apply average_congr
      intro x
      exact average_row_eq_subset_average i d (g (row x.val i))
    _ = _ := average_row_eq_subset_average i c
      (fun s => average (fun y : Subsets (α := β) (q i) => g s y.val))

end Problem315.FixedBlockMarginal

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/FixedBlockMarginal.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/FiniteVarianceDecomposition.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.FiniteVariance

open FixedBlockMarginal (average)

variable {X I : Type*} [Fintype X] [Fintype I]

def variance (f : X → ℝ) : ℝ := average (fun x => (f x - average f) ^ 2)

theorem average_add (f g : X → ℝ) :
    average (fun x => f x + g x) = average f + average g := by
  simp only [average, Finset.sum_add_distrib, add_div]

theorem average_sub (f g : X → ℝ) :
    average (fun x => f x - g x) = average f - average g := by
  simp only [average, Finset.sum_sub_distrib, sub_div]

theorem average_mul (c : ℝ) (f : X → ℝ) :
    average (fun x => c * f x) = c * average f := by
  simp only [average, ← Finset.mul_sum]
  ring

theorem average_sum (f : I → X → ℝ) :
    average (fun x => ∑ i, f i x) = ∑ i, average (f i) := by
  unfold average
  rw [Finset.sum_comm, Finset.sum_div]

theorem variance_eq [Nonempty X] (f : X → ℝ) :
    variance f = average (fun x => (f x) ^ 2) - (average f) ^ 2 := by
  have heq : (fun x => (f x - average f) ^ 2) =
      (fun x => (f x) ^ 2 - (2 * average f) * f x + (average f) ^ 2) := by
    funext x
    ring
  rw [variance, heq, average_add, average_sub, average_mul,
    FixedBlockMarginal.average_const]
  ring

theorem average_center [Nonempty X] (f : X → ℝ) :
    average (fun x => f x - average f) = 0 := by
  rw [average_sub, FixedBlockMarginal.average_const, sub_self]

theorem variance_equiv {Y : Type*} [Fintype Y] (e : X ≃ Y) (f : Y → ℝ) :
    variance (fun x => f (e x)) = variance f := by
  unfold variance
  rw [FixedBlockMarginal.average_equiv]
  exact FixedBlockMarginal.average_equiv e (fun y => (f y - average f) ^ 2)

theorem mixture_variance {K : Type*} [Fintype K]
    (Y : K → Type*) [∀ k, Fintype (Y k)] [∀ k, Nonempty (Y k)]
    (p : K → ℝ) (f : ∀ k, Y k → ℝ) :
    (∑ k, p k * average (fun y => (f k y - ∑ l, p l * average (f l)) ^ 2)) =
      (∑ k, p k * variance (f k)) +
      ∑ k, p k * (average (f k) - ∑ l, p l * average (f l)) ^ 2 := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [variance_eq]
  have heq : (fun y => (f k y - ∑ l, p l * average (f l)) ^ 2) =
      (fun y => (f k y) ^ 2 - (2 * ∑ l, p l * average (f l)) * f k y +
        (∑ l, p l * average (f l)) ^ 2) := by
    funext y
    ring
  rw [heq, average_add, average_sub, average_mul, FixedBlockMarginal.average_const]
  ring

theorem mixture_centered_row_bound {K : Type*} [Fintype K]
    (Y : K → Type*) [∀ k, Fintype (Y k)] [∀ k, Nonempty (Y k)]
    (p : K → ℝ) (hp : ∀ k, 0 ≤ p k)
    (f : I → ∀ k, Y k → ℝ)
    (hfixed : ∀ k, variance (fun y => ∑ i, f i k y) ≤
      2 * ∑ i, variance (f i k))
    (hmean : (∑ k, p k * (∑ i, average (f i k)) ^ 2) ≤
      2 * ∑ i, ∑ k, p k * (average (f i k)) ^ 2) :
    (∑ k, p k * average (fun y => (∑ i, f i k y) ^ 2)) ≤
      2 * ∑ i, ∑ k, p k * average (fun y => (f i k y) ^ 2) := by
  have hfixed' (k : K) := hfixed k
  simp_rw [variance_eq, average_sum] at hfixed'
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hfixed' k) (hp k))
  simp only [mul_sub, Finset.sum_sub_distrib] at hs
  have hrew (q : I → K → ℝ) :
      (∑ k, p k * (2 * ∑ i, q i k)) = 2 * ∑ i, ∑ k, p k * q i k := by
    calc
      _ = ∑ k, 2 * (∑ i, p k * q i k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [← Finset.mul_sum]
        ring
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
  rw [hrew, hrew] at hs
  linarith

end Problem315.FiniteVariance

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/FiniteVarianceDecomposition.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/FiberLabelCounting.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace Problem315.FiberLabelCounting

variable {V C : Type*} [sectionFintypeV : Fintype V] [sectionFintypeC : Fintype C]

abbrev PrescribedFiberColorings (k : C → ℕ) :=
  {g : V → C // ∀ c, Fintype.card {v // g v = c} = k c}

abbrev EqualFiberColorings (f₀ : V → C) :=
  {g : V → C // ∀ c, Fintype.card {v // g v = c} = Fintype.card {v // f₀ v = c}}

abbrev LabeledFibers (f₀ : V → C) :=
  Σ g : EqualFiberColorings f₀, ∀ c, {v // f₀ v = c} ≃ {v // g.val v = c}

include sectionFintypeV sectionFintypeC in
private theorem ofFiberEquiv_apply_subtype {f g : V → C}
    (e : ∀ c, {v // f v = c} ≃ {v // g v = c}) (c : C) (v : {v // f v = c}) :
    Equiv.ofFiberEquiv e v.val = (e c v).val := by
  have retainedsectionFintypeV := sectionFintypeV
  have retainedsectionFintypeC := sectionFintypeC
  rcases v with ⟨v, hv⟩
  subst c
  rfl

def labeledFibersEquivPerm (f₀ : V → C) : LabeledFibers f₀ ≃ Equiv.Perm V := by
  let F : LabeledFibers f₀ → Equiv.Perm V := fun a => Equiv.ofFiberEquiv a.2
  apply Equiv.ofBijective F
  constructor
  · rintro ⟨⟨g, hg⟩, e⟩ ⟨⟨h, hh⟩, f⟩ hp
    change Equiv.ofFiberEquiv e = Equiv.ofFiberEquiv f at hp
    have hgh : g = h := by
      funext y
      obtain ⟨x, rfl⟩ := (Equiv.ofFiberEquiv e).surjective y
      have hx := Equiv.ofFiberEquiv_map e x
      have hy := Equiv.ofFiberEquiv_map f x
      rw [← hp] at hy
      exact hx.trans hy.symm
    subst h
    have hef : e = f := by
      funext c
      apply Equiv.ext
      intro v
      apply Subtype.ext
      rw [← ofFiberEquiv_apply_subtype e c v, ← ofFiberEquiv_apply_subtype f c v]
      exact congrArg (fun p : Equiv.Perm V => p v.val) hp
    subst f
    rfl
  · intro p
    let g : V → C := fun v => f₀ (p.symm v)
    let e (c : C) : {v // f₀ v = c} ≃ {v // g v = c} :=
      { toFun := fun v => ⟨p v.val, by simpa [g] using v.property⟩
        invFun := fun v => ⟨p.symm v.val, v.property⟩
        left_inv := by intro v; apply Subtype.ext; simp
        right_inv := by intro v; apply Subtype.ext; simp }
    have hg : ∀ c, Fintype.card {v // g v = c} = Fintype.card {v // f₀ v = c} :=
      fun c => (Fintype.card_congr (e c)).symm
    refine ⟨⟨⟨g, hg⟩, e⟩, ?_⟩
    apply Equiv.ext
    intro v
    rfl

theorem equalFiberColorings_card_mul_factorials (f₀ : V → C) :
    Fintype.card (EqualFiberColorings f₀) *
      (∏ c, (Fintype.card {v // f₀ v = c}).factorial) = (Fintype.card V).factorial := by
  have he (g : EqualFiberColorings f₀) :
      Fintype.card (∀ c, {v // f₀ v = c} ≃ {v // g.val v = c}) =
        ∏ c, (Fintype.card {v // f₀ v = c}).factorial := by
    rw [Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro c _
    exact Fintype.card_equiv (Fintype.equivOfCardEq (g.property c).symm)
  have hd : Fintype.card (LabeledFibers f₀) =
      Fintype.card (EqualFiberColorings f₀) *
        (∏ c, (Fintype.card {v // f₀ v = c}).factorial) := by
    rw [Fintype.card_sigma]
    simp_rw [he]
    simp
  rw [← hd, Fintype.card_congr (labeledFibersEquivPerm f₀), Fintype.card_perm]

theorem prescribedFiberColorings_nonempty (k : C → ℕ)
    (hk : ∑ c, k c = Fintype.card V) :
    Nonempty (PrescribedFiberColorings (V := V) k) := by
  have hc : Fintype.card V = Fintype.card (Σ c, Fin (k c)) := by
    rw [Fintype.card_sigma]
    simpa only [Fintype.card_fin] using hk.symm
  let e : V ≃ (Σ c, Fin (k c)) := Fintype.equivOfCardEq hc
  let g : V → C := fun v => (e v).1
  refine ⟨⟨g, fun c => ?_⟩⟩
  let ef : {v // g v = c} ≃ Fin (k c) :=
    (e.subtypeEquiv (fun v => Iff.rfl)).trans (Equiv.sigmaSubtype c)
  exact (Fintype.card_congr ef).trans (Fintype.card_fin (k c))

theorem prescribedFiberColorings_card_mul_factorials (k : C → ℕ)
    (hne : Nonempty (PrescribedFiberColorings (V := V) k)) :
    Fintype.card (PrescribedFiberColorings (V := V) k) *
      (∏ c, (k c).factorial) = (Fintype.card V).factorial := by
  obtain ⟨⟨f₀, hf₀⟩⟩ := hne
  let e : {g : V → C // ∀ c, Fintype.card {v // g v = c} = k c} ≃
      EqualFiberColorings f₀ :=
    Equiv.subtypeEquivRight (fun g => by simp only [hf₀])
  have h := equalFiberColorings_card_mul_factorials f₀
  rw [Fintype.card_congr e]
  simpa only [hf₀] using h

end Problem315.FiberLabelCounting

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/FiberLabelCounting.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/FixedBlockCount.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace Problem315.FixedBlock

variable {α β : Type*} [Fintype α] [sectionDecidableEqα : DecidableEq α] [Fintype β] [DecidableEq β]

def partitionEquivColorings (sizes : Fin 3 → ℕ) :
    Partition (α := α) sizes ≃
    FiberLabelCounting.PrescribedFiberColorings (V := α) sizes :=
  Equiv.subtypeEquivRight (fun g => by simp [Fintype.card_subtype, row])

include sectionDecidableEqα in
theorem partition_nonempty (sizes : Fin 3 → ℕ)
    (hsum : ∑ i, sizes i = Fintype.card α) :
    Nonempty (Partition (α := α) sizes) := by
  have retainedsectionDecidableEqα := sectionDecidableEqα
  have h := FiberLabelCounting.prescribedFiberColorings_nonempty (V := α) sizes hsum
  exact h.map (fun c => (partitionEquivColorings (α := α) sizes).symm c)

theorem partition_card_mul_factorials (sizes : Fin 3 → ℕ)
    (hne : Nonempty (Partition (α := α) sizes)) :
    Fintype.card (Partition (α := α) sizes) * (∏ i, (sizes i).factorial) =
      (Fintype.card α).factorial := by
  rw [Fintype.card_congr (partitionEquivColorings sizes)]
  have h := FiberLabelCounting.prescribedFiberColorings_card_mul_factorials (V := α) sizes
    (hne.map (fun c => partitionEquivColorings (α := α) sizes c))
  simpa only [← Nat.card_eq_fintype_card] using h

theorem partition_card_real (sizes : Fin 3 → ℕ)
    (hne : Nonempty (Partition (α := α) sizes)) :
    (Fintype.card (Partition (α := α) sizes) : ℝ) =
      (Fintype.card α).factorial / ∏ i, ((sizes i).factorial : ℝ) := by
  have hp : (∏ i, ((sizes i).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast Nat.factorial_ne_zero (sizes i))
  apply (eq_div_iff hp).mpr
  exact_mod_cast partition_card_mul_factorials sizes hne

theorem partition_pair_card_real (sizesU sizesW : Fin 3 → ℕ)
    (hU : Nonempty (Partition (α := α) sizesU))
    (hW : Nonempty (Partition (α := β) sizesW)) :
    (Fintype.card (Partition (α := α) sizesU × Partition (α := β) sizesW) : ℝ) =
      ((Fintype.card α).factorial * (Fintype.card β).factorial : ℝ) /
        ∏ i, (((sizesU i).factorial : ℝ) * ((sizesW i).factorial : ℝ)) := by
  rw [Fintype.card_prod, Nat.cast_mul, partition_card_real sizesU hU,
    partition_card_real sizesW hW, div_mul_div_comm, Finset.prod_mul_distrib]

theorem partition_pair_card_real_of_sum (sizesU sizesW : Fin 3 → ℕ)
    (hU : ∑ i, sizesU i = Fintype.card α)
    (hW : ∑ i, sizesW i = Fintype.card β) :
    (Fintype.card (Partition (α := α) sizesU × Partition (α := β) sizesW) : ℝ) =
      ((Fintype.card α).factorial * (Fintype.card β).factorial : ℝ) /
        ∏ i, (((sizesU i).factorial : ℝ) * ((sizesW i).factorial : ℝ)) :=
  partition_pair_card_real sizesU sizesW
    (partition_nonempty sizesU hU) (partition_nonempty sizesW hW)

def pairSizeWeight (sizesU sizesW : Fin 3 → ℕ) : ℝ :=
  (∏ i, (((sizesU i).factorial : ℝ) * ((sizesW i).factorial : ℝ)))⁻¹

theorem uniform_size_expectation {K : Type*} [Fintype K]
    (sizesU sizesW : K → Fin 3 → ℕ)
    (hU : ∀ k, ∑ i, sizesU k i = Fintype.card α)
    (hW : ∀ k, ∑ i, sizesW k i = Fintype.card β) (f : K → ℝ) :
    (∑ p : (Σ k, Partition (α := α) (sizesU k) × Partition (α := β) (sizesW k)),
      f p.1) /
      Fintype.card (Σ k, Partition (α := α) (sizesU k) × Partition (α := β) (sizesW k)) =
    (∑ k, pairSizeWeight (sizesU k) (sizesW k) * f k) /
      ∑ k, pairSizeWeight (sizesU k) (sizesW k) := by
  let C : ℝ := (Fintype.card α).factorial * (Fintype.card β).factorial
  have hC : C ≠ 0 := by
    dsimp [C]
    exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (Fintype.card α))
      (by exact_mod_cast Nat.factorial_ne_zero (Fintype.card β))
  have hc (k : K) :
      (Fintype.card (Partition (α := α) (sizesU k) ×
        Partition (α := β) (sizesW k)) : ℝ) =
      C * pairSizeWeight (sizesU k) (sizesW k) := by
    simpa only [C, pairSizeWeight, div_eq_mul_inv] using
      partition_pair_card_real_of_sum (sizesU k) (sizesW k) (hU k) (hW k)
  have hn : (∑ p : (Σ k, Partition (α := α) (sizesU k) ×
      Partition (α := β) (sizesW k)), f p.1) =
      C * ∑ k, pairSizeWeight (sizesU k) (sizesW k) * f k := by
    rw [Fintype.sum_sigma, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc, mul_assoc]
  have hd : (Fintype.card (Σ k, Partition (α := α) (sizesU k) ×
      Partition (α := β) (sizesW k)) : ℝ) =
      C * ∑ k, pairSizeWeight (sizesU k) (sizesW k) := by
    rw [Fintype.card_sigma, Nat.cast_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => hc k)
  rw [hn, hd, mul_div_mul_left _ _ hC]

theorem uniform_family_expectation {K : Type*} [Fintype K]
    (sizesU sizesW : K → Fin 3 → ℕ)
    (hU : ∀ k, ∑ i, sizesU k i = Fintype.card α)
    (hW : ∀ k, ∑ i, sizesW k i = Fintype.card β)
    (f : ∀ k, Partition (α := α) (sizesU k) × Partition (α := β) (sizesW k) → ℝ) :
    (∑ p : (Σ k, Partition (α := α) (sizesU k) × Partition (α := β) (sizesW k)),
      f p.1 p.2) /
      Fintype.card (Σ k, Partition (α := α) (sizesU k) × Partition (α := β) (sizesW k)) =
    (∑ k, pairSizeWeight (sizesU k) (sizesW k) *
      ((∑ p, f k p) /
        Fintype.card (Partition (α := α) (sizesU k) × Partition (α := β) (sizesW k)))) /
      ∑ k, pairSizeWeight (sizesU k) (sizesW k) := by
  rw [← uniform_size_expectation sizesU sizesW hU hW]
  congr 1
  rw [Fintype.sum_sigma, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  obtain ⟨u⟩ := partition_nonempty (sizesU k) (hU k)
  obtain ⟨w⟩ := partition_nonempty (sizesW k) (hW k)
  have : Nonempty (Partition (α := α) (sizesU k) ×
      Partition (α := β) (sizesW k)) := ⟨(u, w)⟩
  have hc : (Fintype.card (Partition (α := α) (sizesU k) ×
      Partition (α := β) (sizesW k)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  change (∑ p, f k p) =
    ∑ _p : Partition (α := α) (sizesU k) × Partition (α := β) (sizesW k),
      (∑ p, f k p) / Fintype.card (Partition (α := α) (sizesU k) ×
        Partition (α := β) (sizesW k))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

end Problem315.FixedBlock

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/FixedBlockCount.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/CountCoupling.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.CountCoupling

theorem weighted_covariance_identity {ι : Type*} (s : Finset ι)
    (w a b : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * (a i - a j) * (b i - b j)) =
      2 * ((∑ i ∈ s, w i) * (∑ i ∈ s, w i * a i * b i) -
        (∑ i ∈ s, w i * a i) * (∑ i ∈ s, w i * b i)) := by
  calc
    _ = ∑ i ∈ s, ∑ j ∈ s,
        (w i * a i * b i * w j - w i * a i * (w j * b j) -
          w i * b i * (w j * a j) + w i * (w j * a j * b j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul]
      ring

theorem weighted_chebyshev {ι : Type*} (s : Finset ι)
    (w a b : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hab : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ (a i - a j) * (b i - b j)) :
    (∑ i ∈ s, w i * a i) * (∑ i ∈ s, w i * b i) ≤
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * a i * b i) := by
  have hnonneg : 0 ≤ ∑ i ∈ s, ∑ j ∈ s,
      w i * w j * (a i - a j) * (b i - b j) := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    simpa only [mul_assoc] using
      mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (hab i hi j hj)
  rw [weighted_covariance_identity] at hnonneg
  linarith

theorem weighted_chebyshev_of_monotone {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (w a b : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (ha : MonotoneOn a s) (hb : MonotoneOn b s) :
    (∑ i ∈ s, w i * a i) * (∑ i ∈ s, w i * b i) ≤
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * a i * b i) := by
  apply weighted_chebyshev s w a b hw
  intro i hi j hj
  rcases le_total i j with hij | hji
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (ha hi hj hij))
      (sub_nonpos.mpr (hb hi hj hij))
  · exact mul_nonneg (sub_nonneg.mpr (ha hj hi hji))
      (sub_nonneg.mpr (hb hj hi hji))

theorem monotone_reweighting {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (w a b : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hW : 0 < ∑ i ∈ s, w i)
    (hA : 0 < ∑ i ∈ s, w i * a i)
    (ha : MonotoneOn a s) (hb : MonotoneOn b s) :
    (∑ i ∈ s, w i * b i) / (∑ i ∈ s, w i) ≤
      (∑ i ∈ s, w i * a i * b i) / (∑ i ∈ s, w i * a i) := by
  apply (div_le_div_iff₀ hW hA).mpr
  simpa only [mul_comm] using weighted_chebyshev_of_monotone s w a b hw ha hb

def countWeight (α t : ℕ) : ℝ :=
  1 / ((t.factorial : ℝ) * ((t + α).factorial : ℝ))

theorem countWeight_pos (α t : ℕ) : 0 < countWeight α t := by
  unfold countWeight
  positivity

theorem countWeight_succ (α t : ℕ) :
    countWeight α (t + 1) =
      countWeight α t / (((t : ℝ) + 1) * ((t : ℝ) + 1 + α)) := by
  unfold countWeight
  rw [show t + 1 + α = (t + α) + 1 by omega,
    Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  rw [div_div]
  congr 1
  ring

theorem adjacent_likelihood_monotone (α s : ℕ) :
    MonotoneOn
      (fun y : ℕ => 1 / (((s - y : ℕ) : ℝ) * ((s - y + α : ℕ) : ℝ)))
      (Finset.range s) := by
  intro y hy z hz hyz
  have hys : y < s := Finset.mem_range.mp hy
  have hzs : z < s := Finset.mem_range.mp hz
  have hsub : s - z ≤ s - y := Nat.sub_le_sub_left hyz s
  have hzpos : (0 : ℝ) < (s - z : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hzs
  have hsubR : ((s - z : ℕ) : ℝ) ≤ (s - y : ℕ) := by exact_mod_cast hsub
  apply one_div_le_one_div_of_le
  · have hzpos' : (0 : ℝ) < ((s - z + α : ℕ) : ℝ) := by
      have : 0 < s - z + α := by omega
      exact_mod_cast this
    exact mul_pos hzpos hzpos'
  · push_cast
    exact mul_le_mul hsubR (add_le_add hsubR le_rfl) (by positivity)
      (by positivity)

theorem mean_le_add_top_mass {ι : Type*} (s : Finset ι)
    (w b : ι → ℝ) (a B : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : 0 < ∑ i ∈ s, w i)
    (ha : 0 ≤ a) (hB : ∀ i ∈ s, b i ≤ B) :
    (∑ i ∈ s, w i * b i) / (∑ i ∈ s, w i) ≤
      ((∑ i ∈ s, w i * b i) + a * B) / ((∑ i ∈ s, w i) + a) := by
  have hsum : (∑ i ∈ s, w i * b i) ≤ (∑ i ∈ s, w i) * B := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hB i hi) (hw i hi))
  apply (div_le_div_iff₀ hW (by linarith)).mpr
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hsum)]

def pairWeight (α β s y : ℕ) : ℝ :=
  countWeight α y * countWeight β (s - y)

theorem pairWeight_pos (α β s y : ℕ) : 0 < pairWeight α β s y := by
  exact mul_pos (countWeight_pos α y) (countWeight_pos β (s - y))

theorem pairWeight_succ (α β s y : ℕ) (hy : y ≤ s) :
    pairWeight α β (s + 1) y = pairWeight α β s y *
      (1 / (((s + 1 - y : ℕ) : ℝ) * ((s + 1 - y + β : ℕ) : ℝ))) := by
  unfold pairWeight
  have hsub : s + 1 - y = (s - y) + 1 := by omega
  rw [hsub, countWeight_succ]
  push_cast
  ring

def pairExpectation (α β s : ℕ) (b : ℕ → ℝ) : ℝ :=
  (∑ y ∈ Finset.range (s + 1), pairWeight α β s y * b y) /
    (∑ y ∈ Finset.range (s + 1), pairWeight α β s y)

theorem pairExpectation_le_succ (α β s : ℕ) (b : ℕ → ℝ)
    (hb : Monotone b) : pairExpectation α β s b ≤ pairExpectation α β (s + 1) b := by
  let S := Finset.range (s + 1)
  let w := pairWeight α β s
  let a : ℕ → ℝ := fun y =>
    1 / (((s + 1 - y : ℕ) : ℝ) * ((s + 1 - y + β : ℕ) : ℝ))
  have hw : ∀ y ∈ S, 0 ≤ w y := fun y _ => le_of_lt (pairWeight_pos α β s y)
  have hW : 0 < ∑ y ∈ S, w y := by
    apply Finset.sum_pos
    · intro y hy
      exact pairWeight_pos α β s y
    · exact ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hnew : ∀ y ∈ S, w y * a y = pairWeight α β (s + 1) y := by
    intro y hy
    symm
    exact pairWeight_succ α β s y (by have := Finset.mem_range.mp hy; omega)
  have hA : 0 < ∑ y ∈ S, w y * a y := by
    apply Finset.sum_pos
    · intro y hy
      rw [hnew y hy]
      exact pairWeight_pos α β (s + 1) y
    · exact ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hfirst := monotone_reweighting S w a b hw hW hA
    (adjacent_likelihood_monotone β (s + 1)) (hb.monotoneOn _)
  have hnext := mean_le_add_top_mass S (fun y => w y * a y) b
    (pairWeight α β (s + 1) (s + 1)) (b (s + 1))
    (fun y hy => by rw [hnew y hy]; exact le_of_lt (pairWeight_pos α β (s + 1) y))
    hA (le_of_lt (pairWeight_pos α β (s + 1) (s + 1)))
    (fun y hy => hb (by have := Finset.mem_range.mp hy; omega))
  have hnum : (∑ y ∈ S, w y * a y * b y) =
      ∑ y ∈ S, pairWeight α β (s + 1) y * b y := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [hnew y hy]
  have hden : (∑ y ∈ S, w y * a y) =
      ∑ y ∈ S, pairWeight α β (s + 1) y := by
    exact Finset.sum_congr rfl hnew
  rw [hnum, hden] at hfirst hnext
  simpa only [pairExpectation, S, w, Finset.sum_range_succ] using hfirst.trans hnext

theorem pairExpectation_congr (α β s : ℕ) (b c : ℕ → ℝ)
    (h : ∀ y ≤ s, b y = c y) :
    pairExpectation α β s b = pairExpectation α β s c := by
  unfold pairExpectation
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  rw [h y (by have := Finset.mem_range.mp hy; omega)]

theorem sum_pairWeight_reflect (α β s : ℕ) (b : ℕ → ℝ) :
    (∑ y ∈ Finset.range (s + 1), pairWeight α β s y * b y) =
      ∑ y ∈ Finset.range (s + 1), pairWeight β α s y * b (s - y) := by
  calc
    _ = ∑ y ∈ Finset.range (s + 1), pairWeight α β s (s - y) * b (s - y) := by
      simpa using (Finset.sum_range_reflect
        (fun y => pairWeight α β s y * b y) (s + 1)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y hy
      have hys : y ≤ s := by have := Finset.mem_range.mp hy; omega
      have hsub : s - (s - y) = y := by omega
      simp only [pairWeight, hsub]
      ring

theorem pairExpectation_reflect (α β s : ℕ) (b : ℕ → ℝ) :
    pairExpectation α β s b = pairExpectation β α s (fun y => b (s - y)) := by
  unfold pairExpectation
  rw [sum_pairWeight_reflect]
  have hden := sum_pairWeight_reflect α β s (fun _ => (1 : ℝ))
  simp only [mul_one] at hden
  rw [hden]

theorem pairExpectation_neg (α β s : ℕ) (b : ℕ → ℝ) :
    pairExpectation α β s (fun y => -b y) = -pairExpectation α β s b := by
  simp only [pairExpectation, mul_neg, Finset.sum_neg_distrib, neg_div]

theorem pairExpectation_succ_le_of_antitone (α β s : ℕ) (b : ℕ → ℝ)
    (hb : Antitone b) : pairExpectation α β (s + 1) b ≤ pairExpectation α β s b := by
  have h := pairExpectation_le_succ α β s (fun y => -b y)
    (fun _ _ hij => neg_le_neg (hb hij))
  rw [pairExpectation_neg, pairExpectation_neg] at h
  linarith

theorem pairExpectation_succ_le_shift (α β s : ℕ) (b : ℕ → ℝ)
    (hb : Monotone b) :
    pairExpectation α β (s + 1) b ≤ pairExpectation α β s (fun y => b (y + 1)) := by
  let c : ℕ → ℝ := fun y => b (s + 1 - y)
  have hc : Antitone c := by
    intro y z hyz
    exact hb (Nat.sub_le_sub_left hyz (s + 1))
  rw [pairExpectation_reflect α β (s + 1) b]
  calc
    pairExpectation β α (s + 1) c ≤ pairExpectation β α s c :=
      pairExpectation_succ_le_of_antitone β α s c hc
    _ = pairExpectation α β s (fun y => c (s - y)) :=
      pairExpectation_reflect β α s c
    _ = pairExpectation α β s (fun y => b (y + 1)) := by
      apply pairExpectation_congr
      intro y hy
      dsimp [c]
      congr 1
      omega

end Problem315.CountCoupling

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/CountCoupling.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/TripleCountLaw.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.TripleCountLaw

abbrev Triple (m : ℕ) :=
  {x : Fin 3 → Fin (m + 1) // ∑ i : Fin 3, (x i).val = m}

def weight (a : Fin 3 → ℕ) {m : ℕ} (x : Triple m) : ℝ :=
  ∏ i : Fin 3, CountCoupling.countWeight (a i) (x.val i).val

abbrev Fiber (m : ℕ) (σ : Equiv.Perm (Fin 3)) (t : ℕ) :=
  {x : Triple m // (x.val (σ 0)).val = t}

def fiberEquiv (m : ℕ) (σ : Equiv.Perm (Fin 3)) (t : ℕ) (ht : t ≤ m) :
    Fin (m - t + 1) ≃ Fiber m σ t where
  toFun y :=
    ⟨⟨fun i => (![⟨t, by omega⟩, ⟨y.val, by omega⟩,
      ⟨m - t - y.val, by omega⟩] : Fin 3 → Fin (m + 1)) (σ.symm i), by
      rw [← Equiv.sum_comp σ]
      simp only [Equiv.symm_apply_apply]
      simp only [Fin.sum_univ_three]
      dsimp
      omega⟩, by simp⟩
  invFun x := ⟨(x.val.val (σ 1)).val, by
    have hs := x.val.property
    rw [← Equiv.sum_comp σ] at hs
    simp only [Fin.sum_univ_three] at hs
    have hx := x.property
    omega⟩
  left_inv y := by simp
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    obtain ⟨j, rfl⟩ := σ.surjective i
    apply Fin.ext
    have hs := x.val.property
    rw [← Equiv.sum_comp σ] at hs
    simp only [Fin.sum_univ_three] at hs
    have hx := x.property
    fin_cases j <;> simp at * <;> omega

@[simp] theorem fiberEquiv_coordinate_zero (m : ℕ) (σ : Equiv.Perm (Fin 3))
    (t : ℕ) (ht : t ≤ m) (y : Fin (m - t + 1)) :
    (((fiberEquiv m σ t ht y).val.val (σ 0)).val) = t := by
  simp [fiberEquiv]

@[simp] theorem fiberEquiv_coordinate_one (m : ℕ) (σ : Equiv.Perm (Fin 3))
    (t : ℕ) (ht : t ≤ m) (y : Fin (m - t + 1)) :
    (((fiberEquiv m σ t ht y).val.val (σ 1)).val) = y.val := by
  simp [fiberEquiv]

@[simp] theorem fiberEquiv_coordinate_two (m : ℕ) (σ : Equiv.Perm (Fin 3))
    (t : ℕ) (ht : t ≤ m) (y : Fin (m - t + 1)) :
    (((fiberEquiv m σ t ht y).val.val (σ 2)).val) = m - t - y.val := by
  simp [fiberEquiv]

theorem weight_pos (a : Fin 3 → ℕ) {m : ℕ} (x : Triple m) : 0 < weight a x := by
  exact Finset.prod_pos (fun i _ => CountCoupling.countWeight_pos _ _)

theorem weight_fiberEquiv (a : Fin 3 → ℕ) (m : ℕ) (σ : Equiv.Perm (Fin 3))
    (t : ℕ) (ht : t ≤ m) (y : Fin (m - t + 1)) :
    weight a (fiberEquiv m σ t ht y).val =
      CountCoupling.countWeight (a (σ 0)) t *
        CountCoupling.pairWeight (a (σ 1)) (a (σ 2)) (m - t) y.val := by
  unfold weight
  rw [← Equiv.prod_comp σ]
  simp [Fin.prod_univ_three, CountCoupling.pairWeight, mul_assoc]

def conditionalAverage (a : Fin 3 → ℕ) {m : ℕ} (f : Triple m → ℝ)
    (σ : Equiv.Perm (Fin 3)) (t : ℕ) : ℝ :=
  (∑ x : Fiber m σ t, weight a x.val * f x.val) /
    (∑ x : Fiber m σ t, weight a x.val)

theorem conditionalAverage_reindex (a : Fin 3 → ℕ) {m : ℕ}
    (f : Triple m → ℝ) (σ : Equiv.Perm (Fin 3)) (t : ℕ) (ht : t ≤ m) :
    conditionalAverage a f σ t =
      (∑ y : Fin (m - t + 1),
        CountCoupling.pairWeight (a (σ 1)) (a (σ 2)) (m - t) y.val *
          f (fiberEquiv m σ t ht y).val) /
      (∑ y : Fin (m - t + 1),
        CountCoupling.pairWeight (a (σ 1)) (a (σ 2)) (m - t) y.val) := by
  unfold conditionalAverage
  rw [← Equiv.sum_comp (fiberEquiv m σ t ht) (fun x => weight a x.val * f x.val),
    ← Equiv.sum_comp (fiberEquiv m σ t ht) (fun x => weight a x.val)]
  simp_rw [weight_fiberEquiv, mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ (ne_of_gt (CountCoupling.countWeight_pos _ _))

def rowSum {m : ℕ} (b : Fin 3 → ℕ → ℝ) (x : Triple m) : ℝ :=
  ∑ i : Fin 3, b i (x.val i).val

theorem rowSum_fiberEquiv (b : Fin 3 → ℕ → ℝ) (m : ℕ)
    (σ : Equiv.Perm (Fin 3)) (t : ℕ) (ht : t ≤ m) (y : Fin (m - t + 1)) :
    rowSum b (fiberEquiv m σ t ht y).val =
      b (σ 0) t + (b (σ 1) y.val + b (σ 2) (m - t - y.val)) := by
  unfold rowSum
  rw [← Equiv.sum_comp σ]
  simp [Fin.sum_univ_three, add_assoc]

theorem conditionalAverage_rowSum (a : Fin 3 → ℕ) (m : ℕ)
    (b : Fin 3 → ℕ → ℝ) (σ : Equiv.Perm (Fin 3)) (t : ℕ) (ht : t ≤ m) :
    conditionalAverage a (rowSum b : Triple m → ℝ) σ t =
      b (σ 0) t + CountCoupling.pairExpectation (a (σ 1)) (a (σ 2)) (m - t)
        (fun y => b (σ 1) y + b (σ 2) (m - t - y)) := by
  rw [conditionalAverage_reindex a (rowSum b) σ t ht]
  simp_rw [rowSum_fiberEquiv]
  rw [Fin.sum_univ_eq_sum_range
    (fun y => CountCoupling.pairWeight (a (σ 1)) (a (σ 2)) (m - t) y *
      (b (σ 0) t + (b (σ 1) y + b (σ 2) (m - t - y)))) (m - t + 1),
    Fin.sum_univ_eq_sum_range]
  unfold CountCoupling.pairExpectation
  have hpos : 0 < ∑ y ∈ Finset.range (m - t + 1),
      CountCoupling.pairWeight (a (σ 1)) (a (σ 2)) (m - t) y := by
    apply Finset.sum_pos
    · intro y hy
      exact CountCoupling.pairWeight_pos _ _ _ _
    · exact ⟨0, Finset.mem_range.mpr (by omega)⟩
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  field_simp [ne_of_gt hpos]

theorem fiber_nonempty (m : ℕ) (σ : Equiv.Perm (Fin 3)) (t : ℕ) (ht : t ≤ m) :
    Nonempty (Fiber m σ t) :=
  ⟨fiberEquiv m σ t ht ⟨0, by omega⟩⟩

theorem fiber_weight_sum_pos (a : Fin 3 → ℕ) (m : ℕ)
    (σ : Equiv.Perm (Fin 3)) (t : ℕ) (ht : t ≤ m) :
    0 < ∑ x : Fiber m σ t, weight a x.val := by
  have := fiber_nonempty m σ t ht
  exact Finset.sum_pos (fun x _ => weight_pos a x.val) Finset.univ_nonempty

def totalWeight (a : Fin 3 → ℕ) (m : ℕ) : ℝ := ∑ x : Triple m, weight a x

theorem totalWeight_pos (a : Fin 3 → ℕ) (m : ℕ) : 0 < totalWeight a m := by
  obtain ⟨x⟩ := fiber_nonempty m (Equiv.refl _) 0 (Nat.zero_le _)
  have : Nonempty (Triple m) := ⟨x.val⟩
  exact Finset.sum_pos (fun x _ => weight_pos a x) Finset.univ_nonempty

def probability (a : Fin 3 → ℕ) {m : ℕ} (x : Triple m) : ℝ :=
  weight a x / totalWeight a m

theorem probability_pos (a : Fin 3 → ℕ) {m : ℕ} (x : Triple m) :
    0 < probability a x := div_pos (weight_pos a x) (totalWeight_pos a m)

theorem probability_sum (a : Fin 3 → ℕ) (m : ℕ) :
    ∑ x : Triple m, probability a x = 1 := by
  simp only [probability, ← Finset.sum_div]
  exact div_self (ne_of_gt (totalWeight_pos a m))

theorem sum_fiber_eq_indicator (m : ℕ) (σ : Equiv.Perm (Fin 3)) (t : ℕ)
    (f : Triple m → ℝ) :
    (∑ x : Fiber m σ t, f x.val) =
      ∑ x : Triple m, if (x.val (σ 0)).val = t then f x else 0 := by
  classical
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (fun x => by simp) f).symm

theorem normalized_conditionalAverage (a : Fin 3 → ℕ) {m : ℕ}
    (f : Triple m → ℝ) (σ : Equiv.Perm (Fin 3)) (t : ℕ) :
    ((∑ x : Triple m, if (x.val (σ 0)).val = t then probability a x * f x else 0) /
      (∑ x : Triple m, if (x.val (σ 0)).val = t then probability a x else 0)) =
      conditionalAverage a f σ t := by
  rw [← sum_fiber_eq_indicator, ← sum_fiber_eq_indicator]
  unfold probability conditionalAverage
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, ← Finset.sum_div]
  exact div_div_div_cancel_right₀ (ne_of_gt (totalWeight_pos a m)) _ _

theorem marginal_pos (a : Fin 3 → ℕ) (m : ℕ) (σ : Equiv.Perm (Fin 3))
    (t : ℕ) (ht : t ≤ m) :
    0 < ∑ x : Triple m, if (x.val (σ 0)).val = t then probability a x else 0 := by
  rw [← sum_fiber_eq_indicator]
  have := fiber_nonempty m σ t ht
  exact Finset.sum_pos (fun x _ => probability_pos a x.val) Finset.univ_nonempty

theorem normalized_conditional_rowSum (a : Fin 3 → ℕ) (m : ℕ)
    (b : Fin 3 → ℕ → ℝ) (σ : Equiv.Perm (Fin 3)) (t : ℕ) (ht : t ≤ m) :
    ((∑ x : Triple m, if (x.val (σ 0)).val = t then
        probability a x * rowSum b x else 0) /
      (∑ x : Triple m, if (x.val (σ 0)).val = t then probability a x else 0)) =
      b (σ 0) t + CountCoupling.pairExpectation (a (σ 1)) (a (σ 2)) (m - t)
        (fun y => b (σ 1) y + b (σ 2) (m - t - y)) := by
  rw [normalized_conditionalAverage]
  exact conditionalAverage_rowSum a m b σ t ht

end Problem315.TripleCountLaw

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/TripleCountLaw.lean -/
