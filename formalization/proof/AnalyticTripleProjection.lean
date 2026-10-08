import AnalyticMatrixVariance

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairFibers.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Problem315.PairFibers

def SameFiber {n : ℕ} (a : Finset (Fin n))
    (G H : SimpleGraph (Fin n)) : Prop :=
  (∀ u v, u ∉ a → v ∉ a → (G.Adj u v ↔ H.Adj u v)) ∧
  (∀ u v, u ∈ a → v ∈ a → (G.Adj u v ↔ H.Adj u v)) ∧
  (∀ w, w ∉ a →
    (a.filter (fun u => G.Adj u w)).card = (a.filter (fun u => H.Adj u w)).card)

theorem SameFiber.refl {n : ℕ} (a : Finset (Fin n)) (G : SimpleGraph (Fin n)) :
    SameFiber a G G := by
  exact ⟨fun _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl, fun _ _ => rfl⟩

theorem SameFiber.symm {n : ℕ} {a : Finset (Fin n)} {G H : SimpleGraph (Fin n)}
    (h : SameFiber a G H) : SameFiber a H G := by
  exact ⟨fun u v hu hv => (h.1 u v hu hv).symm,
    fun u v hu hv => (h.2.1 u v hu hv).symm,
    fun w hw => (h.2.2 w hw).symm⟩

theorem SameFiber.trans {n : ℕ} {a : Finset (Fin n)} {G H K : SimpleGraph (Fin n)}
    (hGH : SameFiber a G H) (hHK : SameFiber a H K) : SameFiber a G K := by
  exact ⟨fun u v hu hv => (hGH.1 u v hu hv).trans (hHK.1 u v hu hv),
    fun u v hu hv => (hGH.2.1 u v hu hv).trans (hHK.2.1 u v hu hv),
    fun w hw => (hGH.2.2 w hw).trans (hHK.2.2 w hw)⟩

def stateSetoid {n : ℕ} (d : Fin n → ℕ) (a : Finset (Fin n)) :
    Setoid (GraphState n d) where
  r G H := SameFiber a G.val H.val
  iseqv := ⟨fun G => SameFiber.refl a G.val,
    fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

section Partition

variable {α : Type*} [Fintype α]

def constantSubspace (R : Setoid α) : Submodule ℝ (EuclideanSpace ℝ α) where
  carrier := {f | ∀ x y, R.r x y → f x = f y}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg x y hxy
    change f x + g x = f y + g y
    rw [hf x y hxy, hg x y hxy]
  smul_mem' := by
    intro c f hf x y hxy
    change c * f x = c * f y
    rw [hf x y hxy]

omit [Fintype α] in
@[simp] theorem mem_constantSubspace (R : Setoid α) (f : EuclideanSpace ℝ α) :
    f ∈ constantSubspace R ↔ ∀ x y, R.r x y → f x = f y := Iff.rfl

def expectation (R : Setoid α) : EuclideanSpace ℝ α →L[ℝ] EuclideanSpace ℝ α :=
  (constantSubspace R).starProjection

def deviation (R : Setoid α) : EuclideanSpace ℝ α →L[ℝ] EuclideanSpace ℝ α :=
  (constantSubspace R)ᗮ.starProjection

theorem expectation_mem (R : Setoid α) (f : EuclideanSpace ℝ α) :
    expectation R f ∈ constantSubspace R :=
  (constantSubspace R).starProjection_apply_mem f

theorem expectation_constant (R : Setoid α) (f : EuclideanSpace ℝ α)
    {x y : α} (hxy : R.r x y) : expectation R f x = expectation R f y :=
  expectation_mem R f x y hxy

theorem expectation_eq_self_iff (R : Setoid α) (f : EuclideanSpace ℝ α) :
    expectation R f = f ↔ ∀ x y, R.r x y → f x = f y :=
  Submodule.starProjection_eq_self_iff

theorem deviation_eq_sub (R : Setoid α) (f : EuclideanSpace ℝ α) :
    deviation R f = f - expectation R f := by
  simpa only [deviation, expectation, sub_apply,
    ContinuousLinearMap.id_apply] using
    congrArg (fun T : EuclideanSpace ℝ α →L[ℝ] EuclideanSpace ℝ α => T f)
      (Submodule.starProjection_orthogonal (constantSubspace R))

theorem deviation_eq_zero_iff (R : Setoid α) (f : EuclideanSpace ℝ α) :
    deviation R f = 0 ↔ ∀ x y, R.r x y → f x = f y := by
  rw [deviation_eq_sub, sub_eq_zero, eq_comm]
  exact expectation_eq_self_iff R f

theorem expectation_idempotent (R : Setoid α) (f : EuclideanSpace ℝ α) :
    expectation R (expectation R f) = expectation R f := by
  exact (expectation_eq_self_iff R _).2 (expectation_mem R f)

theorem deviation_idempotent (R : Setoid α) (f : EuclideanSpace ℝ α) :
    deviation R (deviation R f) = deviation R f := by
  apply Submodule.starProjection_eq_self_iff.mpr
  exact (constantSubspace R)ᗮ.starProjection_apply_mem f

theorem expectation_symmetric (R : Setoid α) :
    (expectation R).toLinearMap.IsSymmetric :=
  (constantSubspace R).starProjection_isSymmetric

theorem deviation_symmetric (R : Setoid α) :
    (deviation R).toLinearMap.IsSymmetric :=
  (constantSubspace R)ᗮ.starProjection_isSymmetric

theorem deviation_energy (R : Setoid α) (f : EuclideanSpace ℝ α) :
    inner ℝ f (deviation R f) = ‖deviation R f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  have h := deviation_symmetric R f (deviation R f)
  simpa only [ContinuousLinearMap.coe_coe, deviation_idempotent] using h.symm

theorem deviation_energy_nonneg (R : Setoid α) (f : EuclideanSpace ℝ α) :
    0 ≤ inner ℝ f (deviation R f) := by
  rw [deviation_energy]
  exact sq_nonneg _

def cell (R : Setoid α) (x : α) : Finset α :=
  Finset.univ.filter (fun y => R.r x y)

@[simp] theorem mem_cell (R : Setoid α) (x y : α) :
    y ∈ cell R x ↔ R.r x y := by simp [cell]

theorem cell_nonempty (R : Setoid α) (x : α) : (cell R x).Nonempty :=
  ⟨x, (mem_cell R x x).2 (R.refl x)⟩

theorem cell_eq (R : Setoid α) {x y : α} (hxy : R.r x y) : cell R x = cell R y := by
  ext z
  simp only [mem_cell]
  exact ⟨fun h => R.trans (R.symm hxy) h, fun h => R.trans hxy h⟩

def cellIndicator (R : Setoid α) (x : α) : EuclideanSpace ℝ α :=
  WithLp.toLp 2 (fun y => if R.r x y then 1 else 0)

omit [Fintype α] in
theorem cellIndicator_mem (R : Setoid α) (x : α) :
    cellIndicator R x ∈ constantSubspace R := by
  intro y z hyz
  change (if R.r x y then (1 : ℝ) else 0) = if R.r x z then 1 else 0
  have hiff : R.r x y ↔ R.r x z :=
    ⟨fun h => R.trans h hyz, fun h => R.trans h (R.symm hyz)⟩
  simp only [hiff]

theorem inner_cellIndicator (R : Setoid α) (x : α) (f : EuclideanSpace ℝ α) :
    inner ℝ f (cellIndicator R x) = ∑ y ∈ cell R x, f y := by
  simp [cellIndicator, PiLp.inner_apply, cell, Finset.sum_filter]

theorem expectation_apply (R : Setoid α) (f : EuclideanSpace ℝ α) (x : α) :
    expectation R f x = (∑ y ∈ cell R x, f y) / ((cell R x).card : ℝ) := by
  have hcNat : 0 < (cell R x).card := Finset.card_pos.mpr (cell_nonempty R x)
  have hc : (0 : ℝ) < (cell R x).card := by exact_mod_cast hcNat
  have horth := Submodule.starProjection_inner_eq_zero
    (K := constantSubspace R) f (cellIndicator R x) (cellIndicator_mem R x)
  change inner ℝ (f - expectation R f) (cellIndicator R x) = 0 at horth
  rw [inner_sub_left, inner_cellIndicator, inner_cellIndicator] at horth
  have hsum : (∑ y ∈ cell R x, expectation R f y) =
      (cell R x).card * expectation R f x := by
    calc
      (∑ y ∈ cell R x, expectation R f y) = ∑ _y ∈ cell R x, expectation R f x := by
        apply Finset.sum_congr rfl
        intro y hy
        exact (expectation_constant R f ((mem_cell R x y).1 hy)).symm
      _ = _ := by simp
  rw [hsum] at horth
  apply (eq_div_iff (ne_of_gt hc)).2
  nlinarith

end Partition

abbrev StateSpace (n : ℕ) (d : Fin n → ℕ) := EuclideanSpace ℝ (GraphState n d)

def pairExpectation {n : ℕ} (d : Fin n → ℕ) (a : Finset (Fin n)) :
    StateSpace n d →L[ℝ] StateSpace n d := expectation (stateSetoid d a)

def pairDeviation {n : ℕ} (d : Fin n → ℕ) (a : Finset (Fin n)) :
    StateSpace n d →L[ℝ] StateSpace n d := deviation (stateSetoid d a)

theorem pairDeviation_eq_zero_iff {n : ℕ} (d : Fin n → ℕ)
    (a : Finset (Fin n)) (f : StateSpace n d) :
    pairDeviation d a f = 0 ↔
      ∀ G H : GraphState n d, SameFiber a G.val H.val → f G = f H :=
  deviation_eq_zero_iff (stateSetoid d a) f

end Problem315.PairFibers

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairFibers.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/CellProjectionTransport.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.CellProjectionTransport

attribute [local instance] Classical.propDecidable

variable {α β : Type*} [sectionFintypeα : Fintype α] [sectionFintypeβ : Fintype β]

def restrictedSetoid (R : Setoid α) (C : α → Prop) : Setoid {x // C x} :=
  Setoid.comap Subtype.val R

def restrict (C : α → Prop) (f : EuclideanSpace ℝ α) :
    EuclideanSpace ℝ {x // C x} := WithLp.toLp 2 (fun x => f x.val)

include sectionFintypeα in
@[simp] theorem restrict_apply (C : α → Prop) (f : EuclideanSpace ℝ α)
    (x : {x // C x}) : restrict C f x = f x.val := by
  have retainedsectionFintypeα := sectionFintypeα
  exact rfl

def classEquiv (R : Setoid α) (C : α → Prop)
    (hC : ∀ x y, R.r x y → (C x ↔ C y)) (x : {x // C x}) :
    ↥(PairFibers.cell R x.val) ≃
      ↥(PairFibers.cell (restrictedSetoid R C) x) where
  toFun y := ⟨⟨y.val, (hC x.val y.val
    ((PairFibers.mem_cell R x.val y.val).mp y.property)).mp x.property⟩,
    (PairFibers.mem_cell _ _ _).mpr ((PairFibers.mem_cell R x.val y.val).mp y.property)⟩
  invFun y := ⟨y.val.val, (PairFibers.mem_cell R x.val y.val.val).mpr
    ((PairFibers.mem_cell (restrictedSetoid R C) x y.val).mp y.property)⟩
  left_inv y := by apply Subtype.ext; rfl
  right_inv y := by apply Subtype.ext; rfl

theorem expectation_restrict (R : Setoid α) (C : α → Prop)
    (hC : ∀ x y, R.r x y → (C x ↔ C y)) (f : EuclideanSpace ℝ α) :
    restrict C (PairFibers.expectation R f) =
      PairFibers.expectation (restrictedSetoid R C) (restrict C f) := by
  ext x
  simp only [restrict_apply, PairFibers.expectation_apply]
  have hc : (PairFibers.cell R x.val).card =
      (PairFibers.cell (restrictedSetoid R C) x).card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr (classEquiv R C hC x)
  rw [hc]
  congr 1
  calc
    (∑ y ∈ PairFibers.cell R x.val, f y) =
        ∑ y : PairFibers.cell R x.val, f y.val :=
      (Finset.sum_coe_sort _ _).symm
    _ = ∑ y : PairFibers.cell (restrictedSetoid R C) x, f y.val.val :=
      (classEquiv R C hC x).sum_comp (fun y => f y.val.val)
    _ = ∑ y ∈ PairFibers.cell (restrictedSetoid R C) x, f y.val :=
      Finset.sum_coe_sort (PairFibers.cell (restrictedSetoid R C) x) (fun y => f y.val)

def pull (e : α ≃ β) (f : EuclideanSpace ℝ β) : EuclideanSpace ℝ α :=
  WithLp.toLp 2 (fun x => f (e x))

include sectionFintypeα sectionFintypeβ in
@[simp] theorem pull_apply (e : α ≃ β) (f : EuclideanSpace ℝ β) (x : α) :
    pull e f x = f (e x) := by
  have retainedsectionFintypeα := sectionFintypeα
  have retainedsectionFintypeβ := sectionFintypeβ
  exact rfl

include sectionFintypeα sectionFintypeβ in
@[simp] theorem pull_symm (e : α ≃ β) (f : EuclideanSpace ℝ α) :
    pull e (pull e.symm f) = f := by
  have retainedsectionFintypeα := sectionFintypeα
  have retainedsectionFintypeβ := sectionFintypeβ
  ext x
  simp [pull]

def equivClass (e : α ≃ β) (R : Setoid α) (S : Setoid β)
    (he : ∀ x y, R.r x y ↔ S.r (e x) (e y)) (x : α) :
    ↥(PairFibers.cell R x) ≃ ↥(PairFibers.cell S (e x)) where
  toFun y := ⟨e y.val, (PairFibers.mem_cell _ _ _).mpr
    ((he x y.val).mp ((PairFibers.mem_cell _ _ _).mp y.property))⟩
  invFun y := ⟨e.symm y.val, (PairFibers.mem_cell _ _ _).mpr
    ((he x (e.symm y.val)).mpr (by
      simpa only [e.apply_symm_apply] using
        ((PairFibers.mem_cell S (e x) y.val).mp y.property)))⟩
  left_inv y := by apply Subtype.ext; exact e.symm_apply_apply y.val
  right_inv y := by apply Subtype.ext; exact e.apply_symm_apply y.val

theorem expectation_pull (e : α ≃ β) (R : Setoid α) (S : Setoid β)
    (he : ∀ x y, R.r x y ↔ S.r (e x) (e y)) (f : EuclideanSpace ℝ β) :
    PairFibers.expectation R (pull e f) = pull e (PairFibers.expectation S f) := by
  ext x
  simp only [pull_apply, PairFibers.expectation_apply]
  have hc : (PairFibers.cell R x).card = (PairFibers.cell S (e x)).card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr (equivClass e R S he x)
  rw [hc]
  congr 1
  calc
    (∑ y ∈ PairFibers.cell R x, f (e y)) =
        ∑ y : PairFibers.cell R x, f (e y.val) :=
      (Finset.sum_coe_sort _ _).symm
    _ = ∑ y : PairFibers.cell S (e x), f y.val :=
      (equivClass e R S he x).sum_comp (fun y => f y.val)
    _ = ∑ y ∈ PairFibers.cell S (e x), f y :=
      Finset.sum_coe_sort _ _

theorem inner_pull (e : α ≃ β) (f g : EuclideanSpace ℝ β) :
    ⟪pull e f, pull e g⟫ = ⟪f, g⟫ := by
  simp only [PiLp.inner_apply, pull_apply]
  exact e.sum_comp (fun x => inner ℝ (f x) (g x))

@[simp] theorem norm_sq_pull (e : α ≃ β) (f : EuclideanSpace ℝ β) :
    ‖pull e f‖ ^ 2 = ‖f‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using inner_pull e f f

@[simp] theorem expectation_constant (R : Setoid α) (c : ℝ) :
    PairFibers.expectation R (WithLp.toLp 2 (fun _ : α => c)) =
      WithLp.toLp 2 (fun _ : α => c) := by
  apply (PairFibers.expectation_eq_self_iff R _).mpr
  intro x y hxy
  rfl

theorem sum_expectation (R : Setoid α) (f : EuclideanSpace ℝ α) :
    (∑ x, PairFibers.expectation R f x) = ∑ x, f x := by
  let one : EuclideanSpace ℝ α := WithLp.toLp 2 (fun _ => 1)
  have h := PairFibers.expectation_symmetric R f one
  change ⟪PairFibers.expectation R f, one⟫ =
    ⟪f, PairFibers.expectation R one⟫ at h
  rw [show PairFibers.expectation R one = one from expectation_constant R 1] at h
  simpa [PiLp.inner_apply, one] using h

theorem expectation_centered (R : Setoid α) (f : EuclideanSpace ℝ α)
    (hf : ∑ x, f x = 0) : ∑ x, PairFibers.expectation R f x = 0 := by
  rw [sum_expectation, hf]

theorem sum_pull (e : α ≃ β) (f : EuclideanSpace ℝ β) :
    (∑ x, pull e f x) = ∑ y, f y := e.sum_comp f

variable {n : ℕ} {d : Fin n → ℕ}

def graphSetoid (a : Finset (Fin n)) : Setoid (GraphState n d) where
  r G H := PairResampling.SameFiber a G.val H.val
  iseqv := ⟨fun G => PairResampling.SameFiber.refl a G.val,
    fun h => h.symm, fun h k => h.trans k⟩

theorem graph_expectation (a : Finset (Fin n)) :
    PairFibers.expectation (graphSetoid (d := d) a) = PairResampling.expectation n d a := by
  have h : PairFibers.constantSubspace (graphSetoid (d := d) a) =
      PairResampling.fiberSpace n d a := by
    ext f
    rfl
  unfold PairFibers.expectation PairResampling.expectation
  simp only [h]

theorem graph_expectation_restrict (a : Finset (Fin n)) (C : GraphState n d → Prop)
    (hC : ∀ G H, PairResampling.SameFiber a G.val H.val → (C G ↔ C H))
    (f : PairResampling.StateSpace n d) :
    restrict C (PairResampling.expectation n d a f) =
      PairFibers.expectation (restrictedSetoid (graphSetoid a) C) (restrict C f) := by
  rw [← graph_expectation]
  exact expectation_restrict (graphSetoid a) C hC f

theorem graph_expectation_equiv (a : Finset (Fin n)) (C : GraphState n d → Prop)
    (hC : ∀ G H, PairResampling.SameFiber a G.val H.val → (C G ↔ C H))
    (e : {G // C G} ≃ β) (S : Setoid β)
    (he : ∀ G H : {G // C G},
      PairResampling.SameFiber a G.val.val H.val.val ↔ S.r (e G) (e H))
    (f : PairResampling.StateSpace n d) :
    restrict C (PairResampling.expectation n d a f) =
      pull e (PairFibers.expectation S (pull e.symm (restrict C f))) := by
  rw [graph_expectation_restrict a C hC]
  have h := expectation_pull e (restrictedSetoid (graphSetoid a) C) S he
    (pull e.symm (restrict C f))
  simpa only [pull_symm] using h

end Problem315.CellProjectionTransport

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/CellProjectionTransport.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/TripleProjectionBridge.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.TripleProjectionBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem projection_sum_bound {ι : Type*} [Fintype ι]
    (x : E) (y : ι → E)
    (horth : ∀ i, ⟪x, y i⟫ = ‖y i‖ ^ 2)
    (hvar : ‖∑ i, y i‖ ^ 2 ≤ 2 * ∑ i, ‖y i‖ ^ 2) :
    (∑ i, ‖y i‖ ^ 2) ≤ 2 * ‖x‖ ^ 2 := by
  have hi : ⟪x, ∑ i, y i⟫ = ∑ i, ‖y i‖ ^ 2 := by
    simp [inner_sum, horth]
  have hnorm := sq_nonneg ‖(2 : ℝ) • x - ∑ i, y i‖
  rw [norm_sub_sq_real] at hnorm
  norm_num [norm_smul, inner_smul_left, hi] at hnorm
  nlinarith

theorem triple_gap_of_row_variance (x : E) (y : Fin 3 → E)
    (horth : ∀ i, ⟪x, y i⟫ = ‖y i‖ ^ 2)
    (hvar : ‖∑ i, y i‖ ^ 2 ≤ 2 * ∑ i, ‖y i‖ ^ 2) :
    ‖x‖ ^ 2 ≤ ⟪x, ∑ i, (x - y i)⟫ := by
  have hb := projection_sum_bound x y horth hvar
  have hi : ⟪x, ∑ i, (x - y i)⟫ =
      3 * ‖x‖ ^ 2 - ∑ i, ‖y i‖ ^ 2 := by
    rw [inner_sum]
    simp only [inner_sub_right, horth, real_inner_self_eq_norm_sq]
    rw [Finset.sum_sub_distrib]
    simp
  rw [hi]
  linarith

theorem square_bound_of_unit_gap (x z : E) (hgap : ‖x‖ ^ 2 ≤ ⟪x, z⟫) :
    ⟪x, z⟫ ≤ ‖z‖ ^ 2 := by
  have hnorm := sq_nonneg ‖x - z‖
  rw [norm_sub_sq_real] at hnorm
  linarith

theorem triple_square_of_row_variance (x : E) (y : Fin 3 → E)
    (horth : ∀ i, ⟪x, y i⟫ = ‖y i‖ ^ 2)
    (hvar : ‖∑ i, y i‖ ^ 2 ≤ 2 * ∑ i, ‖y i‖ ^ 2) :
    ⟪x, ∑ i, (x - y i)⟫ ≤ ‖∑ i, (x - y i)‖ ^ 2 :=
  square_bound_of_unit_gap x _ (triple_gap_of_row_variance x y horth hvar)

theorem triple_square_of_centered_row_variance
    (P : Fin 3 → E →ₗ[ℝ] E) (C : E → E)
    (hsymm : ∀ i, (P i).IsSymmetric)
    (hidem : ∀ i x, P i (P i x) = P i x)
    (hfix : ∀ i x, P i (C x) = C x)
    (hvar : ∀ x, ‖∑ i, P i (x - C x)‖ ^ 2 ≤
      2 * ∑ i, ‖P i (x - C x)‖ ^ 2) :
    ∀ x, ⟪x, ∑ i, (x - P i x)⟫ ≤ ‖∑ i, (x - P i x)‖ ^ 2 := by
  intro x
  have horth : ∀ i, ⟪x - C x, P i (x - C x)⟫ =
      ‖P i (x - C x)‖ ^ 2 := by
    intro i
    have hi := hsymm i (x - C x) (P i (x - C x))
    rw [hidem] at hi
    rw [← hi, real_inner_self_eq_norm_sq]
  have heq : (∑ i, ((x - C x) - P i (x - C x))) =
      ∑ i, (x - P i x) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_sub, hfix]
    abel
  have hzero : ⟪C x, ∑ i, (x - P i x)⟫ = 0 := by
    rw [inner_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [inner_sub_right, ← hsymm i (C x) x, hfix, sub_self]
  have h := triple_square_of_row_variance (x - C x)
    (fun i => P i (x - C x)) horth (hvar x)
  rw [heq, inner_sub_left, hzero, sub_zero] at h
  exact h

end Problem315.TripleProjectionBridge

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/TripleProjectionBridge.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairTripleBridge.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
attribute [local instance] Classical.propDecidable

namespace Problem315.TripleProjectionBridge

theorem square_of_card_three_centered_row_variance
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hcard : Fintype.card ι = 3) (P : ι → E →ₗ[ℝ] E) (C : E → E)
    (hsymm : ∀ i, (P i).IsSymmetric)
    (hidem : ∀ i x, P i (P i x) = P i x)
    (hfix : ∀ i x, P i (C x) = C x)
    (hvar : ∀ x, ‖∑ i, P i (x - C x)‖ ^ 2 ≤
      2 * ∑ i, ‖P i (x - C x)‖ ^ 2) :
    ∀ x, ⟪x, ∑ i, (x - P i x)⟫ ≤ ‖∑ i, (x - P i x)‖ ^ 2 := by
  let e : ι ≃ Fin 3 := Fintype.equivFinOfCardEq hcard
  have hv : ∀ x, ‖∑ j : Fin 3, P (e.symm j) (x - C x)‖ ^ 2 ≤
      2 * ∑ j : Fin 3, ‖P (e.symm j) (x - C x)‖ ^ 2 := by
    intro x
    rw [e.symm.sum_comp (fun i => P i (x - C x)),
      e.symm.sum_comp (fun i => ‖P i (x - C x)‖ ^ 2)]
    exact hvar x
  have h := triple_square_of_centered_row_variance
    (fun j => P (e.symm j)) C (fun j => hsymm (e.symm j))
    (fun j => hidem (e.symm j)) (fun j => hfix (e.symm j)) hv
  intro x
  simpa only [e.symm.sum_comp (fun i => x - P i x)] using h x

end Problem315.TripleProjectionBridge

namespace Problem315.PairResampling

theorem triple_fluctuation_square_of_row_variance
    {n : ℕ} {d : Fin n → ℕ} {ι : Type*} [Fintype ι]
    (hcard : Fintype.card ι = 3) (a : ι → Finset (Fin n))
    (C : StateSpace n d → StateSpace n d)
    (hfix : ∀ i f, expectation n d (a i) (C f) = C f)
    (hvar : ∀ f, ‖∑ i, expectation n d (a i) (f - C f)‖ ^ 2 ≤
      2 * ∑ i, ‖expectation n d (a i) (f - C f)‖ ^ 2) :
    ∀ f, ⟪f, ∑ i, fluctuation n d (a i) f⟫ ≤
      ‖∑ i, fluctuation n d (a i) f‖ ^ 2 := by
  have h := TripleProjectionBridge.square_of_card_three_centered_row_variance
    hcard (fun i => (expectation n d (a i)).toLinearMap) C
    (fun i => expectation_isSymmetric (a i))
    (fun i => expectation_idempotent (a i)) hfix hvar
  intro f
  simpa only [fluctuation_eq_sub, ContinuousLinearMap.coe_coe] using h f

theorem vertex_triple_square_of_row_variance
    {n : ℕ} {d : Fin n → ℕ} (T : Finset (Fin n)) (hT : T.card = 3)
    (C : StateSpace n d → StateSpace n d)
    (hfix : ∀ a ∈ T.powersetCard 2, ∀ f, expectation n d a (C f) = C f)
    (hvar : ∀ f, ‖∑ a ∈ T.powersetCard 2, expectation n d a (f - C f)‖ ^ 2 ≤
      2 * ∑ a ∈ T.powersetCard 2, ‖expectation n d a (f - C f)‖ ^ 2) :
    ∀ f, ⟪f, ∑ a ∈ T.powersetCard 2, fluctuation n d a f⟫ ≤
      ‖∑ a ∈ T.powersetCard 2, fluctuation n d a f‖ ^ 2 := by
  classical
  have hc : Fintype.card (T.powersetCard 2) = 3 := by
    rw [Fintype.card_coe, Finset.card_powersetCard, hT]
    norm_num
  have hv : ∀ f, ‖∑ a : T.powersetCard 2, expectation n d a.val (f - C f)‖ ^ 2 ≤
      2 * ∑ a : T.powersetCard 2, ‖expectation n d a.val (f - C f)‖ ^ 2 := by
    intro f
    rw [Finset.sum_coe_sort (T.powersetCard 2) (fun a => expectation n d a (f - C f)),
      Finset.sum_coe_sort (T.powersetCard 2) (fun a => ‖expectation n d a (f - C f)‖ ^ 2)]
    exact hvar f
  have h := triple_fluctuation_square_of_row_variance hc
    (fun a : T.powersetCard 2 => a.val) C (fun a => hfix a.val a.property) hv
  intro f
  simpa only [Finset.sum_coe_sort (T.powersetCard 2)
    (fun a => fluctuation n d a f)] using h f

end Problem315.PairResampling

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairTripleBridge.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/TripleCellVarianceGluing.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
attribute [local instance] Classical.propDecidable

namespace Problem315.CellVarianceGluing

variable {α κ : Type*} [sectionFintypeα : Fintype α] [sectionFintypeκ : Fintype κ]

def restrict (key : α → κ) (k : κ) :
    EuclideanSpace ℝ α →ₗ[ℝ] EuclideanSpace ℝ {x // key x = k} where
  toFun f := WithLp.toLp 2 (fun x => f x.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

include sectionFintypeα sectionFintypeκ in
@[simp] theorem restrict_apply (key : α → κ) (k : κ)
    (f : EuclideanSpace ℝ α) (x : {x // key x = k}) :
    restrict key k f x = f x.val := by
  have retainedsectionFintypeα := sectionFintypeα
  have retainedsectionFintypeκ := sectionFintypeκ
  exact rfl

theorem norm_sq_eq_sum_restrict (key : α → κ) (f : EuclideanSpace ℝ α) :
    ‖f‖ ^ 2 = ∑ k, ‖restrict key k f‖ ^ 2 := by
  classical
  simp only [EuclideanSpace.norm_sq_eq]
  exact (Fintype.sum_fiberwise key (fun x => ‖f x‖ ^ 2)).symm

theorem norm_sum_sq_le_of_cells {ι : Type*} [Fintype ι]
    (key : α → κ) (y : ι → EuclideanSpace ℝ α) (c : ℝ)
    (hlocal : ∀ k, ‖∑ i, restrict key k (y i)‖ ^ 2 ≤
      c * ∑ i, ‖restrict key k (y i)‖ ^ 2) :
    ‖∑ i, y i‖ ^ 2 ≤ c * ∑ i, ‖y i‖ ^ 2 := by
  calc
    _ = ∑ k, ‖∑ i, restrict key k (y i)‖ ^ 2 := by
      rw [norm_sq_eq_sum_restrict key]
      simp only [map_sum]
    _ ≤ ∑ k, c * ∑ i, ‖restrict key k (y i)‖ ^ 2 :=
      Finset.sum_le_sum (fun k _ => hlocal k)
    _ = c * ∑ i, ‖y i‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => (norm_sq_eq_sum_restrict key (y i)).symm)

def cellSpace (key : α → κ) : Submodule ℝ (EuclideanSpace ℝ α) where
  carrier := {f | ∀ x y, key x = key y → f x = f y}
  zero_mem' := by intro x y h; rfl
  add_mem' := by
    intro f g hf hg x y h
    change f x + g x = f y + g y
    rw [hf x y h, hg x y h]
  smul_mem' := by
    intro c f hf x y h
    change c * f x = c * f y
    rw [hf x y h]

def center (key : α → κ) : EuclideanSpace ℝ α →L[ℝ] EuclideanSpace ℝ α :=
  (cellSpace key).starProjection

include sectionFintypeκ in
theorem center_mem (key : α → κ) (f : EuclideanSpace ℝ α) :
    center key f ∈ cellSpace key := by
  have retainedsectionFintypeκ := sectionFintypeκ
  exact (cellSpace key).starProjection_apply_mem f

include sectionFintypeκ in
theorem sum_restrict_sub_center_eq_zero (key : α → κ) (k : κ)
    (f : EuclideanSpace ℝ α) :
    ∑ x : {x // key x = k}, restrict key k (f - center key f) x = 0 := by
  have retainedsectionFintypeκ := sectionFintypeκ
  classical
  let indicator : EuclideanSpace ℝ α :=
    WithLp.toLp 2 (fun x => if key x = k then 1 else 0)
  have hmem : indicator ∈ cellSpace key := by
    intro x y h
    change (if key x = k then (1 : ℝ) else 0) =
      (if key y = k then (1 : ℝ) else 0)
    rw [h]
  have horth := Submodule.starProjection_inner_eq_zero
    (K := cellSpace key) f indicator hmem
  change ⟪f - center key f, indicator⟫ = 0 at horth
  have horth' : (∑ x, if key x = k then (f - center key f) x else 0) = 0 := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, indicator,
      mul_ite] using horth
  have hsum : (∑ x ∈ Finset.univ.filter (fun x => key x = k),
      (f - center key f) x) = 0 := by
    simpa only [Finset.sum_filter] using horth'
  rw [Finset.sum_subtype (p := fun x => key x = k) _ (fun x => by simp)] at hsum
  exact hsum

theorem centered_row_variance_of_cells {ι : Type*} [Fintype ι]
    (key : α → κ) (P : ι → EuclideanSpace ℝ α →ₗ[ℝ] EuclideanSpace ℝ α)
    (Q : ∀ k, ι → EuclideanSpace ℝ {x // key x = k} →ₗ[ℝ]
      EuclideanSpace ℝ {x // key x = k})
    (htransport : ∀ i k f, restrict key k (P i f) = Q k i (restrict key k f))
    (c : ℝ)
    (hlocal : ∀ k (g : EuclideanSpace ℝ {x // key x = k}),
      (∑ x, g x) = 0 → ‖∑ i, Q k i g‖ ^ 2 ≤ c * ∑ i, ‖Q k i g‖ ^ 2)
    (f : EuclideanSpace ℝ α) :
    ‖∑ i, P i (f - center key f)‖ ^ 2 ≤
      c * ∑ i, ‖P i (f - center key f)‖ ^ 2 := by
  apply norm_sum_sq_le_of_cells key
  intro k
  simp only [htransport]
  exact hlocal k _ (sum_restrict_sub_center_eq_zero key k f)

end Problem315.CellVarianceGluing

namespace Problem315.PairResampling
open CellVarianceGluing

theorem expectation_center_of_key_invariant
    {n : ℕ} {d : Fin n → ℕ} {κ : Type*} [Fintype κ]
    (key : GraphState n d → κ) (a : Finset (Fin n))
    (hkey : ∀ G H : GraphState n d, SameFiber a G.val H.val → key G = key H)
    (f : StateSpace n d) : expectation n d a (center key f) = center key f := by
  apply (expectation_eq_self_iff a _).mpr
  intro G H h
  exact center_mem key f G H (hkey G H h)

theorem vertex_triple_square_of_cellwise_row_variance
    {n : ℕ} {d : Fin n → ℕ} {κ : Type*} [Fintype κ]
    (T : Finset (Fin n)) (hT : T.card = 3)
    (key : GraphState n d → κ)
    (hkey : ∀ a ∈ T.powersetCard 2, ∀ G H : GraphState n d,
      SameFiber a G.val H.val → key G = key H)
    (hlocal : ∀ k (f : StateSpace n d),
      ‖∑ a : T.powersetCard 2,
        restrict key k (expectation n d a.val (f - center key f))‖ ^ 2 ≤
      2 * ∑ a : T.powersetCard 2,
        ‖restrict key k (expectation n d a.val (f - center key f))‖ ^ 2) :
    ∀ f, ⟪f, ∑ a ∈ T.powersetCard 2, fluctuation n d a f⟫ ≤
      ‖∑ a ∈ T.powersetCard 2, fluctuation n d a f‖ ^ 2 := by
  apply vertex_triple_square_of_row_variance T hT (center key)
  · intro a ha f
    exact expectation_center_of_key_invariant key a (hkey a ha) f
  · intro f
    have h := norm_sum_sq_le_of_cells key
      (fun a : T.powersetCard 2 => expectation n d a.val (f - center key f)) 2
      (fun k => hlocal k f)
    simpa only [Finset.sum_coe_sort (T.powersetCard 2)
      (fun a => expectation n d a (f - center key f)),
      Finset.sum_coe_sort (T.powersetCard 2)
      (fun a => ‖expectation n d a (f - center key f)‖ ^ 2)] using h

end Problem315.PairResampling

namespace Problem315.PairResampling
open CellVarianceGluing

def tripleExteriorKey {n : ℕ} {d : Fin n → ℕ} (T : Finset (Fin n))
    (G : GraphState n d) : SimpleGraph {v : Fin n // v ∉ T} :=
  G.val.comap Subtype.val

theorem tripleExteriorKey_eq_of_sameFiber {n : ℕ} {d : Fin n → ℕ}
    {T a : Finset (Fin n)} (ha : a ⊆ T) (G H : GraphState n d)
    (h : SameFiber a G.val H.val) : tripleExteriorKey T G = tripleExteriorKey T H := by
  ext u v
  exact h.1 u.val (fun hu => u.property (ha hu))
    v.val (fun hv => v.property (ha hv))

theorem expectation_tripleExterior_center {n : ℕ} {d : Fin n → ℕ}
    {T a : Finset (Fin n)} (ha : a ⊆ T) (f : StateSpace n d) :
    expectation n d a (center (tripleExteriorKey T) f) =
      center (tripleExteriorKey T) f := by
  exact expectation_center_of_key_invariant (tripleExteriorKey T) a
    (fun G H h => tripleExteriorKey_eq_of_sameFiber ha G H h) f

theorem vertex_triple_square_of_exterior_cellwise_row_variance
    {n : ℕ} {d : Fin n → ℕ}
    (T : Finset (Fin n)) (hT : T.card = 3)
    (hlocal : ∀ (k : SimpleGraph {v : Fin n // v ∉ T}) (f : StateSpace n d),
      ‖∑ a : T.powersetCard 2,
        restrict (tripleExteriorKey T) k
          (expectation n d a.val (f - center (tripleExteriorKey T) f))‖ ^ 2 ≤
      2 * ∑ a : T.powersetCard 2,
        ‖restrict (tripleExteriorKey T) k
          (expectation n d a.val (f - center (tripleExteriorKey T) f))‖ ^ 2) :
    ∀ f, ⟪f, ∑ a ∈ T.powersetCard 2, fluctuation n d a f⟫ ≤
      ‖∑ a ∈ T.powersetCard 2, fluctuation n d a f‖ ^ 2 := by
  apply vertex_triple_square_of_cellwise_row_variance T hT (tripleExteriorKey T) _ hlocal
  intro a ha G H h
  exact tripleExteriorKey_eq_of_sameFiber (Finset.mem_powersetCard.mp ha).1 G H h

end Problem315.PairResampling

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/TripleCellVarianceGluing.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/FiniteVarianceEuclidean.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.FiniteVariance

open FixedBlockMarginal (average)

variable {X I : Type*} [Fintype X] [Fintype I]

theorem average_square_eq_norm_sq_div_card (f : X → ℝ) :
    average (fun x => (f x) ^ 2) =
      ‖WithLp.toLp 2 f‖ ^ 2 / (Fintype.card X : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

theorem variance_eq_centered_norm_sq_div_card (f : X → ℝ) :
    variance f =
      ‖WithLp.toLp 2 (fun x => f x - average f)‖ ^ 2 /
        (Fintype.card X : ℝ) :=
  average_square_eq_norm_sq_div_card _

theorem variance_eq_norm_sq_div_card_of_average_zero
    (f : EuclideanSpace ℝ X) (hf : average (fun x => f x) = 0) :
    variance (fun x => f x) = ‖f‖ ^ 2 / (Fintype.card X : ℝ) := by
  rw [variance_eq_centered_norm_sq_div_card, hf]
  simp only [sub_zero, WithLp.toLp_ofLp]

theorem norm_sum_sq_le_of_variance_bound [Nonempty X]
    (y : I → EuclideanSpace ℝ X) (c : ℝ)
    (hcenter : ∀ i, average (fun x => y i x) = 0)
    (hvar : variance (fun x => ∑ i, y i x) ≤
      c * ∑ i, variance (fun x => y i x)) :
    ‖∑ i, y i‖ ^ 2 ≤ c * ∑ i, ‖y i‖ ^ 2 := by
  have hcard : (0 : ℝ) < Fintype.card X := by
    exact_mod_cast Fintype.card_pos
  have hsum : average (fun x => (∑ i, y i) x) = 0 := by
    simp only [WithLp.ofLp_sum, Finset.sum_apply, average_sum, hcenter, Finset.sum_const_zero]
  have hleft := variance_eq_norm_sq_div_card_of_average_zero (∑ i, y i) hsum
  have hright (i : I) := variance_eq_norm_sq_div_card_of_average_zero (y i) (hcenter i)
  simp only [WithLp.ofLp_sum, Finset.sum_apply] at hleft
  rw [hleft] at hvar
  simp_rw [hright] at hvar
  rw [← Finset.sum_div, ← mul_div_assoc] at hvar
  exact (div_le_div_iff_of_pos_right hcard).mp hvar

end Problem315.FiniteVariance

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/FiniteVarianceEuclidean.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/TripleActualRowBound.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.TripleActualRowBound

open TripleCellTransport TripleInternalEncoding
attribute [local instance] Classical.propDecidable

theorem row_variance_transport {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
    (e : X ≃ Y) (f : I → X → ℝ)
    (h : FiniteVariance.variance (fun y => ∑ i, f i (e.symm y)) ≤
      2 * ∑ i, FiniteVariance.variance (fun y => f i (e.symm y))) :
    FiniteVariance.variance (fun x => ∑ i, f i x) ≤
      2 * ∑ i, FiniteVariance.variance (f i) := by
  have hl := FiniteVariance.variance_equiv e.symm (fun x => ∑ i, f i x)
  have hr (i : I) := FiniteVariance.variance_equiv e.symm (f i)
  rw [hl] at h
  simp_rw [hr] at h
  exact h

theorem full_matrix_row_variance_transport {X C : Type*} [Fintype X] [Fintype C]
    [Nonempty X] (k : C → ℕ) (r : Fin 3 → ℕ)
    (e : X ≃ ForcedColumns.FullMargins k r) (f : Fin 3 → X → ℝ)
    (hf : ∀ i x y, (e x).val i = (e y).val i → f i x = f i y) :
    FiniteVariance.variance (fun x => ∑ i, f i x) ≤
      2 * ∑ i, FiniteVariance.variance (f i) := by
  apply row_variance_transport e f
  apply MatrixRowVariance.row_variance_bound k r ⟨e (Classical.choice inferInstance)⟩
  intro i M N hMN
  apply hf i
  simpa only [e.apply_symm_apply] using hMN

variable {n : ℕ} {d : Fin n → ℕ}
variable (T : Finset (Fin n)) (hT : T.card = 3)

def finiteCellEquiv (G : GraphState n d) : Cell T hT G ≃
    ForcedColumns.FullMargins
      (TripleMatrixFinEquiv.margins
        (internalEdgeCount (internalGraph (splitGraph T hT G)))
        (crossColumn (splitGraph T hT G)))
      (fun i => leftDegree (splitGraph T hT G) i -
        rowOffset (internalEdgeCount (internalGraph (splitGraph T hT G)))) :=
   (matrixEquiv T hT G).trans
    (TripleMatrixFinEquiv.augmentedEquiv
      (internalEdgeCount (internalGraph (splitGraph T hT G)))
      (leftDegree (splitGraph T hT G)) (crossColumn (splitGraph T hT G)))

theorem finiteCell_row_iff (G : GraphState n d) (H K : Cell T hT G) (i : Fin 3) :
    (finiteCellEquiv T hT G H).val i = (finiteCellEquiv T hT G K).val i ↔
      PairResampling.SameFiber (pair T hT i) H.val.val K.val.val := by
  change (TripleMatrixFinEquiv.augmentedEquiv _ _ _ (matrixEquiv T hT G H)).val i =
    (TripleMatrixFinEquiv.augmentedEquiv _ _ _ (matrixEquiv T hT G K)).val i ↔ _
  rw [TripleMatrixFinEquiv.augmented_row_eq_iff]
  exact (sameFiber_iff_matrixRow T hT G H K i).symm

theorem cell_row_variance (G : GraphState n d)
    (f : Fin 3 → Cell T hT G → ℝ)
    (hf : ∀ i H K, PairResampling.SameFiber (pair T hT i) H.val.val K.val.val →
      f i H = f i K) :
    FiniteVariance.variance (fun H => ∑ i, f i H) ≤
      2 * ∑ i, FiniteVariance.variance (f i) := by
  let : Nonempty (Cell T hT G) := ⟨referenceCell T hT G⟩
  apply full_matrix_row_variance_transport _ _ (finiteCellEquiv T hT G) f
  intro i H K hHK
  exact hf i H K ((finiteCell_row_iff T hT G H K i).mp hHK)

def exteriorCellEquiv (G : GraphState n d) :
    {H : GraphState n d // PairResampling.tripleExteriorKey T H =
      PairResampling.tripleExteriorKey T G} ≃ Cell T hT G :=
  outsideCellEquiv T hT G

theorem exterior_row_variance (G : GraphState n d)
    (f : Fin 3 → {H : GraphState n d // PairResampling.tripleExteriorKey T H =
      PairResampling.tripleExteriorKey T G} → ℝ)
    (hf : ∀ i H K, PairResampling.SameFiber (pair T hT i) H.val.val K.val.val →
      f i H = f i K) :
    FiniteVariance.variance (fun H => ∑ i, f i H) ≤
      2 * ∑ i, FiniteVariance.variance (f i) := by
  let e := exteriorCellEquiv T hT G
  apply row_variance_transport e f
  apply cell_row_variance T hT G
  intro i H K hHK
  exact hf i (e.symm H) (e.symm K) hHK

theorem sum_expectation_exterior (a : Finset (Fin n)) (ha : a ⊆ T)
    (k : SimpleGraph {v : Fin n // v ∉ T}) (f : PairResampling.StateSpace n d) :
    (∑ H : {H : GraphState n d // PairResampling.tripleExteriorKey T H = k},
      PairResampling.expectation n d a f H.val) =
    ∑ H : {H : GraphState n d // PairResampling.tripleExteriorKey T H = k}, f H.val := by
  let C := fun H : GraphState n d => PairResampling.tripleExteriorKey T H = k
  have hc : ∀ G H : GraphState n d, PairResampling.SameFiber a G.val H.val →
      (C G ↔ C H) := by
    intro G H h
    dsimp [C]
    rw [PairResampling.tripleExteriorKey_eq_of_sameFiber ha G H h]
  have he := CellProjectionTransport.graph_expectation_restrict a C hc f
  have hs := CellProjectionTransport.sum_expectation
    (CellProjectionTransport.restrictedSetoid (CellProjectionTransport.graphSetoid a) C)
    (CellProjectionTransport.restrict C f)
  rw [← he] at hs
  exact hs

theorem exterior_projection_norm_centered (G : GraphState n d)
    (f : PairResampling.StateSpace n d)
    (hf : (∑ H : {H : GraphState n d // PairResampling.tripleExteriorKey T H =
      PairResampling.tripleExteriorKey T G}, f H.val) = 0) :
    ‖∑ i : Fin 3, CellVarianceGluing.restrict (PairResampling.tripleExteriorKey T)
      (PairResampling.tripleExteriorKey T G)
      (PairResampling.expectation n d (pair T hT i) f)‖ ^ 2 ≤
    2 * ∑ i : Fin 3, ‖CellVarianceGluing.restrict (PairResampling.tripleExteriorKey T)
      (PairResampling.tripleExteriorKey T G)
      (PairResampling.expectation n d (pair T hT i) f)‖ ^ 2 := by
  let : Nonempty {H : GraphState n d // PairResampling.tripleExteriorKey T H =
      PairResampling.tripleExteriorKey T G} := ⟨⟨G, rfl⟩⟩
  apply FiniteVariance.norm_sum_sq_le_of_variance_bound
  · intro i
    unfold FixedBlockMarginal.average
    change (∑ H : {H : GraphState n d // PairResampling.tripleExteriorKey T H =
      PairResampling.tripleExteriorKey T G},
      PairResampling.expectation n d (pair T hT i) f H.val) / _ = 0
    rw [sum_expectation_exterior T (pair T hT i)
      (Finset.mem_powersetCard.mp (pair_mem_powersetCard T hT i)).1, hf, zero_div]
  · apply exterior_row_variance T hT G
    intro i H K hHK
    exact PairResampling.expectation_mem (pair T hT i) f H.val K.val hHK

include hT in

theorem triple_square (f : PairResampling.StateSpace n d) :
    ⟪f, ∑ a ∈ T.powersetCard 2, PairResampling.fluctuation n d a f⟫ ≤
      ‖∑ a ∈ T.powersetCard 2, PairResampling.fluctuation n d a f‖ ^ 2 := by
  apply PairResampling.vertex_triple_square_of_exterior_cellwise_row_variance T hT
  intro k g
  by_cases hk : Nonempty {H : GraphState n d // PairResampling.tripleExteriorKey T H = k}
  · obtain ⟨⟨G, hG⟩⟩ := hk
    subst k
    have hz := CellVarianceGluing.sum_restrict_sub_center_eq_zero
      (PairResampling.tripleExteriorKey T) (PairResampling.tripleExteriorKey T G) g
    have h := exterior_projection_norm_centered T hT G
      (g - CellVarianceGluing.center (PairResampling.tripleExteriorKey T) g) hz
    let y : T.powersetCard 2 → _ := fun a =>
      CellVarianceGluing.restrict (PairResampling.tripleExteriorKey T)
        (PairResampling.tripleExteriorKey T G)
        (PairResampling.expectation n d a.val
          (g - CellVarianceGluing.center (PairResampling.tripleExteriorKey T) g))
    change ‖∑ i : Fin 3, y (pairEquiv T hT i)‖ ^ 2 ≤
      2 * ∑ i : Fin 3, ‖y (pairEquiv T hT i)‖ ^ 2 at h
    rw [(pairEquiv T hT).sum_comp y,
      (pairEquiv T hT).sum_comp (fun a => ‖y a‖ ^ 2)] at h
    exact h
  · have hz (a : T.powersetCard 2) :
        CellVarianceGluing.restrict (PairResampling.tripleExteriorKey T) k
          (PairResampling.expectation n d a.val
            (g - CellVarianceGluing.center (PairResampling.tripleExteriorKey T) g)) = 0 := by
      ext H
      exact False.elim (hk ⟨H⟩)
    simp only [hz, Finset.sum_const_zero, norm_zero, zero_pow (by omega : 2 ≠ 0),
      mul_zero, le_refl]

end Problem315.TripleActualRowBound

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/TripleActualRowBound.lean -/
