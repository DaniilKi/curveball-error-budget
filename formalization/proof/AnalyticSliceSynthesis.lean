import AnalyticSliceTransport

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SliceCoefficientAlgebra.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceCoefficients

variable {V : Type*} [sectionFintypeV : Fintype V] [DecidableEq V]

def linearPair (u : V → ℝ) (i j : V) : ℝ :=
  if i = j then 0 else u i + u j

def rowSum (c : V → V → ℝ) (i : V) : ℝ := ∑ j, c i j

def outside (i j : V) : Finset V := (Finset.univ.erase i).erase j

def meetingSum (c : V → V → ℝ) (i j : V) : ℝ :=
  ∑ k ∈ outside i j, (c i k + c j k)

def disjointSum (c : V → V → ℝ) (i j : V) : ℝ :=
  (∑ k ∈ outside i j, ∑ l ∈ outside i j, c k l) / 2

theorem sum_outside (f : V → ℝ) {i j : V} (hij : i ≠ j) :
    (∑ k ∈ outside i j, f k) = (∑ k, f k) - f i - f j := by
  have hi := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  have hj := Finset.sum_erase_add (Finset.univ.erase i) f
    (by simp [Ne.symm hij] : j ∈ Finset.univ.erase i)
  unfold outside
  linarith

theorem linearPair_rowSum (u : V → ℝ) (hu : ∑ i, u i = 0) (i : V) :
    rowSum (linearPair u) i = ((Fintype.card V : ℝ) - 2) * u i := by
  have heq (j : V) : linearPair u i j =
      (u i + u j) - (if i = j then 2 * u i else 0) := by
    by_cases hij : i = j <;> simp [linearPair, hij] ; ring
  simp only [rowSum, heq, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hu,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

theorem meetingSum_eq (c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    {i j : V} (hij : i ≠ j) :
    meetingSum c i j = rowSum c i + rowSum c j - 2 * c i j := by
  unfold meetingSum
  rw [Finset.sum_add_distrib, sum_outside _ hij, sum_outside _ hij]
  simp only [hdiag, hsym j i, rowSum]
  ring

theorem double_outside_eq (c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    {i j : V} (hij : i ≠ j) :
    (∑ k ∈ outside i j, ∑ l ∈ outside i j, c k l) =
      (∑ k, rowSum c k) - 2 * rowSum c i - 2 * rowSum c j + 2 * c i j := by
  simp_rw [sum_outside (fun l => c _ l) hij]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    sum_outside _ hij, sum_outside _ hij, sum_outside _ hij]
  have hci : (∑ k, c k i) = rowSum c i := by
    unfold rowSum
    apply Finset.sum_congr rfl
    intro k hk
    exact hsym k i
  have hcj : (∑ k, c k j) = rowSum c j := by
    unfold rowSum
    apply Finset.sum_congr rfl
    intro k hk
    exact hsym k j
  simp only [hdiag, hsym j i, hci, hcj]
  change (∑ k, rowSum c k) - rowSum c i - rowSum c j -
    (rowSum c i - 0 - c i j) - (rowSum c j - c i j - 0) = _
  ring

include sectionFintypeV in
theorem linearPair_symmetric (u : V → ℝ) (i j : V) :
    linearPair u i j = linearPair u j i := by
  have retainedsectionFintypeV := sectionFintypeV
  simp [linearPair, eq_comm, add_comm]

include sectionFintypeV in
@[simp] theorem linearPair_diag (u : V → ℝ) (i : V) : linearPair u i i = 0 := by
  have retainedsectionFintypeV := sectionFintypeV
  simp [linearPair]

theorem linearPair_total (u : V → ℝ) (hu : ∑ i, u i = 0) :
    ∑ i, rowSum (linearPair u) i = 0 := by
  simp_rw [linearPair_rowSum u hu, ← Finset.mul_sum, hu, mul_zero]

theorem linearPair_meetingSum (u : V → ℝ) (hu : ∑ i, u i = 0)
    {i j : V} (hij : i ≠ j) :
    meetingSum (linearPair u) i j =
      ((Fintype.card V : ℝ) - 4) * linearPair u i j := by
  rw [meetingSum_eq _ (linearPair_symmetric u) (linearPair_diag u) hij]
  simp only [linearPair_rowSum u hu, linearPair, hij, ite_false]
  ring

theorem linearPair_disjointSum (u : V → ℝ) (hu : ∑ i, u i = 0)
    {i j : V} (hij : i ≠ j) :
    disjointSum (linearPair u) i j =
      -((Fintype.card V : ℝ) - 3) * linearPair u i j := by
  unfold disjointSum
  rw [double_outside_eq _ (linearPair_symmetric u) (linearPair_diag u) hij,
    linearPair_total u hu]
  simp only [linearPair_rowSum u hu, linearPair, hij, ite_false]
  ring

theorem rowZero_meetingSum (c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    (hrow : ∀ i, rowSum c i = 0) {i j : V} (hij : i ≠ j) :
    meetingSum c i j = -2 * c i j := by
  rw [meetingSum_eq c hsym hdiag hij, hrow, hrow]
  ring

theorem rowZero_disjointSum (c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    (hrow : ∀ i, rowSum c i = 0) {i j : V} (hij : i ≠ j) :
    disjointSum c i j = c i j := by
  unfold disjointSum
  rw [double_outside_eq c hsym hdiag hij]
  simp [hrow]

theorem linearPair_injective_of_centered (hcard : 3 ≤ Fintype.card V)
    (u v : V → ℝ) (hu : ∑ i, u i = 0) (hv : ∑ i, v i = 0)
    (heq : linearPair u = linearPair v) : u = v := by
  funext i
  have hrow := congrArg (fun c => rowSum c i) heq
  rw [linearPair_rowSum u hu, linearPair_rowSum v hv] at hrow
  have hc : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hcard
  have hn : (Fintype.card V : ℝ) - 2 ≠ 0 := by linarith
  exact mul_left_cancel₀ hn hrow

theorem linearPair_orthogonal_rowZero (u : V → ℝ) (c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    (hrow : ∀ i, rowSum c i = 0) :
    (∑ i, ∑ j, linearPair u i j * c i j) = 0 := by
  have heq (i j : V) : linearPair u i j * c i j =
      u i * c i j + u j * c i j := by
    by_cases hij : i = j
    · subst j
      simp [hdiag]
    · simp only [linearPair, hij, ite_false]
      ring
  simp_rw [heq, Finset.sum_add_distrib]
  have hfirst : (∑ i, ∑ j, u i * c i j) = 0 := by
    simp_rw [← Finset.mul_sum]
    change (∑ i, u i * rowSum c i) = 0
    simp [hrow]
  have hsecond : (∑ i, ∑ j, u j * c i j) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hcol (j : V) : (∑ i, c i j) = 0 := by
      calc
        (∑ i, c i j) = rowSum c j := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hsym i j
        _ = 0 := hrow j
    simp [hcol]
  rw [hfirst, hsecond, add_zero]

theorem linearPair_row_sq (u : V → ℝ) (hu : ∑ i, u i = 0) (i : V) :
    (∑ j, linearPair u i j ^ 2) =
      ((Fintype.card V : ℝ) - 4) * u i ^ 2 + ∑ j, u j ^ 2 := by
  have heq (j : V) : linearPair u i j ^ 2 =
      (u i ^ 2 + 2 * u i * u j + u j ^ 2) -
        (if i = j then 4 * u i ^ 2 else 0) := by
    by_cases hij : i = j <;> simp [linearPair, hij] <;> ring
  simp only [heq, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum, hu, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  ring

theorem linearPair_norm_sq (u : V → ℝ) (hu : ∑ i, u i = 0) :
    (∑ i, ∑ j, linearPair u i j ^ 2) / 2 =
      ((Fintype.card V : ℝ) - 2) * ∑ i, u i ^ 2 := by
  simp only [linearPair_row_sq u hu, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

def constantPair (a : ℝ) (i j : V) : ℝ := if i = j then 0 else a

include sectionFintypeV in
@[simp] theorem constantPair_diag (a : ℝ) (i : V) : constantPair a i i = 0 := by
  have retainedsectionFintypeV := sectionFintypeV
  simp [constantPair]

include sectionFintypeV in
theorem constantPair_symmetric (a : ℝ) (i j : V) :
    constantPair a i j = constantPair a j i := by
  have retainedsectionFintypeV := sectionFintypeV
  simp [constantPair, eq_comm]

theorem constantPair_rowSum (a : ℝ) (i : V) :
    rowSum (constantPair a) i = ((Fintype.card V : ℝ) - 1) * a := by
  have heq (j : V) : constantPair a i j = a - (if i = j then a else 0) := by
    by_cases h : i = j <;> simp [constantPair, h]
  simp only [rowSum, heq, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

theorem exists_coefficient_decomposition (hcard : 3 ≤ Fintype.card V)
    (c : V → V → ℝ) (hsym : ∀ i j, c i j = c j i)
    (hdiag : ∀ i, c i i = 0) :
    ∃ a : ℝ, ∃ u : V → ℝ, ∃ z : V → V → ℝ,
      (∑ i, u i) = 0 ∧ (∀ i, rowSum z i = 0) ∧
      (∀ i j, z i j = z j i) ∧ (∀ i, z i i = 0) ∧
      (∀ i j, c i j = constantPair a i j + linearPair u i j + z i j) := by
  let N : ℝ := Fintype.card V
  let C : ℝ := ∑ i, rowSum c i
  let a : ℝ := C / (N * (N - 1))
  let u : V → ℝ := fun i => (rowSum c i - C / N) / (N - 2)
  let z : V → V → ℝ := fun i j => c i j - constantPair a i j - linearPair u i j
  have hN3 : 3 ≤ N := by
    dsimp [N]
    exact_mod_cast hcard
  have hN : N ≠ 0 := by linarith
  have hN1 : N - 1 ≠ 0 := by linarith
  have hN2 : N - 2 ≠ 0 := by linarith
  have hu : (∑ i, u i) = 0 := by
    simp only [u, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    change (C - N * C / N) / (N - 2) = 0
    field_simp
    ring
  have hzrow (i : V) : rowSum z i = 0 := by
    change (∑ j, (c i j - constantPair a i j - linearPair u i j)) = 0
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    change rowSum c i - rowSum (constantPair a) i - rowSum (linearPair u) i = 0
    rw [constantPair_rowSum, linearPair_rowSum u hu]
    change rowSum c i - (N - 1) * (C / (N * (N - 1))) -
      (N - 2) * ((rowSum c i - C / N) / (N - 2)) = 0
    field_simp
    ring
  refine ⟨a, u, z, hu, hzrow, ?_, ?_, ?_⟩
  · intro i j
    simp only [z, hsym i j, constantPair_symmetric a i j, linearPair_symmetric u i j]
  · intro i
    simp [z, hdiag]
  · intro i j
    dsimp [z]
    ring

def intersectionAction (a b d : ℝ) (c : V → V → ℝ) (i j : V) : ℝ :=
  if i = j then 0 else a * c i j + b * meetingSum c i j + d * disjointSum c i j

theorem intersectionAction_linearPair (a b d : ℝ) (u : V → ℝ)
    (hu : ∑ i, u i = 0) (i j : V) :
    intersectionAction a b d (linearPair u) i j =
      (a + ((Fintype.card V : ℝ) - 4) * b -
        ((Fintype.card V : ℝ) - 3) * d) * linearPair u i j := by
  by_cases hij : i = j
  · subst j
    simp [intersectionAction]
  · simp only [intersectionAction, hij, ite_false,
      linearPair_meetingSum u hu hij, linearPair_disjointSum u hu hij]
    ring

theorem intersectionAction_rowZero (a b d : ℝ) (c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    (hrow : ∀ i, rowSum c i = 0) (i j : V) :
    intersectionAction a b d c i j = (a - 2 * b + d) * c i j := by
  by_cases hij : i = j
  · subst j
    simp [intersectionAction, hdiag]
  · simp only [intersectionAction, hij, ite_false,
      rowZero_meetingSum c hsym hdiag hrow hij,
      rowZero_disjointSum c hsym hdiag hrow hij]
    ring

end Problem315.SliceCoefficients

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SliceCoefficientAlgebra.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/GramComparison.lean -/
section

namespace OAI

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace Problem315.Analytic

variable {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem gram_comparison_of_range
    (B : F →ₗ[ℝ] E) (G : E →ₗ[ℝ] E) (hG : G.IsSymmetric)
    (hpos : ∀ x : E, 0 ≤ ⟪x, G x⟫)
    (hinv : ∀ y : E, y ∈ LinearMap.range B → G y ∈ LinearMap.range B)
    (hcomp : ∀ c : F, ‖LinearMap.adjoint B (B c)‖ ^ 2 ≤ ⟪B c, G (B c)⟫)
    (x : E) : ⟪x, B (LinearMap.adjoint B x)⟫ ≤ ⟪x, G x⟫ := by
  let M := LinearMap.range B
  let p := M.starProjection x
  let q := x - p
  have hp : p ∈ M := M.starProjection_apply_mem x
  have hq : q ∈ Mᗮ := M.sub_starProjection_mem_orthogonal x
  have hx : x = p + q := by dsimp only [q]; abel
  have hBq : LinearMap.adjoint B q = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [LinearMap.adjoint_inner_left]
    rw [real_inner_comm]
    exact hq (B (LinearMap.adjoint B q)) (LinearMap.mem_range_self _ _)
  have hcross : ⟪p, G q⟫ = 0 := by
    rw [← hG p q]
    exact hq (G p) (hinv p hp)
  have hcross' : ⟪q, G p⟫ = 0 := by
    rw [real_inner_comm]
    exact hq (G p) (hinv p hp)
  have hnorm : ‖LinearMap.adjoint B x‖ ^ 2 = ‖LinearMap.adjoint B p‖ ^ 2 := by
    rw [hx, map_add, hBq, add_zero]
  have hform : ⟪x, G x⟫ = ⟪p, G p⟫ + ⟪q, G q⟫ := by
    rw [hx, map_add, inner_add_left, inner_add_right, inner_add_right,
      hcross, hcross']
    ring
  obtain ⟨c, hc⟩ := hp
  have hccomp := hcomp c
  rw [hc] at hccomp
  rw [← LinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq, hnorm, hform]
  exact hccomp.trans (le_add_of_nonneg_right (hpos q))

omit [FiniteDimensional ℝ F] in

theorem inner_basis_apply_of_diagonal {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ F) (A : F →ₗ[ℝ] F) (μ : ι → ℝ)
    (hdiag : ∀ i, A (b i) = μ i • b i) (c : F) (i : ι) :
    ⟪b i, A c⟫ = μ i * ⟪b i, c⟫ := by
  have hsum : A c = ∑ j, (b.repr c j * μ j) • b j := by
    calc
      A c = A (∑ j, b.repr c j • b j) := congrArg A (b.sum_repr c).symm
      _ = _ := by simp only [map_sum, map_smul, hdiag, smul_smul]
  rw [hsum, b.orthonormal.inner_right_fintype, b.repr_apply_apply]
  ring

theorem gram_comparison_of_eigenbasis {ι : Type*} [Fintype ι]
    (B : F →ₗ[ℝ] E) (G : E →ₗ[ℝ] E) (hG : G.IsSymmetric)
    (hpos : ∀ x : E, 0 ≤ ⟪x, G x⟫)
    (b : OrthonormalBasis ι ℝ F) (μ lam : ι → ℝ)
    (hgram : ∀ i, LinearMap.adjoint B (B (b i)) = μ i • b i)
    (himage : ∀ i, G (B (b i)) = lam i • B (b i))
    (hbound : ∀ i, μ i ≤ lam i) (x : E) :
    ⟪x, B (LinearMap.adjoint B x)⟫ ≤ ⟪x, G x⟫ := by
  classical
  have hμpos (i : ι) : 0 ≤ μ i := by
    have h := B.adjoint_inner_right (b i) (B (b i))
    have hunit : ⟪b i, b i⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one i]
      norm_num
    rw [hgram, inner_smul_right, hunit, mul_one, real_inner_self_eq_norm_sq] at h
    rw [h]
    positivity
  apply gram_comparison_of_range B G hG hpos
  · rintro y ⟨c, rfl⟩
    rw [← b.sum_repr c, map_sum, map_sum]
    apply Submodule.sum_mem
    intro i hi
    rw [map_smul, map_smul, himage]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (LinearMap.mem_range_self B (b i)))
  · intro c
    let K := (LinearMap.adjoint B).comp B
    let L := (LinearMap.adjoint B).comp (G.comp B)
    have hK (i : ι) : K (b i) = μ i • b i := hgram i
    have hL (i : ι) : L (b i) = (lam i * μ i) • b i := by
      simp only [L, LinearMap.comp_apply, himage, map_smul, hgram, smul_smul]
    have hKcoord (i : ι) : ⟪b i, LinearMap.adjoint B (B c)⟫ =
        μ i * ⟪b i, c⟫ := inner_basis_apply_of_diagonal b K μ hK c i
    have hLcoord (i : ι) : ⟪b i, LinearMap.adjoint B (G (B c))⟫ =
        (lam i * μ i) * ⟪b i, c⟫ :=
      inner_basis_apply_of_diagonal b L (fun i => lam i * μ i) hL c i
    rw [← b.sum_sq_inner_right, ← B.adjoint_inner_right,
      ← b.sum_inner_mul_inner c (LinearMap.adjoint B (G (B c)))]
    apply Finset.sum_le_sum
    intro i hi
    rw [hKcoord, hLcoord]
    have hcomm : ⟪c, b i⟫ = ⟪b i, c⟫ := real_inner_comm _ _
    rw [hcomm]
    have hh := mul_le_mul_of_nonneg_right (hbound i) (hμpos i)
    have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg ⟪b i, c⟫)
    nlinarith

theorem gram_comparison_of_two_blocks_without_signs
    (B : F →ₗ[ℝ] E) (G : E →ₗ[ℝ] E) (hG : G.IsSymmetric)
    (hpos : ∀ x : E, 0 ≤ ⟪x, G x⟫)
    (μ₁ μ₂ lam₁ lam₂ : ℝ)
    (hbound₁ : μ₁ ≤ lam₁) (hbound₂ : μ₂ ≤ lam₂)
    (hdecomp : ∀ c : F, ∃ u v : F,
      B c = B u + B v ∧ ⟪u, v⟫ = 0 ∧
      LinearMap.adjoint B (B u) = μ₁ • u ∧
      LinearMap.adjoint B (B v) = μ₂ • v ∧
      G (B u) = lam₁ • B u ∧ G (B v) = lam₂ • B v)
    (x : E) : ⟪x, B (LinearMap.adjoint B x)⟫ ≤ ⟪x, G x⟫ := by
  apply gram_comparison_of_range B G hG hpos
  · rintro y ⟨c, rfl⟩
    obtain ⟨u, v, hc, huv, hKu, hKv, hGu, hGv⟩ := hdecomp c
    rw [hc, map_add, hGu, hGv]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (LinearMap.mem_range_self B u))
      (Submodule.smul_mem _ _ (LinearMap.mem_range_self B v))
  · intro c
    obtain ⟨u, v, hc, huv, hKu, hKv, hGu, hGv⟩ := hdecomp c
    have hvu : ⟪v, u⟫ = 0 := by rw [real_inner_comm]; exact huv
    have hBu : ⟪B u, B u⟫ = μ₁ * ‖u‖ ^ 2 := by
      rw [← B.adjoint_inner_right, hKu, inner_smul_right, real_inner_self_eq_norm_sq]
    have hBv : ⟪B v, B v⟫ = μ₂ * ‖v‖ ^ 2 := by
      rw [← B.adjoint_inner_right, hKv, inner_smul_right, real_inner_self_eq_norm_sq]
    have hBuv : ⟪B u, B v⟫ = 0 := by
      rw [← B.adjoint_inner_right, hKv, inner_smul_right, huv, mul_zero]
    have hBvu : ⟪B v, B u⟫ = 0 := by rw [real_inner_comm]; exact hBuv
    rw [hc, map_add, hKu, hKv, ← real_inner_self_eq_norm_sq,
      map_add, hGu, hGv]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real, huv, hvu, hBuv, hBvu, hBu, hBv,
      real_inner_self_eq_norm_sq, mul_zero, add_zero, zero_add]
    have hposu : 0 ≤ μ₁ * ‖u‖ ^ 2 := by
      rw [← hBu]
      rw [real_inner_self_eq_norm_sq]
      positivity
    have hposv : 0 ≤ μ₂ * ‖v‖ ^ 2 := by
      rw [← hBv]
      rw [real_inner_self_eq_norm_sq]
      positivity
    have h₁ := mul_le_mul_of_nonneg_right hbound₁ hposu
    have h₂ := mul_le_mul_of_nonneg_right hbound₂ hposv
    nlinarith

theorem gram_comparison_of_two_blocks
    (B : F →ₗ[ℝ] E) (G : E →ₗ[ℝ] E) (hG : G.IsSymmetric)
    (hpos : ∀ x : E, 0 ≤ ⟪x, G x⟫)
    (μ₁ μ₂ lam₁ lam₂ : ℝ)
    (_hμ₁ : 0 ≤ μ₁) (_hμ₂ : 0 ≤ μ₂)
    (hbound₁ : μ₁ ≤ lam₁) (hbound₂ : μ₂ ≤ lam₂)
    (hdecomp : ∀ c : F, ∃ u v : F,
      B c = B u + B v ∧ ⟪u, v⟫ = 0 ∧
      LinearMap.adjoint B (B u) = μ₁ • u ∧
      LinearMap.adjoint B (B v) = μ₂ • v ∧
      G (B u) = lam₁ • B u ∧ G (B v) = lam₂ • B v)
    (x : E) : ⟪x, B (LinearMap.adjoint B x)⟫ ≤ ⟪x, G x⟫ :=
  gram_comparison_of_two_blocks_without_signs B G hG hpos μ₁ μ₂ lam₁ lam₂
    hbound₁ hbound₂ hdecomp x

end Problem315.Analytic

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/GramComparison.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SliceSynthesis.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceSynthesis
open SliceCoefficients

variable {V E : Type*} [Fintype V] [sectionDecidableEqV : DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Coeff (V : Type*) [Fintype V] := EuclideanSpace ℝ (V × V)

def ofMatrix (c : V → V → ℝ) : Coeff V :=
  WithLp.toLp 2 (fun p => c p.1 p.2)

include sectionDecidableEqV in
@[simp] theorem ofMatrix_apply (c : V → V → ℝ) (i j : V) :
    ofMatrix c (i,j) = c i j := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  exact rfl

def synthesis (z : V → V → E) : Coeff V →ₗ[ℝ] E where
  toFun c := ∑ i, ∑ j, c (i,j) • z i j
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [mul_smul, Finset.smul_sum]

include sectionDecidableEqV in
@[simp] theorem synthesis_ofMatrix (z : V → V → E) (c : V → V → ℝ) :
    synthesis z (ofMatrix c) = ∑ i, ∑ j, c i j • z i j := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  exact rfl

def symMatrix (c : Coeff V) (i j : V) : ℝ :=
  if i = j then 0 else (c (i,j) + c (j,i)) / 2

@[simp] theorem symMatrix_diag (c : Coeff V) (i : V) : symMatrix c i i = 0 := by
  simp [symMatrix]

theorem symMatrix_symmetric (c : Coeff V) (i j : V) :
    symMatrix c i j = symMatrix c j i := by simp [symMatrix, eq_comm, add_comm]

theorem synthesis_symMatrix (z : V → V → E)
    (hzsym : ∀ i j, z i j = z j i) (hzdiag : ∀ i, z i i = 0)
    (c : Coeff V) : synthesis z (ofMatrix (symMatrix c)) = synthesis z c := by
  have hterm (i j : V) : symMatrix c i j • z i j =
      (1 / 2 : ℝ) • (c (i,j) • z i j + c (j,i) • z i j) := by
    by_cases hij : i = j
    · subst j; simp [hzdiag]
    · simp only [symMatrix, hij, ite_false, ← add_smul, ← mul_smul]
      congr 1
      ring
  have htranspose : (∑ i, ∑ j, c (j,i) • z i j) = ∑ i, ∑ j, c (i,j) • z i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hzsym]
  rw [synthesis_ofMatrix]
  simp_rw [hterm, ← Finset.smul_sum, Finset.sum_add_distrib]
  rw [htranspose, smul_add, ← add_smul]
  norm_num
  rfl

theorem synthesis_constant (z : V → V → E)
    (hzdiag : ∀ i, z i i = 0) (hztotal : (∑ i, ∑ j, z i j) = 0)
    (a : ℝ) : synthesis z (ofMatrix (constantPair a)) = 0 := by
  have hterm (i j : V) : constantPair a i j • z i j = a • z i j := by
    by_cases hij : i = j
    · subst j; simp [hzdiag]
    · simp [constantPair, hij]
  rw [synthesis_ofMatrix]
  simp_rw [hterm, ← Finset.smul_sum]
  rw [hztotal, smul_zero]

include sectionDecidableEqV in
theorem ofMatrix_inner (c d : V → V → ℝ) :
    ⟪ofMatrix c, ofMatrix d⟫ = ∑ i, ∑ j, c i j * d i j := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fintype.sum_prod_type, ofMatrix, mul_comm]

theorem exists_synthesis_decomposition (hcard : 3 ≤ Fintype.card V)
    (z : V → V → E) (hzsym : ∀ i j, z i j = z j i)
    (hzdiag : ∀ i, z i i = 0) (hztotal : (∑ i, ∑ j, z i j) = 0)
    (c : Coeff V) :
    ∃ u : V → ℝ, ∃ v : V → V → ℝ,
      (∑ i, u i) = 0 ∧ (∀ i, rowSum v i = 0) ∧
      (∀ i j, v i j = v j i) ∧ (∀ i, v i i = 0) ∧
      synthesis z c = synthesis z (ofMatrix (linearPair u)) + synthesis z (ofMatrix v) ∧
      ⟪ofMatrix (linearPair u), ofMatrix v⟫ = 0 := by
  obtain ⟨a,u,v,hu,hvrow,hvsym,hvdiag,hdecomp⟩ :=
    exists_coefficient_decomposition hcard (symMatrix c)
      (symMatrix_symmetric c) (symMatrix_diag c)
  refine ⟨u,v,hu,hvrow,hvsym,hvdiag,?_,?_⟩
  · rw [← synthesis_symMatrix z hzsym hzdiag c]
    have heq : ofMatrix (symMatrix c) =
        ofMatrix (constantPair a) + ofMatrix (linearPair u) + ofMatrix v := by
      ext p
      exact hdecomp p.1 p.2
    rw [heq, map_add, map_add, synthesis_constant z hzdiag hztotal, zero_add]
  · rw [ofMatrix_inner]
    exact linearPair_orthogonal_rowZero u v hvsym hvdiag hvrow

variable [sectionFiniteDimensionalℝE : FiniteDimensional ℝ E]

include sectionFiniteDimensionalℝE in
theorem synthesis_single (z : V → V → E) (i j : V) :
    synthesis z (EuclideanSpace.single (i,j) 1) = z i j := by
  have retainedsectionFiniteDimensionalℝE := sectionFiniteDimensionalℝE
  simp [synthesis, ite_and]

theorem adjoint_synthesis_apply (z : V → V → E) (x : E) (i j : V) :
    LinearMap.adjoint (synthesis z) x (i,j) = ⟪z i j,x⟫ := by
  have h := (synthesis z).adjoint_inner_right (EuclideanSpace.single (i,j) 1) x
  simpa [synthesis_single, EuclideanSpace.inner_single_left] using h

theorem gram_synthesis_apply (z : V → V → E) (c : Coeff V) (i j : V) :
    LinearMap.adjoint (synthesis z) (synthesis z c) (i,j) =
      ∑ k, ∑ l, c (k,l) * ⟪z i j,z k l⟫ := by
  rw [adjoint_synthesis_apply]
  simp [synthesis, inner_sum, inner_smul_right]

theorem comparison_of_scalar_actions (hcard : 3 ≤ Fintype.card V)
    (z : V → V → E) (hzsym : ∀ i j, z i j = z j i)
    (hzdiag : ∀ i, z i i = 0) (hztotal : (∑ i, ∑ j, z i j) = 0)
    (G : E →ₗ[ℝ] E) (hG : G.IsSymmetric) (hpos : ∀ x : E, 0 ≤ ⟪x, G x⟫)
    (μ₁ μ₂ lam₁ lam₂ : ℝ) (hμ₁ : 0 ≤ μ₁) (hμ₂ : 0 ≤ μ₂)
    (hbound₁ : μ₁ ≤ lam₁) (hbound₂ : μ₂ ≤ lam₂)
    (hgram₁ : ∀ u : V → ℝ, (∑ i, u i) = 0 →
      LinearMap.adjoint (synthesis z) (synthesis z (ofMatrix (linearPair u))) =
        μ₁ • ofMatrix (linearPair u))
    (hgram₂ : ∀ v : V → V → ℝ, (∀ i, rowSum v i = 0) →
      (∀ i j, v i j = v j i) → (∀ i, v i i = 0) →
      LinearMap.adjoint (synthesis z) (synthesis z (ofMatrix v)) = μ₂ • ofMatrix v)
    (himage₁ : ∀ u : V → ℝ, (∑ i, u i) = 0 →
      G (synthesis z (ofMatrix (linearPair u))) =
        lam₁ • synthesis z (ofMatrix (linearPair u)))
    (himage₂ : ∀ v : V → V → ℝ, (∀ i, rowSum v i = 0) →
      (∀ i j, v i j = v j i) → (∀ i, v i i = 0) →
      G (synthesis z (ofMatrix v)) = lam₂ • synthesis z (ofMatrix v))
    (x : E) : ⟪x, synthesis z (LinearMap.adjoint (synthesis z) x)⟫ ≤ ⟪x, G x⟫ := by
  apply Analytic.gram_comparison_of_two_blocks (synthesis z) G hG hpos
    μ₁ μ₂ lam₁ lam₂ hμ₁ hμ₂ hbound₁ hbound₂
  intro c
  obtain ⟨u,v,hu,hvrow,hvsym,hvdiag,hc,huv⟩ :=
    exists_synthesis_decomposition hcard z hzsym hzdiag hztotal c
  exact ⟨ofMatrix (linearPair u),ofMatrix v,hc,huv,
    hgram₁ u hu,hgram₂ v hvrow hvsym hvdiag,
    himage₁ u hu,himage₂ v hvrow hvsym hvdiag⟩

end Problem315.SliceSynthesis

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SliceSynthesis.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SliceEuclideanGenerator.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Problem315.SliceEuclideanGenerator

variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev State (α : Type*) [Fintype α] (q : ℕ) :=
  ↥((Finset.univ : Finset α).powersetCard q)

def relabel (q : ℕ) (e : Equiv.Perm α) : Equiv.Perm (State α q) where
  toFun S := ⟨S.val.image e, by
    have hc := (Finset.mem_powersetCard.mp S.property).2
    simp [Finset.mem_powersetCard, Finset.card_image_of_injective _ e.injective, hc]⟩
  invFun S := ⟨S.val.image e.symm, by
    have hc := (Finset.mem_powersetCard.mp S.property).2
    simp [Finset.mem_powersetCard, Finset.card_image_of_injective _ e.symm.injective, hc]⟩
  left_inv S := by apply Subtype.ext; simp [Finset.image_image]
  right_inv S := by apply Subtype.ext; simp [Finset.image_image]

@[simp] theorem relabel_val (q : ℕ) (e : Equiv.Perm α) (S : State α q) :
    (relabel q e S).val = S.val.image e := rfl

def swapState (q : ℕ) (a b : α) : Equiv.Perm (State α q) :=
  relabel q (Equiv.swap a b)

@[simp] theorem swapState_twice (q : ℕ) (a b : α) (S : State α q) :
    swapState q a b (swapState q a b S) = S := by
  apply Subtype.ext
  simp [swapState, Finset.image_image, Function.comp_def]

def moveOperator (q : ℕ) (a b : α) :
    EuclideanSpace ℝ (State α q) →ₗ[ℝ] EuclideanSpace ℝ (State α q) where
  toFun f := WithLp.toLp 2 (fun S => f (swapState q a b S))
  map_add' _ _ := by ext S; rfl
  map_smul' _ _ := by ext S; rfl

@[simp] theorem moveOperator_apply (q : ℕ) (a b : α)
    (f : EuclideanSpace ℝ (State α q)) (S : State α q) :
    moveOperator q a b f S = f (swapState q a b S) := rfl

@[simp] theorem moveOperator_twice (q : ℕ) (a b : α)
    (f : EuclideanSpace ℝ (State α q)) :
    moveOperator q a b (moveOperator q a b f) = f := by
  ext S
  simp

theorem moveOperator_symmetric (q : ℕ) (a b : α) :
    (moveOperator q a b).IsSymmetric := by
  intro f g
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, moveOperator_apply]
  have h := Equiv.sum_comp (swapState q a b)
    (fun S : State α q => g S * f (swapState q a b S))
  simpa only [swapState_twice] using h.symm

theorem move_energy (q : ℕ) (a b : α) (f : EuclideanSpace ℝ (State α q)) :
    ⟪f, f - moveOperator q a b f⟫ =
      (1 / 2 : ℝ) * ‖f - moveOperator q a b f‖ ^ 2 := by
  have hs := moveOperator_symmetric q a b f (moveOperator q a b f)
  rw [moveOperator_twice] at hs
  have hn := norm_sub_sq_real f (moveOperator q a b f)
  have hnorm : ‖moveOperator q a b f‖ ^ 2 = ‖f‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using hs
  rw [inner_sub_right, real_inner_self_eq_norm_sq]
  rw [hn, hnorm]
  ring

def generator (q : ℕ) :
    EuclideanSpace ℝ (State α q) →ₗ[ℝ] EuclideanSpace ℝ (State α q) :=
  (1 / 4 : ℝ) • ∑ a : α, ∑ b : α, (LinearMap.id - moveOperator q a b)

@[simp] theorem generator_apply (q : ℕ) (f : EuclideanSpace ℝ (State α q))
    (S : State α q) :
    generator q f S = (∑ a : α, ∑ b : α, (f S - f (swapState q a b S))) / 4 := by
  simp only [generator, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.sub_apply, LinearMap.id_apply, PiLp.smul_apply, smul_eq_mul,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.sub_apply, moveOperator_apply]
  ring

theorem generator_symmetric (q : ℕ) : (generator (α := α) q).IsSymmetric := by
  apply LinearMap.IsSymmetric.smul (by simp)
  apply LinearMap.isSymmetric_sum
  intro a _
  apply LinearMap.isSymmetric_sum
  intro b _
  exact LinearMap.IsSymmetric.id.sub (moveOperator_symmetric q a b)

theorem generator_energy (q : ℕ) (f : EuclideanSpace ℝ (State α q)) :
    ⟪f, generator q f⟫ =
      (1 / 8 : ℝ) * ∑ a : α, ∑ b : α, ‖f - moveOperator q a b f‖ ^ 2 := by
  simp only [generator, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.sub_apply, LinearMap.id_apply, inner_smul_right, inner_sum]
  simp_rw [move_energy, ← Finset.mul_sum]
  ring

theorem generator_positive (q : ℕ) (f : EuclideanSpace ℝ (State α q)) :
    0 ≤ ⟪f, generator q f⟫ := by
  rw [generator_energy]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _)

end Problem315.SliceEuclideanGenerator

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SliceEuclideanGenerator.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SliceGenerator.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceGenerator

theorem sum_swap_coordinate
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (k : α) :
    (∑ i, ∑ j, (x k - x (Equiv.swap i j k))) =
      2 * ((Fintype.card α : ℝ) * x k - ∑ i, x i) := by
  have inner_sum (i : α) :
      (∑ j, (x k - x (Equiv.swap i j k))) =
        (if i = k then (Fintype.card α : ℝ) * x k - ∑ j, x j else 0) +
          (x k - x i) := by
    by_cases hi : i = k
    · subst i
      simp [Finset.sum_sub_distrib, mul_comm]
    · have hterm (j : α) :
          x k - x (Equiv.swap i j k) = if j = k then x k - x i else 0 := by
        by_cases hj : j = k
        · subst j
          simp
        · simp [Equiv.swap_apply_of_ne_of_ne (Ne.symm hi) (Ne.symm hj), hj]
      simp_rw [hterm]
      simp [hi]
  simp_rw [inner_sum]
  simp only [Finset.sum_add_distrib]
  simp [Finset.sum_sub_distrib, mul_comm]
  ring

theorem sum_swap_coordinate_cross
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (k l : α) (hkl : k ≠ l) :
    (∑ i, ∑ j,
      (x k - x (Equiv.swap i j k)) * (x l - x (Equiv.swap i j l))) =
      -2 * (x k - x l) ^ 2 := by
  have hterm (i j : α) :
      (x k - x (Equiv.swap i j k)) * (x l - x (Equiv.swap i j l)) =
        (if i = k ∧ j = l then -(x k - x l) ^ 2 else 0) +
        (if i = l ∧ j = k then -(x k - x l) ^ 2 else 0) := by
    by_cases hik : i = k <;> by_cases hil : i = l <;>
      by_cases hjk : j = k <;> by_cases hjl : j = l <;>
      simp_all [Equiv.swap_apply_def, eq_comm] <;> ring
  simp_rw [hterm, Finset.sum_add_distrib]
  simp_rw [ite_and]
  simp
  ring

theorem sum_swap_quadratic
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (k l : α) (hkl : k ≠ l) :
    (∑ i, ∑ j,
      (x k * x l - x (Equiv.swap i j k) * x (Equiv.swap i j l))) =
      4 * ((Fintype.card α : ℝ) - 1) * x k * x l +
      2 * (x k ^ 2 + x l ^ 2) - 2 * (∑ i, x i) * (x k + x l) := by
  calc
    _ = ∑ i, ∑ j,
        (x l * (x k - x (Equiv.swap i j k)) +
         x k * (x l - x (Equiv.swap i j l)) -
         (x k - x (Equiv.swap i j k)) * (x l - x (Equiv.swap i j l))) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = x l * (∑ i, ∑ j, (x k - x (Equiv.swap i j k))) +
        x k * (∑ i, ∑ j, (x l - x (Equiv.swap i j l))) -
        (∑ i, ∑ j,
          (x k - x (Equiv.swap i j k)) * (x l - x (Equiv.swap i j l))) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by
      rw [sum_swap_coordinate, sum_swap_coordinate,
        sum_swap_coordinate_cross x k l hkl]
      ring

def generator {α : Type*} [Fintype α] [DecidableEq α]
    (f : (α → ℝ) → ℝ) (x : α → ℝ) : ℝ :=
  (1 / 4 : ℝ) * ∑ i, ∑ j, (f x - f (x ∘ Equiv.swap i j))

theorem generator_coordinate
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (q : ℝ) (hsum : ∑ i, x i = q) (k : α) :
    generator (fun y => y k) x = ((Fintype.card α : ℝ) * x k - q) / 2 := by
  unfold generator
  simp only [Function.comp_apply]
  rw [sum_swap_coordinate, hsum]
  ring

theorem generator_quadratic
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (q : ℝ) (hsum : ∑ i, x i = q)
    (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (k l : α) (hkl : k ≠ l) :
    generator (fun y => y k * y l) x =
      ((Fintype.card α : ℝ) - 1) * x k * x l - (q - 1) / 2 * (x k + x l) := by
  have hsq (i : α) : x i ^ 2 = x i := by
    rcases hbinary i with h | h <;> simp [h]
  unfold generator
  simp only [Function.comp_apply]
  rw [sum_swap_quadratic x k l hkl, hsum, hsq k, hsq l]
  ring

def generatorLinearMap {α : Type*} [Fintype α] [DecidableEq α] :
    ((α → ℝ) → ℝ) →ₗ[ℝ] ((α → ℝ) → ℝ) where
  toFun := generator
  map_add' f g := by
    ext x
    simp only [generator, Pi.add_apply]
    simp_rw [show ∀ a b c d : ℝ, a + b - (c + d) = (a-c) + (b-d) by intros; ring]
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' c f := by
    ext x
    simp only [generator, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [← mul_sub, ← Finset.mul_sum]
    ring

theorem generator_centered_linear
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (u : α → ℝ) (hu : ∑ i, u i = 0) :
    generator (fun y => ∑ i, u i * y i) x =
      (Fintype.card α : ℝ) / 2 * (∑ i, u i * x i) := by
  have heq : (fun y : α → ℝ => ∑ i, u i * y i) =
      ∑ i, u i • (fun y : α → ℝ => y i) := by
    ext y
    simp
  change generatorLinearMap (fun y => ∑ i, u i * y i) x = _
  rw [heq, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ i, u i * generator (fun y => y i) x) = _
  simp_rw [generator_coordinate x (∑ j, x j) rfl]
  simp_rw [← mul_div_assoc, ← Finset.sum_div, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, hu, zero_mul, sub_zero]
  rw [show (∑ i, u i * ((Fintype.card α : ℝ) * x i)) =
      (Fintype.card α : ℝ) * ∑ i, u i * x i by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring]
  ring

theorem sum_coeff_linear_eq_zero
    {α : Type*} [Fintype α]
    (c : α → α → ℝ) (x : α → ℝ)
    (hrow : ∀ i, ∑ j, c i j = 0) (hcol : ∀ j, ∑ i, c i j = 0) :
    (∑ i, ∑ j, c i j * (x i + x j)) = 0 := by
  simp_rw [mul_add, Finset.sum_add_distrib]
  have hleft : (∑ i, ∑ j, c i j * x i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [← Finset.sum_mul, hrow, zero_mul]
  have hright : (∑ i, ∑ j, c i j * x j) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j hj
    rw [← Finset.sum_mul, hcol, zero_mul]
  rw [hleft, hright, add_zero]

theorem generator_row_zero_quadratic
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (q : ℝ) (hsum : ∑ i, x i = q)
    (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (c : α → α → ℝ) (hdiag : ∀ i, c i i = 0)
    (hrow : ∀ i, ∑ j, c i j = 0) (hcol : ∀ j, ∑ i, c i j = 0) :
    generator (fun y => ∑ i, ∑ j, c i j * (y i * y j)) x =
      ((Fintype.card α : ℝ) - 1) * (∑ i, ∑ j, c i j * (x i * x j)) := by
  have heq : (fun y : α → ℝ => ∑ i, ∑ j, c i j * (y i * y j)) =
      ∑ i, ∑ j, c i j • (fun y : α → ℝ => y i * y j) := by
    ext y
    simp
  change generatorLinearMap (fun y => ∑ i, ∑ j, c i j * (y i * y j)) x = _
  rw [heq, map_sum]
  simp_rw [map_sum, map_smul]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ i, ∑ j, c i j * generator (fun y => y i * y j) x) = _
  have hterm (i j : α) : c i j * generator (fun y => y i * y j) x =
      ((Fintype.card α : ℝ) - 1) * (c i j * (x i * x j)) -
        (q - 1) / 2 * (c i j * (x i + x j)) := by
    by_cases hij : i = j
    · subst j
      simp [hdiag]
    · rw [generator_quadratic x q hsum hbinary i j hij]
      ring
  simp_rw [hterm]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_coeff_linear_eq_zero c x hrow hcol]
  ring

theorem generator_symmetric_row_zero_quadratic
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (q : ℝ) (hsum : ∑ i, x i = q)
    (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (c : α → α → ℝ) (hdiag : ∀ i, c i i = 0)
    (hsymm : ∀ i j, c i j = c j i) (hrow : ∀ i, ∑ j, c i j = 0) :
    generator (fun y => ∑ i, ∑ j, c i j * (y i * y j)) x =
      ((Fintype.card α : ℝ) - 1) * (∑ i, ∑ j, c i j * (x i * x j)) := by
  apply generator_row_zero_quadratic x q hsum hbinary c hdiag hrow
  intro j
  simpa only [hsymm] using hrow j

end Problem315.SliceGenerator

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SliceGenerator.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SliceGeneratorSampling.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315.SliceEuclideanGenerator

variable {α : Type*} [Fintype α] [DecidableEq α]

def coordinates {q : ℕ} (S : State α q) (i : α) : ℝ :=
  if i ∈ S.val then 1 else 0

theorem coordinates_binary {q : ℕ} (S : State α q) (i : α) :
    coordinates S i = 0 ∨ coordinates S i = 1 := by
  by_cases hi : i ∈ S.val <;> simp [coordinates, hi]

theorem coordinates_sum {q : ℕ} (S : State α q) :
    ∑ i, coordinates S i = (q : ℝ) := by
  have hc := (Finset.mem_powersetCard.mp S.property).2
  simp [coordinates, hc]

theorem coordinates_swap {q : ℕ} (S : State α q) (a b : α) :
    coordinates (swapState q a b S) = coordinates S ∘ Equiv.swap a b := by
  ext i
  have hm : i ∈ (swapState q a b S).val ↔ Equiv.swap a b i ∈ S.val := by
    change i ∈ S.val.image (Equiv.swap a b) ↔ _
    constructor
    · intro hi
      obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hi
      have he' := congrArg (Equiv.swap a b) he
      have hji : j = Equiv.swap a b i := by simpa using he'
      exact hji ▸ hj
    · intro hi
      apply Finset.mem_image.mpr
      exact ⟨Equiv.swap a b i, hi, by simp⟩
  simp only [coordinates, Function.comp_apply, hm]

def sample (q : ℕ) (f : (α → ℝ) → ℝ) : EuclideanSpace ℝ (State α q) :=
  WithLp.toLp 2 (fun S => f (coordinates S))

@[simp] theorem sample_apply (q : ℕ) (f : (α → ℝ) → ℝ) (S : State α q) :
    sample q f S = f (coordinates S) := rfl

theorem generator_sample (q : ℕ) (f : (α → ℝ) → ℝ) :
    generator q (sample q f) = sample q (SliceGenerator.generator f) := by
  ext S
  rw [generator_apply]
  simp only [sample_apply, SliceGenerator.generator, coordinates_swap]
  ring

theorem generator_sample_linear (q : ℕ) (u : α → ℝ) (hu : ∑ i, u i = 0) :
    generator q (sample q (fun y => ∑ i, u i * y i)) =
      ((Fintype.card α : ℝ) / 2) • sample q (fun y => ∑ i, u i * y i) := by
  rw [generator_sample]
  ext S
  change SliceGenerator.generator (fun y => ∑ i, u i * y i) (coordinates S) = _
  simpa only [PiLp.smul_apply, smul_eq_mul, sample_apply] using
    SliceGenerator.generator_centered_linear (coordinates S) u hu

theorem generator_sample_quadratic (q : ℕ) (c : α → α → ℝ)
    (hdiag : ∀ i, c i i = 0) (hrow : ∀ i, ∑ j, c i j = 0)
    (hcol : ∀ j, ∑ i, c i j = 0) :
    generator q (sample q (fun y => ∑ i, ∑ j, c i j * (y i * y j))) =
      ((Fintype.card α : ℝ) - 1) • sample q (fun y => ∑ i, ∑ j, c i j * (y i * y j)) := by
  rw [generator_sample]
  ext S
  change SliceGenerator.generator (fun y => ∑ i, ∑ j, c i j * (y i * y j)) (coordinates S) = _
  simpa only [PiLp.smul_apply, smul_eq_mul, sample_apply] using
    SliceGenerator.generator_row_zero_quadratic (coordinates S) (q : ℝ)
      (coordinates_sum S) (coordinates_binary S) c hdiag hrow hcol

end Problem315.SliceEuclideanGenerator

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SliceGeneratorSampling.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SliceGeneratorEquality.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315.SliceEuclideanGenerator

variable {α : Type*} [Fintype α] [DecidableEq α]

def equalityVector (q : ℕ) (p : ℝ) (i j : α) : EuclideanSpace ℝ (State α q) :=
  sample q (fun x => SliceEquality.offDiagonal (SliceEquality.centeredEquality x p) i j)

theorem equalityVector_apply (q : ℕ) (p : ℝ) (i j : α) (S : State α q) :
    equalityVector q p i j S =
      if i = j then 0 else SliceMoments.equalIndicator i j S.val - p := by
  by_cases hij : i = j
  · simp [equalityVector, sample, SliceEquality.offDiagonal, hij]
  · by_cases hi : i ∈ S.val <;> by_cases hj : j ∈ S.val <;>
      simp [equalityVector, sample, SliceEquality.offDiagonal, hij,
        SliceEquality.centeredEquality, SliceEquality.equalityIndicator,
        coordinates, SliceMoments.equalIndicator, hi, hj]

theorem additive_equality_image (q : ℕ) (p : ℝ) (u : α → ℝ) (hu : ∑ i, u i = 0) :
    (∑ i, ∑ j, (u i + u j) • equalityVector q p i j) =
      (2 * (2 * (q : ℝ) - (Fintype.card α : ℝ))) •
        sample q (fun x => ∑ i, u i * x i) := by
  ext S
  have h := SliceEquality.additive_centeredEquality_image (coordinates S)
    (coordinates_binary S) (q : ℝ) p (coordinates_sum S) u hu
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    equalityVector, sample_apply]
  linarith

theorem rowzero_equality_image (q : ℕ) (p : ℝ) (c : α → α → ℝ)
    (hdiag : ∀ i, c i i = 0) (hrow : ∀ i, ∑ j, c i j = 0)
    (hcol : ∀ j, ∑ i, c i j = 0) :
    (∑ i, ∑ j, c i j • equalityVector q p i j) =
      (2 : ℝ) • sample q (fun x => ∑ i, ∑ j, c i j * (x i * x j)) := by
  ext S
  have h := SliceEquality.row_zero_offDiagonal_centeredEquality_image (coordinates S)
    (coordinates_binary S) p c hdiag hrow hcol
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    equalityVector, sample_apply]
  linarith

theorem generator_additive_equality (q : ℕ) (p : ℝ) (u : α → ℝ) (hu : ∑ i, u i = 0) :
    generator q (∑ i, ∑ j, (u i + u j) • equalityVector q p i j) =
      ((Fintype.card α : ℝ) / 2) • (∑ i, ∑ j, (u i + u j) • equalityVector q p i j) := by
  rw [additive_equality_image q p u hu, map_smul, generator_sample_linear q u hu]
  simp only [smul_smul]
  congr 1
  ring

theorem generator_rowzero_equality (q : ℕ) (p : ℝ) (c : α → α → ℝ)
    (hdiag : ∀ i, c i i = 0) (hrow : ∀ i, ∑ j, c i j = 0)
    (hcol : ∀ j, ∑ i, c i j = 0) :
    generator q (∑ i, ∑ j, c i j • equalityVector q p i j) =
      ((Fintype.card α : ℝ) - 1) • (∑ i, ∑ j, c i j • equalityVector q p i j) := by
  rw [rowzero_equality_image q p c hdiag hrow hcol, map_smul,
    generator_sample_quadratic q c hdiag hrow hcol]
  simp only [smul_smul]
  congr 1
  ring

end Problem315.SliceEuclideanGenerator

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SliceGeneratorEquality.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SliceBounds.lean -/
section

namespace OAI

noncomputable section

namespace Problem315.SliceBounds

theorem product_ge_sum_sub_one {q r : ℝ} (hq : 1 ≤ q) (hr : 1 ≤ r) :
    q + r - 1 ≤ q * r := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hr)]

def equalityProbability (N q r : ℝ) : ℝ :=
  (q * (q - 1) + r * (r - 1)) / (N * (N - 1))

theorem equalityProbability_pos {N q r : ℝ}
    (hN : 3 ≤ N) (hq : 1 ≤ q) (hr : 1 ≤ r) (hsum : q + r = N) :
    0 < equalityProbability N q r := by
  unfold equalityProbability
  apply div_pos
  · have hq0 : 0 ≤ q - 1 := sub_nonneg.mpr hq
    have hr0 : 0 ≤ r - 1 := sub_nonneg.mpr hr
    have hqprod := mul_nonneg hq0 hq0
    have hrprod := mul_nonneg hr0 hr0
    nlinarith
  · exact mul_pos (by linarith) (by linarith)

theorem equalityProbability_complement {N q r : ℝ}
    (hN : 1 < N) (hsum : q + r = N) :
    1 - equalityProbability N q r = 2 * q * r / (N * (N - 1)) := by
  have hN0 : N ≠ 0 := ne_of_gt (lt_trans (by norm_num) hN)
  have hN1 : N - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hN)
  unfold equalityProbability
  field_simp
  nlinarith [sq_nonneg (q + r - N)]

theorem linear_numerator_identity {N q r : ℝ}
    (hN : 1 < N) (hsum : q + r = N) :
    N * (N - 2) * equalityProbability N q r - (2 * q - N) ^ 2 =
      2 * N / (N - 1) * (q * r - (N - 1)) := by
  have hN0 : N ≠ 0 := ne_of_gt (lt_trans (by norm_num) hN)
  have hN1 : N - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hN)
  unfold equalityProbability
  rw [← hsum] at *
  field_simp
  ring

theorem linear_eigenvalue_le {N q r : ℝ}
    (hN : 3 ≤ N) (hq : 1 ≤ q) (hr : 1 ≤ r) (hsum : q + r = N) :
    (2 * q - N) ^ 2 / (2 * (N - 2) * equalityProbability N q r) ≤ N / 2 := by
  have hp := equalityProbability_pos hN hq hr hsum
  have hden : 0 < 2 * (N - 2) * equalityProbability N q r :=
    mul_pos (mul_pos (by norm_num) (by linarith)) hp
  apply (div_le_iff₀ hden).2
  have hid := linear_numerator_identity (by linarith : 1 < N) hsum
  have hqr : 0 ≤ q * r - (N - 1) := by
    have := product_ge_sum_sub_one hq hr
    linarith
  have hquot : 0 ≤ 2 * N / (N - 1) :=
    div_nonneg (by linarith) (by linarith)
  have hnonneg := mul_nonneg hquot hqr
  nlinarith

theorem quadratic_eigenvalue_le {N μ : ℝ} (hN : 4 ≤ N)
    (htrace : (N * (N - 1) / 2 - N) * μ ≤ N * (N - 1) / 2) :
    μ ≤ N - 1 := by
  have hNpos : 0 < N := by linarith
  have hcoef : 0 < N * (N - 3) / 2 :=
    div_pos (mul_pos hNpos (by linarith)) (by norm_num)
  have hbound : N * (N - 1) / 2 ≤ (N * (N - 3) / 2) * (N - 1) := by
    have hprod := mul_nonneg (by linarith : 0 ≤ N - 4) (by linarith : 0 ≤ N - 1)
    have := mul_nonneg (le_of_lt hNpos) hprod
    nlinarith
  have htrace' : (N * (N - 3) / 2) * μ ≤ N * (N - 1) / 2 := by
    nlinarith [htrace]
  exact (mul_le_mul_iff_right₀ hcoef).mp (htrace'.trans hbound)

theorem disjoint_plane_bound {ρ x y : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    -(x ^ 2 + y ^ 2) * (1 - ρ ^ 2) ≤
      2 * x * y * ρ * (1 - ρ ^ 2) := by
  have hbase : 0 ≤ x ^ 2 + y ^ 2 + 2 * x * y * ρ := by
    have h1 := mul_nonneg hρ0 (sq_nonneg (x + y))
    have h2 := mul_nonneg (sub_nonneg.mpr hρ1) (add_nonneg (sq_nonneg x) (sq_nonneg y))
    nlinarith
  have hfactor : 0 ≤ 1 - ρ ^ 2 := by nlinarith
  have := mul_nonneg hbase hfactor
  nlinarith

end Problem315.SliceBounds

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SliceBounds.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SliceImageNorm.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceImageNorm

variable {α : Type*} [Fintype α] [sectionDecidableEqα : DecidableEq α]

def equalityImage (q : ℕ) (c : α → α → ℝ) (S : Finset α) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, c i j * SliceMoments.centeredEqual Finset.univ q i j S

theorem coord_sum (S : Finset α) :
    (∑ i, SliceMoments.coord i S) = (S.card : ℝ) := by
  simp [SliceMoments.coord]

theorem centeredEquality_coord (q : ℕ) (S : Finset α) (i j : α) :
    SliceEquality.centeredEquality (fun k => SliceMoments.coord k S)
      (SliceMoments.equalMean (Finset.univ : Finset α) q) i j =
      SliceMoments.centeredEqual Finset.univ q i j S := by
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    simp [SliceEquality.centeredEquality, SliceEquality.equalityIndicator,
      SliceMoments.centeredEqual, SliceMoments.equalIndicator, SliceMoments.coord, hi, hj]

theorem equalityImage_linearPair (q : ℕ) (S : Finset α) (hS : S.card = q)
    (u : α → ℝ) (hu : ∑ i, u i = 0) :
    equalityImage q (SliceCoefficients.linearPair u) S =
      (2 * (q : ℝ) - (Fintype.card α : ℝ)) * ∑ i, u i * SliceMoments.coord i S := by
  have hb (i : α) : SliceMoments.coord i S = 0 ∨ SliceMoments.coord i S = 1 := by
    by_cases hi : i ∈ S <;> simp [SliceMoments.coord, hi]
  have hs : (∑ i, SliceMoments.coord i S) = (q : ℝ) := by rw [coord_sum, hS]
  have h := SliceEquality.additive_centeredEquality_image
    (fun i => SliceMoments.coord i S) hb q (SliceMoments.equalMean (Finset.univ : Finset α) q) hs u hu
  have ht (i j : α) :
      (u i + u j) * SliceEquality.offDiagonal
        (SliceEquality.centeredEquality (fun k => SliceMoments.coord k S)
          (SliceMoments.equalMean (Finset.univ : Finset α) q)) i j =
      SliceCoefficients.linearPair u i j * SliceMoments.centeredEqual Finset.univ q i j S := by
    by_cases hij : i = j
    · subst j
      simp [SliceEquality.offDiagonal, SliceCoefficients.linearPair]
    · simp [SliceEquality.offDiagonal, SliceCoefficients.linearPair, hij, centeredEquality_coord]
  simpa only [ht, equalityImage] using h

theorem average_equalityImage_linearPair_sq
    (hN : 2 ≤ Fintype.card α) (q : ℕ) (hq : q ≤ Fintype.card α)
    (u : α → ℝ) (hu : ∑ i, u i = 0) :
    SliceMoments.average Finset.univ q
      (fun S => (equalityImage q (SliceCoefficients.linearPair u) S)^2) =
      (2 * (q : ℝ) - (Fintype.card α : ℝ))^2 *
        ((q : ℝ) * ((Fintype.card α : ℝ) - q) /
          ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1))) * (∑ i, (u i)^2) := by
  calc
    _ = SliceMoments.average Finset.univ q (fun S =>
        (2 * (q : ℝ) - (Fintype.card α : ℝ))^2 *
          (∑ i, u i * SliceMoments.coord i S)^2) := by
      apply SliceMoments.average_congr
      intro S hS
      rw [equalityImage_linearPair q S (Finset.mem_powersetCard.mp hS).2 u hu]
      ring
    _ = _ := by
      rw [SliceMoments.average_mul_left]
      have hm := SliceMoments.average_linear_sq_zero_sum
        (Finset.univ : Finset α) q (by simpa using hN) (by simpa using hq) u (by simpa using hu)
      simp only [Finset.card_univ] at hm
      rw [hm]
      ring

include sectionDecidableEqα in
theorem equalMean_complement (hN : 2 ≤ Fintype.card α) (q : ℕ) :
    1 - SliceMoments.equalMean (Finset.univ : Finset α) q =
      2 * (q : ℝ) * ((Fintype.card α : ℝ) - q) /
        ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1)) := by
  have retainedsectionDecidableEqα := sectionDecidableEqα
  have hc : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hN
  have h0 : (Fintype.card α : ℝ) ≠ 0 := by linarith
  have h1 : (Fintype.card α : ℝ) - 1 ≠ 0 := by linarith
  unfold SliceMoments.equalMean
  simp only [Finset.card_univ]
  field_simp
  ring

def linearGramScalar (q : ℕ) : ℝ :=
  (2 * (q : ℝ) - (Fintype.card α : ℝ))^2 /
    (2 * ((Fintype.card α : ℝ) - 2) *
      SliceMoments.equalMean (Finset.univ : Finset α) q)

theorem average_equalityImage_linearPair_sq_ratio
    (hN : 3 ≤ Fintype.card α) (q : ℕ) (hq : q ≤ Fintype.card α)
    (hp : SliceMoments.equalMean (Finset.univ : Finset α) q ≠ 0)
    (u : α → ℝ) (hu : ∑ i, u i = 0) :
    SliceMoments.average Finset.univ q
      (fun S => (equalityImage q (SliceCoefficients.linearPair u) S)^2) =
      linearGramScalar (α := α) q *
        (SliceMoments.equalMean (Finset.univ : Finset α) q *
          (1 - SliceMoments.equalMean (Finset.univ : Finset α) q)) *
        ((∑ i, ∑ j, (SliceCoefficients.linearPair u i j)^2) / 2) := by
  have hc : (3 : ℝ) ≤ Fintype.card α := by exact_mod_cast hN
  have h0 : (Fintype.card α : ℝ) ≠ 0 := by linarith
  have h1 : (Fintype.card α : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (Fintype.card α : ℝ) - 2 ≠ 0 := by linarith
  have hN' : 2 ≤ Fintype.card α := by omega
  rw [average_equalityImage_linearPair_sq hN' q hq u hu,
    SliceCoefficients.linearPair_norm_sq u hu, equalMean_complement hN' q]
  unfold linearGramScalar
  field_simp

theorem average_normalized_linearPair_sq
    (hN : 3 ≤ Fintype.card α) (q : ℕ) (hq : q ≤ Fintype.card α)
    (hp : 0 < SliceMoments.equalMean (Finset.univ : Finset α) q)
    (hp1 : SliceMoments.equalMean (Finset.univ : Finset α) q < 1)
    (u : α → ℝ) (hu : ∑ i, u i = 0) :
    SliceMoments.average Finset.univ q
      (fun S => (equalityImage q (SliceCoefficients.linearPair u) S /
        Real.sqrt (SliceMoments.equalMean (Finset.univ : Finset α) q *
          (1 - SliceMoments.equalMean (Finset.univ : Finset α) q)))^2) =
      linearGramScalar (α := α) q *
        ((∑ i, ∑ j, (SliceCoefficients.linearPair u i j)^2) / 2) := by
  let v : ℝ := SliceMoments.equalMean (Finset.univ : Finset α) q *
    (1 - SliceMoments.equalMean (Finset.univ : Finset α) q)
  have hv : 0 < v := mul_pos hp (sub_pos.mpr hp1)
  have hs : (Real.sqrt v)^2 = v := Real.sq_sqrt hv.le
  change SliceMoments.average Finset.univ q
    (fun S => (equalityImage q (SliceCoefficients.linearPair u) S / Real.sqrt v)^2) = _
  calc
    _ = SliceMoments.average Finset.univ q
        (fun S => (equalityImage q (SliceCoefficients.linearPair u) S)^2) / v := by
      unfold SliceMoments.average
      simp_rw [div_pow, hs]
      rw [← Finset.sum_div]
      ring
    _ = _ := by
      rw [average_equalityImage_linearPair_sq_ratio hN q hq hp.ne' u hu]
      change (linearGramScalar (α := α) q * v *
        ((∑ i, ∑ j, (SliceCoefficients.linearPair u i j)^2) / 2)) / v = _
      field_simp

include sectionDecidableEqα in
theorem equalMean_pos (hN : 3 ≤ Fintype.card α) (q : ℕ) :
    0 < SliceMoments.equalMean (Finset.univ : Finset α) q := by
  have retainedsectionDecidableEqα := sectionDecidableEqα
  have hN3 : (3 : ℝ) ≤ Fintype.card α := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < Fintype.card α := by linarith
  have hN1 : (0 : ℝ) < (Fintype.card α : ℝ) - 1 := by linarith
  have hN2 : (0 : ℝ) < (Fintype.card α : ℝ) - 2 := by linarith
  have hnprod := mul_pos hN0 hN2
  unfold SliceMoments.equalMean
  simp only [Finset.card_univ]
  apply div_pos _ (mul_pos hN0 hN1)
  nlinarith [sq_nonneg ((q : ℝ) - ((Fintype.card α : ℝ) - q))]

theorem equalMean_lt_one (hN : 2 ≤ Fintype.card α) (q : ℕ)
    (hq0 : 0 < q) (hqN : q < Fintype.card α) :
    SliceMoments.equalMean (Finset.univ : Finset α) q < 1 := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq0
  have hqcard : (q : ℝ) < Fintype.card α := by exact_mod_cast hqN
  have hN2 : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hN
  have hdiff : 0 < 1 - SliceMoments.equalMean (Finset.univ : Finset α) q := by
    rw [equalMean_complement hN q]
    apply div_pos
    · exact mul_pos (mul_pos (by norm_num) hqpos) (sub_pos.mpr hqcard)
    · exact mul_pos (by linarith) (by linarith)
  linarith

theorem average_normalized_linearPair_sq_of_nontrivial
    (hN : 3 ≤ Fintype.card α) (q : ℕ)
    (hq0 : 0 < q) (hqN : q < Fintype.card α)
    (u : α → ℝ) (hu : ∑ i, u i = 0) :
    SliceMoments.average Finset.univ q
      (fun S => (equalityImage q (SliceCoefficients.linearPair u) S /
        Real.sqrt (SliceMoments.equalMean (Finset.univ : Finset α) q *
          (1 - SliceMoments.equalMean (Finset.univ : Finset α) q)))^2) =
      linearGramScalar (α := α) q *
        ((∑ i, ∑ j, (SliceCoefficients.linearPair u i j)^2) / 2) := by
  apply average_normalized_linearPair_sq hN q hqN.le
    (equalMean_pos hN q) (equalMean_lt_one (by omega) q hq0 hqN) u hu

include sectionDecidableEqα in
theorem linearGramScalar_le
    (hN : 3 ≤ Fintype.card α) (q : ℕ)
    (hq0 : 0 < q) (hqN : q < Fintype.card α) :
    linearGramScalar (α := α) q ≤ (Fintype.card α : ℝ) / 2 := by
  have retainedsectionDecidableEqα := sectionDecidableEqα
  have hNc : (3 : ℝ) ≤ Fintype.card α := by exact_mod_cast hN
  have hqc : (1 : ℝ) ≤ q := by exact_mod_cast hq0
  have hqnext : q + 1 ≤ Fintype.card α := by omega
  have hqnextc : (q : ℝ) + 1 ≤ Fintype.card α := by exact_mod_cast hqnext
  have hr : (1 : ℝ) ≤ (Fintype.card α : ℝ) - q := by linarith
  have h := SliceBounds.linear_eigenvalue_le hNc hqc hr
    (by ring : (q : ℝ) + ((Fintype.card α : ℝ) - q) = Fintype.card α)
  simpa only [linearGramScalar, SliceBounds.equalityProbability, SliceMoments.equalMean,
    Finset.card_univ] using h

theorem average_normalized_linearPair_sq_le
    (hN : 3 ≤ Fintype.card α) (q : ℕ)
    (hq0 : 0 < q) (hqN : q < Fintype.card α)
    (u : α → ℝ) (hu : ∑ i, u i = 0) :
    SliceMoments.average Finset.univ q
      (fun S => (equalityImage q (SliceCoefficients.linearPair u) S /
        Real.sqrt (SliceMoments.equalMean (Finset.univ : Finset α) q *
          (1 - SliceMoments.equalMean (Finset.univ : Finset α) q)))^2) ≤
      ((Fintype.card α : ℝ) / 2) *
        ((∑ i, ∑ j, (SliceCoefficients.linearPair u i j)^2) / 2) := by
  rw [average_normalized_linearPair_sq_of_nontrivial hN q hq0 hqN u hu]
  apply mul_le_mul_of_nonneg_right (linearGramScalar_le hN q hq0 hqN)
  positivity

end Problem315.SliceImageNorm

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SliceImageNorm.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/SliceActualSynthesis.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceNormalized
open SliceSynthesis SliceCoefficients

variable {V : Type*} [Fintype V] [DecidableEq V]

 theorem raw_eq_equalityVector (q : ℕ) (i j : V) :
    raw q i j = SliceEuclideanGenerator.equalityVector q
      (SliceMoments.equalMean (Finset.univ : Finset V) q) i j := by
  ext S
  rw [SliceEuclideanGenerator.equalityVector_apply]
  rfl

 theorem synthesis_column (q : ℕ) (c : V → V → ℝ) :
    synthesis (column q) (ofMatrix c) = (denominator V q)⁻¹ •
      ∑ i, ∑ j, c i j • SliceEuclideanGenerator.equalityVector q
        (SliceMoments.equalMean (Finset.univ : Finset V) q) i j := by
  simp only [synthesis_ofMatrix, column, raw_eq_equalityVector,
    Finset.smul_sum, smul_smul]
  simp only [mul_comm]

 theorem synthesis_linearPair_column (q : ℕ) (u : V → ℝ) :
    synthesis (column q) (ofMatrix (linearPair u)) = (denominator V q)⁻¹ •
      ∑ i, ∑ j, (u i + u j) • SliceEuclideanGenerator.equalityVector q
        (SliceMoments.equalMean (Finset.univ : Finset V) q) i j := by
  rw [synthesis_column]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    rw [← raw_eq_equalityVector, raw_diag]
    simp
  · simp [linearPair, hij]

 theorem generator_synthesis_linear (q : ℕ) (u : V → ℝ) (hu : ∑ i, u i = 0) :
    SliceEuclideanGenerator.generator q (synthesis (column q) (ofMatrix (linearPair u))) =
      ((Fintype.card V : ℝ) / 2) • synthesis (column q) (ofMatrix (linearPair u)) := by
  rw [synthesis_linearPair_column, map_smul,
    SliceEuclideanGenerator.generator_additive_equality q _ u hu, smul_smul,
    smul_smul]
  congr 1
  ring

 theorem generator_synthesis_rowZero (q : ℕ) (c : V → V → ℝ)
    (hrow : ∀ i, rowSum c i = 0) (hsym : ∀ i j, c i j = c j i)
    (hdiag : ∀ i, c i i = 0) :
    SliceEuclideanGenerator.generator q (synthesis (column q) (ofMatrix c)) =
      ((Fintype.card V : ℝ) - 1) • synthesis (column q) (ofMatrix c) := by
  have hcol : ∀ j, ∑ i, c i j = 0 := by
    intro j
    simpa only [rowSum, hsym] using hrow j
  rw [synthesis_column, map_smul,
    SliceEuclideanGenerator.generator_rowzero_equality q _ c hdiag hrow hcol,
    smul_smul, smul_smul]
  congr 1
  ring

 theorem synthesis_column_eq_vector (q : ℕ) (c : V → V → ℝ)
    (hdiag : ∀ i, c i i = 0) :
    synthesis (column q) (ofMatrix c) = (2 / denominator V q) •
      SliceMoments.vector Finset.univ q (SliceImageNorm.equalityImage q c) := by
  ext S
  simp only [synthesis_ofMatrix, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, smul_eq_mul, column, raw, 
    SliceMoments.vector, SliceImageNorm.equalityImage]
  have hterm (i j : V) : c i j * ((denominator V q)⁻¹ *
      (if i = j then 0 else SliceMoments.centeredEqual Finset.univ q i j S.val)) =
      (denominator V q)⁻¹ *
        (c i j * SliceMoments.centeredEqual Finset.univ q i j S.val) := by
    by_cases hij : i = j
    · subst j; simp [hdiag]
    · simp only [hij, ite_false]; ring
  simp_rw [hterm, ← Finset.mul_sum]
  ring

 theorem synthesis_linear_norm_sq (q : ℕ) (hN : 3 ≤ Fintype.card V)
    (hq0 : 0 < q) (hqN : q < Fintype.card V)
    (u : V → ℝ) (hu : ∑ i, u i = 0) :
    ‖synthesis (column q) (ofMatrix (linearPair u))‖ ^ 2 =
      SliceImageNorm.linearGramScalar (α := V) q * ‖ofMatrix (linearPair u)‖ ^ 2 := by
  have hp := SliceImageNorm.equalMean_pos hN q
  have hp1 := SliceImageNorm.equalMean_lt_one (by omega : 2 ≤ Fintype.card V) q hq0 hqN
  have hd := denominator_sq (V := V) q hp.le hp1.le
  have hdenpos : 0 < denominator V q := by
    apply Real.sqrt_pos.2
    have hc : (0 : ℝ) < Nat.choose (Fintype.card V) q := by
      exact_mod_cast Nat.choose_pos hqN.le
    exact mul_pos (mul_pos (mul_pos (by norm_num) hc) hp) (sub_pos.mpr hp1)
  have hcoeff : ‖ofMatrix (linearPair u)‖ ^ 2 =
      ∑ i, ∑ j, (linearPair u i j)^2 := by
    rw [← real_inner_self_eq_norm_sq, ofMatrix_inner]
    simp only [pow_two]
  rw [synthesis_column_eq_vector q _ (linearPair_diag u), norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs, SliceMoments.vector_norm_sq _ q
      (by simpa using hqN.le), Finset.card_univ,
    SliceImageNorm.average_equalityImage_linearPair_sq_ratio hN q hqN.le hp.ne' u hu,
    hcoeff, div_pow, hd]
  have hc : (Nat.choose (Fintype.card V) q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hqN.le).ne'
  have hp0 := hp.ne'
  have hp10 : 1 - SliceMoments.equalMean (Finset.univ : Finset V) q ≠ 0 := by linarith
  field_simp

end Problem315.SliceNormalized

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/SliceActualSynthesis.lean -/
