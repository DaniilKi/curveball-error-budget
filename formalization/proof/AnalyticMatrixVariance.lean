import AnalyticCountVariance

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/CountEigenvalue.lean -/
section

namespace OAI

noncomputable section

namespace Problem315.CountEigenvalue

theorem abs_eigenvalue_sub_one_le_one
    {lam M δ : ℝ} (hM : 0 < M) (hδ : |δ| = M)
    (hbound : |(lam - 1) * δ| ≤ M) : |lam - 1| ≤ 1 := by
  rw [abs_mul, hδ] at hbound
  nlinarith

theorem eigenvalue_le_two
    {lam M δ : ℝ} (hM : 0 < M) (hδ : |δ| = M)
    (hbound : |(lam - 1) * δ| ≤ M) : lam ≤ 2 := by
  have h := abs_eigenvalue_sub_one_le_one hM hδ hbound
  have := (abs_le.mp h).2
  linarith

theorem fin_eq_zero_value_of_adjacent_eq {m : ℕ} (b : Fin (m + 1) → ℝ)
    (h : ∀ t : Fin m, b t.succ = b t.castSucc) :
    ∀ t, b t = b 0 := by
  intro t
  induction t using Fin.induction with
  | zero => rfl
  | succ t ih => exact (h t).trans ih

theorem exists_nonzero_adjacent_difference {ι : Type*} {m : ℕ}
    (b : ι → Fin (m + 1) → ℝ)
    (hne : ∃ i s t, b i s ≠ b i t) :
    ∃ i, ∃ t : Fin m, b i t.succ - b i t.castSucc ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨i, s, t, hst⟩ := hne
  have hi : ∀ t : Fin m, b i t.succ = b i t.castSucc := by
    intro t
    exact sub_eq_zero.mp (h i t)
  exact hst ((fin_eq_zero_value_of_adjacent_eq (b i) hi s).trans
    (fin_eq_zero_value_of_adjacent_eq (b i) hi t).symm)

theorem exists_positive_max_abs {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hne : ∃ i, x i ≠ 0) :
    ∃ i, 0 < |x i| ∧ ∀ j, |x j| ≤ |x i| := by
  classical
  obtain ⟨j, hj⟩ := hne
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun k => |x k|) ⟨j, Finset.mem_univ j⟩
  refine ⟨i, lt_of_lt_of_le (abs_pos.mpr hj) (hi j (Finset.mem_univ j)), ?_⟩
  intro k
  exact hi k (Finset.mem_univ k)

theorem eigenvalue_le_two_of_adjacent_coupling
    {ι : Type*} [Fintype ι] {m : ℕ}
    (b : ι → Fin (m + 1) → ℝ) (lam : ℝ)
    (hne : ∃ i s t, b i s ≠ b i t)
    (hcoupling : ∀ i (t : Fin m),
      (∀ j (s : Fin m),
        |b j s.succ - b j s.castSucc| ≤ |b i t.succ - b i t.castSucc|) →
      |(lam - 1) * (b i t.succ - b i t.castSucc)| ≤
        |b i t.succ - b i t.castSucc|) : lam ≤ 2 := by
  obtain ⟨i, t, hit⟩ := exists_nonzero_adjacent_difference b hne
  let x : ι × Fin m → ℝ := fun p => b p.1 p.2.succ - b p.1 p.2.castSucc
  obtain ⟨⟨j, s⟩, hpos, hmax⟩ := exists_positive_max_abs x ⟨(i, t), hit⟩
  exact eigenvalue_le_two hpos rfl (hcoupling j s (fun k u => hmax (k, u)))

theorem exists_nonconstant_of_centered
    {ι : Type*} {m : ℕ} (b p : ι → Fin (m + 1) → ℝ)
    (hmass : ∀ i, ∑ t, p i t = 1)
    (hcenter : ∀ i, ∑ t, p i t * b i t = 0)
    (hne : ∃ i t, b i t ≠ 0) :
    ∃ i s t, b i s ≠ b i t := by
  classical
  by_contra h
  push Not at h
  obtain ⟨i, t, hit⟩ := hne
  have hi : (∑ u, p i u * b i u) = b i t := by
    calc
      _ = ∑ u, p i u * b i t := Finset.sum_congr rfl (fun u _ => by rw [h i u t])
      _ = (∑ u, p i u) * b i t := (Finset.sum_mul _ _ _).symm
      _ = b i t := by rw [hmass, one_mul]
  exact hit (hi.symm.trans (hcenter i))

theorem eigenvalue_le_two_of_centered_adjacent_coupling
    {ι : Type*} [Fintype ι] {m : ℕ}
    (b p : ι → Fin (m + 1) → ℝ) (lam : ℝ)
    (hmass : ∀ i, ∑ t, p i t = 1)
    (hcenter : ∀ i, ∑ t, p i t * b i t = 0)
    (hne : ∃ i t, b i t ≠ 0)
    (hcoupling : ∀ i (t : Fin m),
      (∀ j (s : Fin m),
        |b j s.succ - b j s.castSucc| ≤ |b i t.succ - b i t.castSucc|) →
      |(lam - 1) * (b i t.succ - b i t.castSucc)| ≤
        |b i t.succ - b i t.castSucc|) : lam ≤ 2 := by
  exact eigenvalue_le_two_of_adjacent_coupling b lam
    (exists_nonconstant_of_centered b p hmass hcenter hne) hcoupling

end Problem315.CountEigenvalue

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/CountEigenvalue.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/CountCovering.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.CountCoupling

def prefixMass (p : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, p i

theorem adjacent_transport_identity (p q f : ℕ → ℝ) (s : ℕ)
    (hpEnd : p (s + 1) = 0)
    (hmass : prefixMass p (s + 1) = prefixMass q (s + 2)) :
    (∑ i ∈ Finset.range (s + 2), q i * f i) -
        (∑ i ∈ Finset.range (s + 1), p i * f i) =
      ∑ i ∈ Finset.range (s + 1),
        (prefixMass p (i + 1) - prefixMass q (i + 1)) * (f (i + 1) - f i) := by
  have htotal : (∑ i ∈ Finset.range (s + 2), (q i - p i)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_range_succ (f := p)]
    change prefixMass q (s + 2) - (prefixMass p (s + 1) + p (s + 1)) = 0
    rw [hpEnd, add_zero, hmass, sub_self]
  have hab := Finset.sum_range_by_parts f (fun i => q i - p i) (s + 2)
  simp only [smul_eq_mul, htotal, mul_zero, zero_sub,
    show s + 2 - 1 = s + 1 by omega] at hab
  calc
    _ = ∑ i ∈ Finset.range (s + 2), f i * (q i - p i) := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      rw [Finset.sum_range_succ (f := fun i => f i * p i)]
      simp only [hpEnd, mul_zero, add_zero]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring
    _ = -(∑ i ∈ Finset.range (s + 1),
        (f (i + 1) - f i) * ∑ j ∈ Finset.range (i + 1), (q j - p j)) := hab
    _ = _ := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [prefixMass, Finset.sum_sub_distrib]
      ring

theorem adjacent_two_coordinate_expectation_bound
    (p q b c : ℕ → ℝ) (s : ℕ) (M : ℝ)
    (hpEnd : p (s + 1) = 0)
    (hpMass : prefixMass p (s + 1) = 1)
    (hqMass : prefixMass q (s + 2) = 1)
    (hinterlace : ∀ i ≤ s,
      0 ≤ prefixMass p (i + 1) - prefixMass q (i + 1) ∧
      prefixMass p (i + 1) - prefixMass q (i + 1) ≤ p i)
    (hb : ∀ i ≤ s, |b (i + 1) - b i| ≤ M)
    (hc : ∀ i ≤ s, |c (i + 1) - c i| ≤ M) :
    |(∑ i ∈ Finset.range (s + 2), q i * (b i + c (s + 1 - i))) -
      (∑ i ∈ Finset.range (s + 1), p i * (b i + c (s - i)))| ≤ M := by
  let δ : ℕ → ℝ := fun i => prefixMass p (i + 1) - prefixMass q (i + 1)
  have hid := adjacent_transport_identity p q (fun i => b i + c (s + 1 - i)) s
    hpEnd (hpMass.trans hqMass.symm)
  have hexpand :
      (∑ i ∈ Finset.range (s + 2), q i * (b i + c (s + 1 - i))) -
        (∑ i ∈ Finset.range (s + 1), p i * (b i + c (s - i))) =
      ∑ i ∈ Finset.range (s + 1),
        ((p i - δ i) * (c (s - i + 1) - c (s - i)) +
          δ i * (b (i + 1) - b i)) := by
    calc
      _ = ((∑ i ∈ Finset.range (s + 2), q i * (b i + c (s + 1 - i))) -
          (∑ i ∈ Finset.range (s + 1), p i * (b i + c (s + 1 - i)))) +
          ((∑ i ∈ Finset.range (s + 1), p i * (b i + c (s + 1 - i))) -
          (∑ i ∈ Finset.range (s + 1), p i * (b i + c (s - i)))) := by ring
      _ = _ := by
        rw [hid, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        have his : i ≤ s := by have := Finset.mem_range.mp hi; omega
        have hsub : s + 1 - i = s - i + 1 := by omega
        have hsub' : s + 1 - (i + 1) = s - i := by omega
        simp only [hsub, hsub', δ]
        ring
  rw [hexpand]
  calc
    _ ≤ ∑ i ∈ Finset.range (s + 1),
        |(p i - δ i) * (c (s - i + 1) - c (s - i)) +
          δ i * (b (i + 1) - b i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (s + 1), p i * M := by
      apply Finset.sum_le_sum
      intro i hi
      have his : i ≤ s := by have := Finset.mem_range.mp hi; omega
      have hd0 : 0 ≤ δ i := (hinterlace i his).1
      have hdp : δ i ≤ p i := (hinterlace i his).2
      calc
        _ ≤ |(p i - δ i) * (c (s - i + 1) - c (s - i))| +
            |δ i * (b (i + 1) - b i)| := abs_add_le _ _
        _ = (p i - δ i) * |c (s - i + 1) - c (s - i)| +
            δ i * |b (i + 1) - b i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hdp), abs_of_nonneg hd0]
        _ ≤ (p i - δ i) * M + δ i * M := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (hc (s - i) (Nat.sub_le _ _)) (sub_nonneg.mpr hdp))
            (mul_le_mul_of_nonneg_left (hb i his) hd0)
        _ = p i * M := by ring
    _ = M := by rw [← Finset.sum_mul]; change prefixMass p (s + 1) * M = M; rw [hpMass, one_mul]

def coveredPairProbability (α β s y : ℕ) : ℝ :=
  if y ≤ s then pairWeight α β s y /
    (∑ z ∈ Finset.range (s + 1), pairWeight α β s z) else 0

theorem pairWeight_mass_pos (α β s : ℕ) :
    0 < ∑ y ∈ Finset.range (s + 1), pairWeight α β s y := by
  apply Finset.sum_pos
  · intro y hy
    exact pairWeight_pos α β s y
  · exact ⟨0, Finset.mem_range.mpr (by omega)⟩

theorem coveredPairProbability_mass (α β s : ℕ) :
    prefixMass (coveredPairProbability α β s) (s + 1) = 1 := by
  unfold prefixMass
  calc
    _ = ∑ y ∈ Finset.range (s + 1), pairWeight α β s y /
        (∑ z ∈ Finset.range (s + 1), pairWeight α β s z) := by
      apply Finset.sum_congr rfl
      intro y hy
      have hys : y ≤ s := by have := Finset.mem_range.mp hy; omega
      simp only [coveredPairProbability, ite_eq_left hys]
    _ = 1 := by
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt (pairWeight_mass_pos α β s))

theorem pairExpectation_eq_probability_sum (α β s : ℕ) (b : ℕ → ℝ) :
    pairExpectation α β s b =
      ∑ y ∈ Finset.range (s + 1), coveredPairProbability α β s y * b y := by
  unfold pairExpectation
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y hy
  have hys : y ≤ s := by have := Finset.mem_range.mp hy; omega
  simp only [coveredPairProbability, ite_eq_left hys]
  ring

theorem probability_prefix_eq_expectation (α β s k : ℕ) (hk : k ≤ s + 1) :
    prefixMass (coveredPairProbability α β s) k =
      pairExpectation α β s (fun y => if y < k then 1 else 0) := by
  rw [pairExpectation_eq_probability_sum]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hset : (Finset.range (s + 1)).filter (fun y => y < k) = Finset.range k := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hset]
  rfl

theorem covered_pairExpectation_shift_le_succ_of_antitone (α β s : ℕ) (b : ℕ → ℝ)
    (hb : Antitone b) :
    pairExpectation α β s (fun y => b (y + 1)) ≤ pairExpectation α β (s + 1) b := by
  have h := pairExpectation_succ_le_shift α β s (fun y => -b y)
    (fun _ _ hij => neg_le_neg (hb hij))
  rw [pairExpectation_neg, pairExpectation_neg] at h
  linarith

theorem coveredPairProbability_interlace (α β s i : ℕ) (hi : i ≤ s) :
    0 ≤ prefixMass (coveredPairProbability α β s) (i + 1) -
      prefixMass (coveredPairProbability α β (s + 1)) (i + 1) ∧
    prefixMass (coveredPairProbability α β s) (i + 1) -
      prefixMass (coveredPairProbability α β (s + 1)) (i + 1) ≤
        coveredPairProbability α β s i := by
  have hantitone (k : ℕ) : Antitone (fun y : ℕ => if y < k then (1 : ℝ) else 0) := by
    intro y z hyz
    dsimp only
    split_ifs <;> norm_num ; omega
  have hfirst := pairExpectation_succ_le_of_antitone α β s
    (fun y => if y < i + 1 then (1 : ℝ) else 0) (hantitone (i + 1))
  rw [← probability_prefix_eq_expectation α β (s + 1) (i + 1) (by omega),
    ← probability_prefix_eq_expectation α β s (i + 1) (by omega)] at hfirst
  refine ⟨sub_nonneg.mpr hfirst, ?_⟩
  have hsecond := covered_pairExpectation_shift_le_succ_of_antitone α β s
    (fun y => if y < i + 1 then (1 : ℝ) else 0) (hantitone (i + 1))
  simp only [Nat.add_lt_add_iff_right] at hsecond
  rw [← probability_prefix_eq_expectation α β s i (by omega),
    ← probability_prefix_eq_expectation α β (s + 1) (i + 1) (by omega)] at hsecond
  have hprefix : prefixMass (coveredPairProbability α β s) (i + 1) =
      prefixMass (coveredPairProbability α β s) i + coveredPairProbability α β s i := by
    exact Finset.sum_range_succ _ _
  linarith

theorem pairExpectation_adjacent_sum_bound (α β s : ℕ) (b c : ℕ → ℝ) (M : ℝ)
    (hb : ∀ i ≤ s, |b (i + 1) - b i| ≤ M)
    (hc : ∀ i ≤ s, |c (i + 1) - c i| ≤ M) :
    |pairExpectation α β (s + 1) (fun i => b i + c (s + 1 - i)) -
      pairExpectation α β s (fun i => b i + c (s - i))| ≤ M := by
  rw [pairExpectation_eq_probability_sum, pairExpectation_eq_probability_sum]
  exact adjacent_two_coordinate_expectation_bound
    (coveredPairProbability α β s) (coveredPairProbability α β (s + 1)) b c s M
    (by simp [coveredPairProbability]) (coveredPairProbability_mass α β s)
    (coveredPairProbability_mass α β (s + 1)) (coveredPairProbability_interlace α β s) hb hc

end Problem315.CountCoupling

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/CountCovering.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/CountEigenEquation.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.CountEigenvalue

theorem count_eigenvalue_le_two
    {ι : Type*} [Fintype ι] (m : ℕ)
    (α : ι → ℕ) (left right : ι → ι) (b : ι → ℕ → ℝ) (lam : ℝ)
    (hne : ∃ i, ∃ s t : Fin (m + 1), b i s.val ≠ b i t.val)
    (heig : ∀ i t, t ≤ m →
      (lam - 1) * b i t =
        CountCoupling.pairExpectation (α (left i)) (α (right i)) (m - t)
          (fun y => b (left i) y + b (right i) (m - t - y))) : lam ≤ 2 := by
  apply eigenvalue_le_two_of_adjacent_coupling
    (fun i (t : Fin (m + 1)) => b i t.val) lam hne
  intro i t hmax
  let s := m - (t.val + 1)
  have htotal : s + 1 = m - t.val := by dsimp [s]; omega
  have hleft : ∀ u ≤ s,
      |b (left i) (u + 1) - b (left i) u| ≤
        |b i (t.val + 1) - b i t.val| := by
    intro u hu
    have hum : u < m := by dsimp [s] at hu; have := t.isLt; omega
    exact hmax (left i) ⟨u, hum⟩
  have hright : ∀ u ≤ s,
      |b (right i) (u + 1) - b (right i) u| ≤
        |b i (t.val + 1) - b i t.val| := by
    intro u hu
    have hum : u < m := by dsimp [s] at hu; have := t.isLt; omega
    exact hmax (right i) ⟨u, hum⟩
  have hcover := CountCoupling.pairExpectation_adjacent_sum_bound
    (α (left i)) (α (right i)) s (b (left i)) (b (right i))
    |b i (t.val + 1) - b i t.val| hleft hright
  rw [htotal] at hcover
  change |(lam - 1) * (b i (t.val + 1) - b i t.val)| ≤
    |b i (t.val + 1) - b i t.val|
  rw [mul_sub, heig i (t.val + 1) (by have := t.isLt; omega),
    heig i t.val (by have := t.isLt; omega)]
  simpa only [s, abs_sub_comm] using hcover

theorem count_eigenvalue_le_two_of_centered
    {ι : Type*} [Fintype ι] (m : ℕ)
    (α : ι → ℕ) (left right : ι → ι) (b : ι → ℕ → ℝ)
    (p : ι → Fin (m + 1) → ℝ) (lam : ℝ)
    (hmass : ∀ i, ∑ t, p i t = 1)
    (hcenter : ∀ i, ∑ t, p i t * b i t.val = 0)
    (hne : ∃ i, ∃ t : Fin (m + 1), b i t.val ≠ 0)
    (heig : ∀ i t, t ≤ m →
      (lam - 1) * b i t =
        CountCoupling.pairExpectation (α (left i)) (α (right i)) (m - t)
          (fun y => b (left i) y + b (right i) (m - t - y))) : lam ≤ 2 := by
  exact count_eigenvalue_le_two m α left right b lam
    (exists_nonconstant_of_centered (fun i (t : Fin (m + 1)) => b i t.val)
      p hmass hcenter hne) heig

theorem count_operator_quadratic_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (m : ℕ)
    (α : ι → ℕ) (left right : ι → ι)
    (b : E → ι → ℕ → ℝ) (p : ι → Fin (m + 1) → ℝ)
    (hmass : ∀ i, ∑ t, p i t = 1)
    (hcenter : ∀ x i, ∑ t, p i t * b x i t.val = 0)
    (hdetect : ∀ x, x ≠ 0 → ∃ i, ∃ t : Fin (m + 1), b x i t.val ≠ 0)
    (heig : ∀ (lam : ℝ) (x : E), T x = lam • x → ∀ i t, t ≤ m →
      (lam - 1) * b x i t =
        CountCoupling.pairExpectation (α (left i)) (α (right i)) (m - t)
          (fun y => b x (left i) y + b x (right i) (m - t - y))) :
    ∀ x : E, ⟪x, T x⟫ ≤ 2 * ‖x‖ ^ 2 := by
  classical
  let basis := hT.eigenvectorBasis (rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  let ev := hT.eigenvalues (rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  have hbe (i : Fin (Module.finrank ℝ E)) : T (basis i) = ev i • basis i :=
    hT.apply_eigenvectorBasis rfl i
  have hev (i : Fin (Module.finrank ℝ E)) : ev i ≤ 2 := by
    apply count_eigenvalue_le_two_of_centered m α left right (b (basis i)) p (ev i)
      hmass (hcenter (basis i))
    · apply hdetect
      intro hz
      have hn := basis.orthonormal.1 i
      rw [hz, norm_zero] at hn
      norm_num at hn
    · exact heig (ev i) (basis i) (hbe i)
  intro x
  rw [← basis.sum_inner_mul_inner x (T x), ← basis.sum_sq_inner_right x,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hcoord : ⟪basis i, T x⟫ = ev i * ⟪basis i, x⟫ := by
    rw [← hT (basis i) x, hbe, inner_smul_left]
    simp
  rw [hcoord, real_inner_comm x (basis i)]
  have hi := hev i
  nlinarith [sq_nonneg ⟪basis i, x⟫]

end Problem315.CountEigenvalue

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/CountEigenEquation.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/TripleCountEigenvalue.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.TripleCountLaw

def marginal (a : Fin 3 → ℕ) (m : ℕ) (i : Fin 3) (t : Fin (m + 1)) : ℝ :=
  ∑ x : Triple m, if x.val i = t then probability a x else 0

theorem marginal_sum (a : Fin 3 → ℕ) (m : ℕ) (i : Fin 3) :
    ∑ t : Fin (m + 1), marginal a m i t = 1 := by
  classical
  unfold marginal
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact probability_sum a m

theorem marginal_positive (a : Fin 3 → ℕ) (m : ℕ) (i : Fin 3)
    (t : Fin (m + 1)) : 0 < marginal a m i t := by
  have h := marginal_pos a m (Equiv.swap 0 i) t.val (by have := t.isLt; omega)
  simpa only [marginal, Equiv.swap_apply_left, Fin.val_eq_val] using h

theorem conditional_eigenvalue_le_two (a : Fin 3 → ℕ) (m : ℕ)
    (b : Fin 3 → ℕ → ℝ) (lam : ℝ)
    (hcenter : ∀ i, ∑ t : Fin (m + 1), marginal a m i t * b i t.val = 0)
    (hne : ∃ i, ∃ t : Fin (m + 1), b i t.val ≠ 0)
    (heig : ∀ i t, t ≤ m → lam * b i t =
      conditionalAverage a (rowSum b : Triple m → ℝ) (Equiv.swap 0 i) t) :
    lam ≤ 2 := by
  apply CountEigenvalue.count_eigenvalue_le_two_of_centered m a
    (fun i => Equiv.swap 0 i 1) (fun i => Equiv.swap 0 i 2) b
    (marginal a m) lam (marginal_sum a m) hcenter hne
  intro i t ht
  have h := heig i t ht
  rw [conditionalAverage_rowSum a m b (Equiv.swap 0 i) t ht,
    Equiv.swap_apply_left] at h
  nlinarith

end Problem315.TripleCountLaw

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/TripleCountEigenvalue.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/WeightedConditionalVariance.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.WeightedConditional

variable {Ω ι β : Type*} [Fintype Ω] [sectionFintypeι : Fintype ι] [sectionFintypeβ : Fintype β]
  [sectionDecidableEqβ : DecidableEq β]

def conditionalSum (w : Ω → ℝ) (key : ι → Ω → β)
    (i : ι) (t : β) (f : Ω → ℝ) : ℝ :=
  ∑ x, if key i x = t then w x * f x else 0

include sectionFintypeι in
theorem sum_mul_conditionalSum (w : Ω → ℝ) (key : ι → Ω → β)
    (i : ι) (g : β → ℝ) (f : Ω → ℝ) :
    (∑ t, g t * conditionalSum w key i t f) =
      ∑ x, w x * g (key i x) * f x := by
  have retainedsectionFintypeι := sectionFintypeι
  classical
  unfold conditionalSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  ring

theorem sum_conditionalSum (w : Ω → ℝ) (key : ι → Ω → β)
    (i : ι) (f : Ω → ℝ) :
    (∑ t, conditionalSum w key i t f) = ∑ x, w x * f x := by
  simpa using sum_mul_conditionalSum w key i (fun _ => 1) f

include sectionFintypeι sectionFintypeβ in
theorem conditionalSum_add (w : Ω → ℝ) (key : ι → Ω → β)
    (i : ι) (t : β) (f g : Ω → ℝ) :
    conditionalSum w key i t (fun x => f x + g x) =
      conditionalSum w key i t f + conditionalSum w key i t g := by
  have retainedsectionFintypeι := sectionFintypeι
  have retainedsectionFintypeβ := sectionFintypeβ
  unfold conditionalSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  split <;> simp_all [mul_add]

include sectionFintypeι sectionFintypeβ in
theorem conditionalSum_smul (w : Ω → ℝ) (key : ι → Ω → β)
    (i : ι) (t : β) (c : ℝ) (f : Ω → ℝ) :
    conditionalSum w key i t (fun x => c * f x) =
      c * conditionalSum w key i t f := by
  have retainedsectionFintypeι := sectionFintypeι
  have retainedsectionFintypeβ := sectionFintypeβ
  unfold conditionalSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  split <;> simp_all [mul_left_comm]

abbrev Space (ι β : Type*) [Fintype ι] [Fintype β] :=
  EuclideanSpace ℝ (ι × β)

def decode (p : ι → β → ℝ) (z : Space ι β) (i : ι) (t : β) : ℝ :=
  z (i, t) / Real.sqrt (p i t)

def rowSum (p : ι → β → ℝ) (key : ι → Ω → β) (z : Space ι β) (x : Ω) : ℝ :=
  ∑ i, decode p z i (key i x)

def gram (w : Ω → ℝ) (p : ι → β → ℝ) (key : ι → Ω → β) :
    Space ι β →ₗ[ℝ] Space ι β where
  toFun z := WithLp.toLp 2 (fun it =>
    conditionalSum w key it.1 it.2 (rowSum p key z) / Real.sqrt (p it.1 it.2))
  map_add' z z' := by
    ext it
    change conditionalSum w key it.1 it.2 (rowSum p key (z + z')) /
      Real.sqrt (p it.1 it.2) = _
    have hs : rowSum p key (z + z') = fun x => rowSum p key z x + rowSum p key z' x := by
      funext x
      simp [rowSum, decode, add_div, Finset.sum_add_distrib]
    rw [hs, conditionalSum_add, add_div]
    rfl
  map_smul' c z := by
    ext it
    change conditionalSum w key it.1 it.2 (rowSum p key (c • z)) /
      Real.sqrt (p it.1 it.2) = c * _
    have hs : rowSum p key (c • z) = fun x => c * rowSum p key z x := by
      funext x
      simp [rowSum, decode, mul_div_assoc, Finset.mul_sum]
    rw [hs, conditionalSum_smul]
    change (c * _) / _ = c * (_ / _)
    ring

@[simp] theorem gram_apply (w : Ω → ℝ) (p : ι → β → ℝ)
    (key : ι → Ω → β) (z : Space ι β) (i : ι) (t : β) :
    gram w p key z (i,t) =
      conditionalSum w key i t (rowSum p key z) / Real.sqrt (p i t) := rfl

theorem inner_gram (w : Ω → ℝ) (p : ι → β → ℝ)
    (key : ι → Ω → β) (z z' : Space ι β) :
    inner ℝ z (gram w p key z') =
      ∑ x, w x * rowSum p key z x * rowSum p key z' x := by
  classical
  rw [real_inner_comm]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fintype.sum_prod_type,
    gram_apply]
  have hrew (i : ι) :
      (∑ t, z (i,t) * (conditionalSum w key i t (rowSum p key z') /
        Real.sqrt (p i t))) =
      ∑ x, w x * decode p z i (key i x) * rowSum p key z' x := by
    rw [← sum_mul_conditionalSum w key i (decode p z i) (rowSum p key z')]
    apply Finset.sum_congr rfl
    intro t ht
    simp only [decode]
    ring
  simp_rw [hrew]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  unfold rowSum
  rw [← Finset.sum_mul, ← Finset.mul_sum]

theorem gram_symmetric (w : Ω → ℝ) (p : ι → β → ℝ)
    (key : ι → Ω → β) : (gram w p key).IsSymmetric := by
  intro z z'
  rw [real_inner_comm, inner_gram, inner_gram]
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem gram_nonneg (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (p : ι → β → ℝ) (key : ι → Ω → β) (z : Space ι β) :
    0 ≤ inner ℝ z (gram w p key z) := by
  rw [inner_gram]
  apply Finset.sum_nonneg
  intro x hx
  nlinarith [hw x, sq_nonneg (rowSum p key z x)]

def centered (p : ι → β → ℝ) : Submodule ℝ (Space ι β) where
  carrier := {z | ∀ i, ∑ t, Real.sqrt (p i t) * z (i,t) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro z z' hz hz' i
    simp only [Set.mem_ofPred_eq] at hz hz'
    simp only [PiLp.add_apply, mul_add, Finset.sum_add_distrib, hz i, hz' i, add_zero]
  smul_mem' := by
    intro c z hz i
    simp only [Set.mem_ofPred_eq] at hz
    simp only [PiLp.smul_apply, smul_eq_mul]
    simp_rw [mul_left_comm (Real.sqrt _) c]
    rw [← Finset.mul_sum, hz i, mul_zero]

include sectionDecidableEqβ in
@[simp] theorem mem_centered (p : ι → β → ℝ) (z : Space ι β) :
    z ∈ centered p ↔ ∀ i, ∑ t, Real.sqrt (p i t) * z (i,t) = 0 := by
  have retainedsectionDecidableEqβ := sectionDecidableEqβ
  exact Iff.rfl

include sectionDecidableEqβ in
theorem marginal_mul_decode (p : ι → β → ℝ) (hp : ∀ i t, 0 < p i t)
    (z : Space ι β) (i : ι) (t : β) :
    p i t * decode p z i t = Real.sqrt (p i t) * z (i,t) := by
  have retainedsectionDecidableEqβ := sectionDecidableEqβ
  have hs : Real.sqrt (p i t) ≠ 0 := (Real.sqrt_pos.2 (hp i t)).ne'
  unfold decode
  calc
    p i t * (z (i,t) / Real.sqrt (p i t)) =
        (Real.sqrt (p i t) * Real.sqrt (p i t)) *
          (z (i,t) / Real.sqrt (p i t)) := by
      rw [Real.mul_self_sqrt (hp i t).le]
    _ = Real.sqrt (p i t) * z (i,t) := by field_simp

theorem weighted_rowSum (w : Ω → ℝ) (p : ι → β → ℝ)
    (hp : ∀ i t, 0 < p i t) (key : ι → Ω → β)
    (hmarginal : ∀ i t, conditionalSum w key i t (fun _ => 1) = p i t)
    (z : Space ι β) :
    (∑ x, w x * rowSum p key z x) =
      ∑ i, ∑ t, Real.sqrt (p i t) * z (i,t) := by
  classical
  unfold rowSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have h := sum_mul_conditionalSum w key i (decode p z i) (fun _ => 1)
  simp only [hmarginal, mul_one] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro t ht
  rw [mul_comm, marginal_mul_decode p hp]

theorem gram_preserves_centered (w : Ω → ℝ) (p : ι → β → ℝ)
    (hp : ∀ i t, 0 < p i t) (key : ι → Ω → β)
    (hmarginal : ∀ i t, conditionalSum w key i t (fun _ => 1) = p i t)
    (z : Space ι β) (hz : z ∈ centered p) : gram w p key z ∈ centered p := by
  classical
  intro i
  calc
    (∑ t, Real.sqrt (p i t) * gram w p key z (i,t)) =
        ∑ t, conditionalSum w key i t (rowSum p key z) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [gram_apply]
      have hs : Real.sqrt (p i t) ≠ 0 := (Real.sqrt_pos.2 (hp i t)).ne'
      field_simp
    _ = ∑ x, w x * rowSum p key z x := sum_conditionalSum w key i _
    _ = ∑ j, ∑ t, Real.sqrt (p j t) * z (j,t) :=
      weighted_rowSum w p hp key hmarginal z
    _ = 0 := by
      have hz' := (mem_centered p z).mp hz
      simp only [hz', Finset.sum_const_zero]

theorem conditional_eigen_equation (w : Ω → ℝ) (p : ι → β → ℝ)
    (hp : ∀ i t, 0 < p i t) (key : ι → Ω → β)
    (z : Space ι β) (lam : ℝ) (heig : gram w p key z = lam • z)
    (i : ι) (t : β) :
    lam * decode p z i t =
      conditionalSum w key i t (rowSum p key z) / p i t := by
  have hs : Real.sqrt (p i t) ≠ 0 := (Real.sqrt_pos.2 (hp i t)).ne'
  have he := congrArg (fun q : Space ι β => q (i,t)) heig
  change conditionalSum w key i t (rowSum p key z) / Real.sqrt (p i t) =
    lam * z (i,t) at he
  calc
    lam * decode p z i t = (lam * z (i,t)) / Real.sqrt (p i t) := by
      unfold decode
      ring
    _ = (conditionalSum w key i t (rowSum p key z) / Real.sqrt (p i t)) /
        Real.sqrt (p i t) := by rw [he]
    _ = conditionalSum w key i t (rowSum p key z) / p i t := by
      rw [div_div, Real.mul_self_sqrt (hp i t).le]

def encode (p : ι → β → ℝ) (b : ι → β → ℝ) : Space ι β :=
  WithLp.toLp 2 (fun it => Real.sqrt (p it.1 it.2) * b it.1 it.2)

include sectionDecidableEqβ in
@[simp] theorem decode_encode (p : ι → β → ℝ) (hp : ∀ i t, 0 < p i t)
    (b : ι → β → ℝ) (i : ι) (t : β) : decode p (encode p b) i t = b i t := by
  have retainedsectionDecidableEqβ := sectionDecidableEqβ
  unfold decode encode
  change Real.sqrt (p i t) * b i t / Real.sqrt (p i t) = b i t
  exact mul_div_cancel_left₀ _ (Real.sqrt_pos.2 (hp i t)).ne'

include sectionDecidableEqβ in
theorem encode_mem_centered (p : ι → β → ℝ) (hp : ∀ i t, 0 < p i t)
    (b : ι → β → ℝ) (hb : ∀ i, ∑ t, p i t * b i t = 0) :
    encode p b ∈ centered p := by
  have retainedsectionDecidableEqβ := sectionDecidableEqβ
  intro i
  convert hb i using 1
  apply Finset.sum_congr rfl
  intro t ht
  change Real.sqrt (p i t) * (Real.sqrt (p i t) * b i t) = p i t * b i t
  rw [← mul_assoc, Real.mul_self_sqrt (hp i t).le]

include sectionDecidableEqβ in
theorem norm_encode_sq (p : ι → β → ℝ) (hp : ∀ i t, 0 < p i t)
    (b : ι → β → ℝ) :
    ‖encode p b‖ ^ 2 = ∑ i, ∑ t, p i t * (b i t) ^ 2 := by
  have retainedsectionDecidableEqβ := sectionDecidableEqβ
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro t ht
  change (Real.sqrt (p i t) * b i t) ^ 2 = p i t * (b i t) ^ 2
  rw [mul_pow, Real.sq_sqrt (hp i t).le]

theorem centered_variance_le_of_eigenvalue_bound
    (w : Ω → ℝ) (p : ι → β → ℝ) (hp : ∀ i t, 0 < p i t)
    (key : ι → Ω → β)
    (hmarginal : ∀ i t, conditionalSum w key i t (fun _ => 1) = p i t)
    (C : ℝ)
    (heigen : ∀ (lam : ℝ) (b : ι → β → ℝ),
      (∀ i, ∑ t, p i t * b i t = 0) →
      (∃ i t, b i t ≠ 0) →
      (∀ i t, lam * b i t =
        conditionalSum w key i t (fun x => ∑ j, b j (key j x)) / p i t) →
      lam ≤ C)
    (b : ι → β → ℝ) (hb : ∀ i, ∑ t, p i t * b i t = 0) :
    (∑ x, w x * (∑ i, b i (key i x)) ^ 2) ≤
      C * ∑ i, ∑ t, p i t * (b i t) ^ 2 := by
  classical
  let U := centered p
  let T := (gram w p key).restrict (gram_preserves_centered w p hp key hmarginal)
  have hT : T.IsSymmetric :=
    (gram_symmetric w p key).restrict_invariant
      (gram_preserves_centered w p hp key hmarginal)
  let basis := hT.eigenvectorBasis (rfl : Module.finrank ℝ U = Module.finrank ℝ U)
  let ev := hT.eigenvalues (rfl : Module.finrank ℝ U = Module.finrank ℝ U)
  have hbe (k : Fin (Module.finrank ℝ U)) : T (basis k) = ev k • basis k :=
    hT.apply_eigenvectorBasis rfl k
  have hev (k : Fin (Module.finrank ℝ U)) : ev k ≤ C := by
    apply heigen (ev k) (decode p (basis k : Space ι β))
    · intro i
      simp_rw [marginal_mul_decode p hp]
      exact (basis k).property i
    · by_contra hz
      push Not at hz
      have hz0 : (basis k : Space ι β) = 0 := by
        ext it
        have h := hz it.1 it.2
        unfold decode at h
        exact (div_eq_zero_iff).mp h |>.resolve_right (Real.sqrt_pos.2 (hp it.1 it.2)).ne'
      have hzero : basis k = 0 := Subtype.ext hz0
      have hn := basis.orthonormal.1 k
      rw [hzero, norm_zero] at hn
      norm_num at hn
    · intro i t
      exact conditional_eigen_equation w p hp key _ (ev k)
        (congrArg Subtype.val (hbe k)) i t
  have hquad (z : U) : inner ℝ z (T z) ≤ C * ‖z‖ ^ 2 := by
    rw [← basis.sum_inner_mul_inner z (T z), ← basis.sum_sq_inner_right z,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hcoord : inner ℝ (basis k) (T z) = ev k * inner ℝ (basis k) z := by
      rw [← hT (basis k) z, hbe]
      exact real_inner_smul_left (basis k : U) z (ev k)
    rw [hcoord, real_inner_comm z (basis k)]
    have hk := hev k
    nlinarith [sq_nonneg (inner ℝ (basis k) z)]
  let z : U := ⟨encode p b, encode_mem_centered p hp b hb⟩
  have h := hquad z
  change inner ℝ (encode p b) (gram w p key (encode p b)) ≤ C * ‖encode p b‖ ^ 2 at h
  rw [inner_gram, norm_encode_sq p hp] at h
  simpa only [rowSum, decode_encode p hp, mul_assoc, ← pow_two] using h

end Problem315.WeightedConditional

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/WeightedConditionalVariance.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/TripleCountGram.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.TripleCountLaw

def countKey (m : ℕ) (i : Fin 3) (x : Triple m) : Fin (m + 1) := x.val i

def decodedNat (a : Fin 3 → ℕ) (m : ℕ)
    (z : WeightedConditional.Space (Fin 3) (Fin (m + 1)))
    (i : Fin 3) (t : ℕ) : ℝ :=
  if h : t < m + 1 then WeightedConditional.decode (marginal a m) z i ⟨t, h⟩ else 0

@[simp] theorem decodedNat_fin (a : Fin 3 → ℕ) (m : ℕ)
    (z : WeightedConditional.Space (Fin 3) (Fin (m + 1)))
    (i : Fin 3) (t : Fin (m + 1)) :
    decodedNat a m z i t.val = WeightedConditional.decode (marginal a m) z i t := by
  simp [decodedNat, t.isLt]

theorem count_marginal_eq (a : Fin 3 → ℕ) (m : ℕ) (i : Fin 3) (t : Fin (m + 1)) :
    WeightedConditional.conditionalSum (probability a : Triple m → ℝ) (countKey m)
      i t (fun _ => 1) = marginal a m i t := by
  simp [WeightedConditional.conditionalSum, countKey, marginal]

theorem conditionalSum_ratio (a : Fin 3 → ℕ) (m : ℕ) (f : Triple m → ℝ)
    (i : Fin 3) (t : Fin (m + 1)) :
    WeightedConditional.conditionalSum (probability a) (countKey m) i t f /
      marginal a m i t = conditionalAverage a f (Equiv.swap 0 i) t.val := by
  rw [← normalized_conditionalAverage]
  simp only [WeightedConditional.conditionalSum, countKey, marginal,
    Equiv.swap_apply_left, Fin.val_eq_val]
  rfl

theorem rowSum_decodedNat (a : Fin 3 → ℕ) (m : ℕ)
    (z : WeightedConditional.Space (Fin 3) (Fin (m + 1))) :
    WeightedConditional.rowSum (marginal a m) (countKey m) z =
      rowSum (decodedNat a m z) := by
  funext x
  simp [WeightedConditional.rowSum, rowSum, countKey]

theorem count_gram_eigenvalue_le_two (a : Fin 3 → ℕ) (m : ℕ)
    (z : WeightedConditional.Space (Fin 3) (Fin (m + 1)))
    (hz : z ∈ WeightedConditional.centered (marginal a m)) (hne : z ≠ 0)
    (lam : ℝ)
    (heig : WeightedConditional.gram (probability a : Triple m → ℝ)
      (marginal a m) (countKey m) z = lam • z) : lam ≤ 2 := by
  apply conditional_eigenvalue_le_two a m (decodedNat a m z) lam
  · intro i
    simp only [decodedNat_fin]
    simp_rw [WeightedConditional.marginal_mul_decode (marginal a m)
      (marginal_positive a m)]
    exact hz i
  · by_contra h
    push Not at h
    apply hne
    ext it
    obtain ⟨i, t⟩ := it
    have ht := h i t
    simp only [decodedNat_fin, WeightedConditional.decode] at ht
    exact (div_eq_zero_iff.mp ht).resolve_right
      (Real.sqrt_pos.mpr (marginal_positive a m i t)).ne'
  · intro i t ht
    let t' : Fin (m + 1) := ⟨t, by omega⟩
    have h := WeightedConditional.conditional_eigen_equation
      (probability a : Triple m → ℝ) (marginal a m) (marginal_positive a m)
      (countKey m) z lam heig i t'
    rw [rowSum_decodedNat, conditionalSum_ratio] at h
    simpa [decodedNat, t', show t < m + 1 by omega] using h

theorem count_row_variance_le_two (a : Fin 3 → ℕ) (m : ℕ)
    (b : Fin 3 → Fin (m + 1) → ℝ)
    (hb : ∀ i, ∑ t : Fin (m + 1), marginal a m i t * b i t = 0) :
    (∑ x : Triple m, probability a x * (∑ i : Fin 3, b i (x.val i)) ^ 2) ≤
      2 * ∑ i : Fin 3, ∑ t : Fin (m + 1), marginal a m i t * (b i t) ^ 2 := by
  apply WeightedConditional.centered_variance_le_of_eigenvalue_bound
    (probability a : Triple m → ℝ) (marginal a m) (marginal_positive a m)
    (countKey m) (count_marginal_eq a m) 2 _ b hb
  intro lam c hc hne heig
  let cNat : Fin 3 → ℕ → ℝ := fun i t =>
    if h : t < m + 1 then c i ⟨t, h⟩ else 0
  have hcNat (i : Fin 3) (t : Fin (m + 1)) : cNat i t.val = c i t := by
    dsimp only [cNat]
    rw [dite_eq_left t.isLt]
  apply conditional_eigenvalue_le_two a m cNat lam
  · intro i
    simpa only [hcNat] using hc i
  · obtain ⟨i, t, ht⟩ := hne
    exact ⟨i, t, by simpa only [hcNat] using ht⟩
  · intro i t ht
    let t' : Fin (m + 1) := ⟨t, by omega⟩
    have h := heig i t'
    rw [conditionalSum_ratio] at h
    have hr : (fun x : Triple m => ∑ j : Fin 3, c j (countKey m j x)) =
        rowSum cNat := by
      funext x
      simp only [rowSum, countKey, hcNat]
    rw [hr] at h
    simpa only [← hcNat] using h

def countExpectation (a : Fin 3 → ℕ) {m : ℕ} (f : Triple m → ℝ) : ℝ :=
  ∑ x : Triple m, probability a x * f x

def countVariance (a : Fin 3 → ℕ) {m : ℕ} (f : Triple m → ℝ) : ℝ :=
  countExpectation a (fun x => (f x - countExpectation a f) ^ 2)

theorem countExpectation_row (a : Fin 3 → ℕ) (m : ℕ)
    (i : Fin 3) (b : Fin (m + 1) → ℝ) :
    countExpectation a (fun x : Triple m => b (x.val i)) =
      ∑ t : Fin (m + 1), marginal a m i t * b t := by
  have h := WeightedConditional.sum_mul_conditionalSum
    (probability a : Triple m → ℝ) (countKey m) i b (fun _ => 1)
  simp only [count_marginal_eq, mul_one, countKey] at h
  unfold countExpectation
  rw [← h]
  exact Finset.sum_congr rfl (fun t _ => mul_comm _ _)

theorem countExpectation_sum (a : Fin 3 → ℕ) (m : ℕ)
    (f : Fin 3 → Triple m → ℝ) :
    countExpectation a (fun x => ∑ i, f i x) =
      ∑ i, countExpectation a (f i) := by
  unfold countExpectation
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem count_variance_sum_le_two (a : Fin 3 → ℕ) (m : ℕ)
    (b : Fin 3 → Fin (m + 1) → ℝ) :
    countVariance a (fun x : Triple m => ∑ i, b i (x.val i)) ≤
      2 * ∑ i : Fin 3, countVariance a (fun x : Triple m => b i (x.val i)) := by
  let μ : Fin 3 → ℝ := fun i => countExpectation a (fun x : Triple m => b i (x.val i))
  let c : Fin 3 → Fin (m + 1) → ℝ := fun i t => b i t - μ i
  have hc (i : Fin 3) : ∑ t, marginal a m i t * c i t = 0 := by
    simp only [c, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      marginal_sum, one_mul]
    exact sub_eq_zero.mpr (countExpectation_row a m i (b i)).symm
  have h := count_row_variance_le_two a m c hc
  have hleft : countVariance a (fun x : Triple m => ∑ i, b i (x.val i)) =
      ∑ x : Triple m, probability a x * (∑ i, c i (x.val i)) ^ 2 := by
    unfold countVariance
    rw [countExpectation_sum]
    simp only [countExpectation, c, Finset.sum_sub_distrib, μ]
  have hright (i : Fin 3) : countVariance a (fun x : Triple m => b i (x.val i)) =
      ∑ t, marginal a m i t * (c i t) ^ 2 := by
    exact countExpectation_row a m i (fun t => (c i t) ^ 2)
  rw [hleft]
  simp_rw [hright]
  exact h

end Problem315.TripleCountLaw

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/TripleCountGram.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/VariableBlockVariance.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.VariableBlockVariance
open FixedBlockMarginal (average)
open TripleCountLaw (Triple)

variable (U W : Type*) [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]

def sizes (o : Fin 3 → ℕ) {m : ℕ} (x : Triple m) (i : Fin 3) : ℕ :=
  (x.val i).val + o i

abbrev Fiber (m : ℕ) (u w : Fin 3 → ℕ) (x : Triple m) :=
  FixedBlockVariance.State (α := U) (β := W) (sizes u x) (sizes w x)

abbrev Family (m : ℕ) (u w : Fin 3 → ℕ) :=
  Σ x : Triple m, Fiber U W m u w x

variable {U W}

theorem sum_sizes (o : Fin 3 → ℕ) {m : ℕ} (x : Triple m) :
    ∑ i, sizes o x i = m + ∑ i, o i := by
  simp only [sizes, Finset.sum_add_distrib, x.property]

theorem fiber_nonempty (m : ℕ) (u w : Fin 3 → ℕ)
    (hU : m + ∑ i, u i = Fintype.card U)
    (hW : m + ∑ i, w i = Fintype.card W) (x : Triple m) :
    Nonempty (Fiber U W m u w x) := by
  obtain ⟨c⟩ := FixedBlock.partition_nonempty (α := U) (sizes u x)
    ((sum_sizes u x).trans hU)
  obtain ⟨d⟩ := FixedBlock.partition_nonempty (α := W) (sizes w x)
    ((sum_sizes w x).trans hW)
  exact ⟨(c, d)⟩

theorem pairSizeWeight_eq (m : ℕ) (u w : Fin 3 → ℕ)
    (hsep : ∀ i, u i = 0 ∨ w i = 0) (x : Triple m) :
    FixedBlock.pairSizeWeight (sizes u x) (sizes w x) =
      TripleCountLaw.weight (fun i => u i + w i) x := by
  unfold FixedBlock.pairSizeWeight TripleCountLaw.weight
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rcases hsep i with hu | hw
  · simp [sizes, hu, CountCoupling.countWeight, one_div]
  · simp [sizes, hw, CountCoupling.countWeight, one_div, mul_comm]

theorem family_average (m : ℕ) (u w : Fin 3 → ℕ)
    (hsep : ∀ i, u i = 0 ∨ w i = 0)
    (hU : m + ∑ i, u i = Fintype.card U)
    (hW : m + ∑ i, w i = Fintype.card W)
    (f : Family U W m u w → ℝ) :
    average f = ∑ x : Triple m, TripleCountLaw.probability (fun i => u i + w i) x *
      average (fun z : Fiber U W m u w x => f ⟨x, z⟩) := by
  have h := FixedBlock.uniform_family_expectation (α := U) (β := W)
    (sizes u : Triple m → Fin 3 → ℕ) (sizes w)
    (fun x => (sum_sizes u x).trans hU) (fun x => (sum_sizes w x).trans hW)
    (fun x z => f ⟨x, z⟩)
  change average f = _ at h
  simp_rw [pairSizeWeight_eq m u w hsep] at h
  rw [h]
  simp only [TripleCountLaw.probability, TripleCountLaw.totalWeight,
    div_mul_eq_mul_div, ← Finset.sum_div, average]

def rowFunction (m : ℕ) (u w : Fin 3 → ℕ)
    (g : Fin 3 → Finset U → Finset W → ℝ) (i : Fin 3)
    (x : Triple m) (z : Fiber U W m u w x) : ℝ :=
  g i (FixedBlock.row z.1.val i) (FixedBlock.row z.2.val i)

def rowMean (m : ℕ) (u w : Fin 3 → ℕ)
    (g : Fin 3 → Finset U → Finset W → ℝ) (i : Fin 3) (t : Fin (m + 1)) : ℝ :=
  average (fun z : FixedBlockMarginal.Subsets (α := U) (t.val + u i) ×
      FixedBlockMarginal.Subsets (α := W) (t.val + w i) => g i z.1.val z.2.val)

theorem average_rowFunction (m : ℕ) (u w : Fin 3 → ℕ)
    (hU : m + ∑ i, u i = Fintype.card U)
    (hW : m + ∑ i, w i = Fintype.card W)
    (g : Fin 3 → Finset U → Finset W → ℝ) (i : Fin 3) (x : Triple m) :
    average (rowFunction m u w g i x) = rowMean m u w g i (x.val i) := by
  obtain ⟨z⟩ := fiber_nonempty m u w hU hW x
  exact FixedBlockMarginal.row_function_average_eq_subset_average i z.1 z.2 (g i)

theorem marginal_expectation (a : Fin 3 → ℕ) (m : ℕ) (i : Fin 3)
    (b : Fin (m + 1) → ℝ) :
    (∑ t, TripleCountLaw.marginal a m i t * b t) =
      ∑ x : Triple m, TripleCountLaw.probability a x * b (x.val i) := by
  classical
  unfold TripleCountLaw.marginal
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem centered_row_average_sq (m : ℕ) (u w : Fin 3 → ℕ)
    (hsep : ∀ i, u i = 0 ∨ w i = 0)
    (hU : m + ∑ i, u i = Fintype.card U)
    (hW : m + ∑ i, w i = Fintype.card W)
    (g : Fin 3 → Finset U → Finset W → ℝ)
    (hcenter : ∀ i, average (fun z : Family U W m u w =>
      rowFunction m u w g i z.1 z.2) = 0) :
    average (fun z : Family U W m u w =>
      (∑ i, rowFunction m u w g i z.1 z.2) ^ 2) ≤
      2 * ∑ i, average (fun z : Family U W m u w =>
        (rowFunction m u w g i z.1 z.2) ^ 2) := by
  let (x : Triple m) : Nonempty (Fiber U W m u w x) :=
    fiber_nonempty m u w hU hW x
  have hb (i : Fin 3) : ∑ t, TripleCountLaw.marginal (fun j => u j + w j) m i t *
      rowMean m u w g i t = 0 := by
    rw [marginal_expectation]
    have hc := hcenter i
    rw [family_average m u w hsep hU hW] at hc
    simpa only [average_rowFunction m u w hU hW g i] using hc
  have hmean := TripleCountLaw.count_row_variance_le_two
    (fun i => u i + w i) m (rowMean m u w g) hb
  simp_rw [marginal_expectation] at hmean
  simp_rw [family_average m u w hsep hU hW]
  apply FiniteVariance.mixture_centered_row_bound (Fiber U W m u w)
    (TripleCountLaw.probability (fun i => u i + w i))
    (fun x => (TripleCountLaw.probability_pos _ x).le)
    (rowFunction m u w g)
  · intro x
    exact FixedBlockVariance.variance_sum_row_functions (sizes u x) (sizes w x) g
  · simpa only [average_rowFunction m u w hU hW] using hmean

theorem row_variance_bound (m : ℕ) (u w : Fin 3 → ℕ)
    (hsep : ∀ i, u i = 0 ∨ w i = 0)
    (hU : m + ∑ i, u i = Fintype.card U)
    (hW : m + ∑ i, w i = Fintype.card W)
    (g : Fin 3 → Finset U → Finset W → ℝ) :
    FiniteVariance.variance (fun z : Family U W m u w =>
      ∑ i, rowFunction m u w g i z.1 z.2) ≤
      2 * ∑ i, FiniteVariance.variance (fun z : Family U W m u w =>
        rowFunction m u w g i z.1 z.2) := by
  obtain ⟨x⟩ := TripleCountLaw.fiber_nonempty m (Equiv.refl _) 0 (Nat.zero_le _)
  obtain ⟨z⟩ := fiber_nonempty m u w hU hW x.val
  let : Nonempty (Family U W m u w) := ⟨⟨x.val, z⟩⟩
  let c (i : Fin 3) := average (fun z : Family U W m u w =>
    rowFunction m u w g i z.1 z.2)
  let g' (i : Fin 3) (s : Finset U) (t : Finset W) := g i s t - c i
  have he (i : Fin 3) (z : Family U W m u w) :
      rowFunction m u w g' i z.1 z.2 = rowFunction m u w g i z.1 z.2 - c i := rfl
  have hc (i : Fin 3) : average (fun z : Family U W m u w =>
      rowFunction m u w g' i z.1 z.2) = 0 := by
    simp_rw [he]
    exact FiniteVariance.average_center _
  have h := centered_row_average_sq m u w hsep hU hW g' hc
  simp_rw [he, Finset.sum_sub_distrib] at h
  unfold FiniteVariance.variance
  rw [FiniteVariance.average_sum]
  exact h

end Problem315.VariableBlockVariance

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/VariableBlockVariance.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/BalancedBlockVariance.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.BalancedBlockVariance
open FixedBlockMarginal (average)
open VariableBlockVariance (Family sizes rowFunction)

variable (U W : Type*) [Fintype U] [sectionDecidableEqU : DecidableEq U] [Fintype W] [sectionDecidableEqW : DecidableEq W]

abbrev Balanced (u w : Fin 3 → ℕ) :=
  {c : (U → Fin 3) × (W → Fin 3) // ∀ i,
    (FixedBlock.row c.1 i).card + w i = (FixedBlock.row c.2 i).card + u i}

variable {U W}

theorem sum_row_card {A : Type*} [Fintype A] [DecidableEq A] (c : A → Fin 3) :
    (∑ i, (FixedBlock.row c i).card) = Fintype.card A := by
  simp only [FixedBlock.row, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

include sectionDecidableEqU sectionDecidableEqW in
theorem lower_le {u w : Fin 3 → ℕ} (hsep : ∀ i, u i = 0 ∨ w i = 0)
    (c : Balanced U W u w) (i : Fin 3) : w i ≤ (FixedBlock.row c.val.2 i).card := by
  have retainedsectionDecidableEqU := sectionDecidableEqU
  have retainedsectionDecidableEqW := sectionDecidableEqW
  have h := c.property i
  rcases hsep i with h | h <;> omega

theorem lower_sum_le {u w : Fin 3 → ℕ} (hsep : ∀ i, u i = 0 ∨ w i = 0)
    (c : Balanced U W u w) : (∑ i, w i) ≤ Fintype.card W := by
  rw [← sum_row_card c.val.2]
  exact Finset.sum_le_sum (fun i _ => lower_le hsep c i)

theorem totals {u w : Fin 3 → ℕ} (c : Balanced U W u w) :
    Fintype.card U + ∑ i, w i = Fintype.card W + ∑ i, u i := by
  have h := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => c.property i)
  simpa only [Finset.sum_add_distrib, sum_row_card] using h

def countVector {u w : Fin 3 → ℕ} (hsep : ∀ i, u i = 0 ∨ w i = 0)
    (c : Balanced U W u w) : TripleCountLaw.Triple (Fintype.card W - ∑ i, w i) := by
  let m := Fintype.card W - ∑ i, w i
  have hs : (∑ i, ((FixedBlock.row c.val.2 i).card - w i)) = m := by
    rw [Finset.sum_tsub_distrib]
    · simp only [sum_row_card, m]
    · intro i hi
      exact lower_le hsep c i
  refine ⟨fun i => ⟨(FixedBlock.row c.val.2 i).card - w i, ?_⟩, hs⟩
  have hi : (FixedBlock.row c.val.2 i).card - w i ≤
      ∑ j, ((FixedBlock.row c.val.2 j).card - w j) :=
    Finset.single_le_sum (f := fun j => (FixedBlock.row c.val.2 j).card - w j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [hs] at hi
  omega

def forgetCounts (u w : Fin 3 → ℕ)
    (z : Family U W (Fintype.card W - ∑ i, w i) u w) : Balanced U W u w :=
  ⟨(z.2.1.val, z.2.2.val), by
    intro i
    rw [z.2.1.property i, z.2.2.property i]
    simp only [sizes]
    omega⟩

def familyEquiv (u w : Fin 3 → ℕ) (hsep : ∀ i, u i = 0 ∨ w i = 0) :
    Balanced U W u w ≃ Family U W (Fintype.card W - ∑ i, w i) u w := by
  apply Equiv.symm
  apply Equiv.ofBijective (forgetCounts (U := U) (W := W) u w)
  constructor
  · rintro ⟨x, c, d⟩ ⟨y, e, f⟩ h
    have hc : c.val = e.val := congrArg (fun z : Balanced U W u w => z.val.1) h
    have hd : d.val = f.val := congrArg (fun z : Balanced U W u w => z.val.2) h
    have hxy : x = y := by
      apply Subtype.ext
      funext i
      apply Fin.ext
      have hi := congrArg (fun v : W → Fin 3 => (FixedBlock.row v i).card) hd
      rw [d.property i, f.property i] at hi
      simp only [sizes] at hi
      omega
    subst y
    have hce : c = e := Subtype.ext hc
    have hdf : d = f := Subtype.ext hd
    subst e
    subst f
    rfl
  · intro c
    refine ⟨⟨countVector hsep c, ⟨⟨c.val.1, ?_⟩, ⟨c.val.2, ?_⟩⟩⟩, rfl⟩
    · intro i
      have he := c.property i
      have hl := lower_le hsep c i
      change (FixedBlock.row c.val.1 i).card =
        (FixedBlock.row c.val.2 i).card - w i + u i
      omega
    · intro i
      change (FixedBlock.row c.val.2 i).card =
        (FixedBlock.row c.val.2 i).card - w i + w i
      exact (Nat.sub_add_cancel (lower_le hsep c i)).symm

theorem row_variance_bound (u w : Fin 3 → ℕ)
    (hsep : ∀ i, u i = 0 ∨ w i = 0)
    [Nonempty (Balanced U W u w)]
    (g : Fin 3 → Finset U → Finset W → ℝ) :
    FiniteVariance.variance (fun c : Balanced U W u w =>
      ∑ i, g i (FixedBlock.row c.val.1 i) (FixedBlock.row c.val.2 i)) ≤
      2 * ∑ i, FiniteVariance.variance (fun c : Balanced U W u w =>
        g i (FixedBlock.row c.val.1 i) (FixedBlock.row c.val.2 i)) := by
  obtain ⟨c⟩ := ‹Nonempty (Balanced U W u w)›
  have hw := lower_sum_le hsep c
  have ht := totals c
  let m := Fintype.card W - ∑ i, w i
  have hW : m + ∑ i, w i = Fintype.card W := Nat.sub_add_cancel hw
  have hU : m + ∑ i, u i = Fintype.card U := by omega
  let e := familyEquiv (U := U) (W := W) u w hsep
  have h := VariableBlockVariance.row_variance_bound m u w hsep hU hW g
  have he (f : Balanced U W u w → ℝ) :
      FiniteVariance.variance (fun z => f (e.symm z)) = FiniteVariance.variance f :=
    FiniteVariance.variance_equiv e.symm f
  rw [← he (fun c => ∑ i, g i (FixedBlock.row c.val.1 i) (FixedBlock.row c.val.2 i))]
  simp_rw [← he (fun c => g _ (FixedBlock.row c.val.1 _) (FixedBlock.row c.val.2 _))]
  exact h

theorem row_variance_bound_of_rowInvariant (u w : Fin 3 → ℕ)
    (hsep : ∀ i, u i = 0 ∨ w i = 0)
    [Nonempty (Balanced U W u w)]
    (f : Fin 3 → Balanced U W u w → ℝ)
    (hf : ∀ i c d,
      FixedBlock.row c.val.1 i = FixedBlock.row d.val.1 i →
      FixedBlock.row c.val.2 i = FixedBlock.row d.val.2 i → f i c = f i d) :
    FiniteVariance.variance (fun c => ∑ i, f i c) ≤
      2 * ∑ i, FiniteVariance.variance (f i) := by
  classical
  let g (i : Fin 3) (s : Finset U) (t : Finset W) : ℝ :=
    if h : ∃ c : Balanced U W u w,
        FixedBlock.row c.val.1 i = s ∧ FixedBlock.row c.val.2 i = t then
      f i (Classical.choose h) else 0
  have hg (i : Fin 3) (c : Balanced U W u w) :
      g i (FixedBlock.row c.val.1 i) (FixedBlock.row c.val.2 i) = f i c := by
    have hex : ∃ d : Balanced U W u w,
        FixedBlock.row d.val.1 i = FixedBlock.row c.val.1 i ∧
        FixedBlock.row d.val.2 i = FixedBlock.row c.val.2 i := ⟨c, rfl, rfl⟩
    dsimp only [g]
    rw [dite_eq_left hex]
    exact hf i _ c (Classical.choose_spec hex).1 (Classical.choose_spec hex).2
  have h := row_variance_bound u w hsep g
  simpa only [hg] using h

end Problem315.BalancedBlockVariance

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/BalancedBlockVariance.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/MatrixRowVariance.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace Problem315.MatrixRowVariance

variable {C : Type*} [Fintype C]

def positive (k : C → ℕ) (r : Fin 3 → ℕ) (i : Fin 3) : ℕ :=
  (r i - ForcedColumns.offset k) - Fintype.card (ForcedColumns.Two k)

def negative (k : C → ℕ) (r : Fin 3 → ℕ) (i : Fin 3) : ℕ :=
  Fintype.card (ForcedColumns.Two k) - (r i - ForcedColumns.offset k)

theorem offset_separated (k : C → ℕ) (r : Fin 3 → ℕ) (i : Fin 3) :
    positive k r i = 0 ∨ negative k r i = 0 := by
  unfold positive negative
  omega

theorem coloring_constraints_iff (k : C → ℕ) (r : Fin 3 → ℕ)
    (c : (ForcedColumns.One k → Fin 3) × (ForcedColumns.Two k → Fin 3)) :
    (∀ i, (FixedBlock.row c.1 i).card + Fintype.card (ForcedColumns.Two k) =
      (r i - ForcedColumns.offset k) + (FixedBlock.row c.2 i).card) ↔
    (∀ i, (FixedBlock.row c.1 i).card + negative k r i =
      (FixedBlock.row c.2 i).card + positive k r i) := by
  constructor <;> intro h i
  · have hi := h i
    unfold positive negative
    omega
  · have hi := h i
    unfold positive negative at hi
    omega

def coloringsBalanceEquiv (k : C → ℕ) (r : Fin 3 → ℕ) :
    ForcedColumns.Colorings k r ≃
      BalancedBlockVariance.Balanced (ForcedColumns.One k) (ForcedColumns.Two k)
        (positive k r) (negative k r) :=
  Equiv.subtypeEquivRight (coloring_constraints_iff k r)

def fullBalanceEquiv (k : C → ℕ) (r : Fin 3 → ℕ)
    (h : Nonempty (ForcedColumns.FullMargins k r)) :
    ForcedColumns.FullMargins k r ≃
      BalancedBlockVariance.Balanced (ForcedColumns.One k) (ForcedColumns.Two k)
        (positive k r) (negative k r) :=
  (ForcedColumns.coloringEquiv k r h).trans (coloringsBalanceEquiv k r)

theorem fullBalance_row_eq_iff (k : C → ℕ) (r : Fin 3 → ℕ)
    (h : Nonempty (ForcedColumns.FullMargins k r))
    (M N : ForcedColumns.FullMargins k r) (i : Fin 3) :
    M.val i = N.val i ↔
      FixedBlock.row (fullBalanceEquiv k r h M).val.1 i =
        FixedBlock.row (fullBalanceEquiv k r h N).val.1 i ∧
      FixedBlock.row (fullBalanceEquiv k r h M).val.2 i =
        FixedBlock.row (fullBalanceEquiv k r h N).val.2 i := by
  exact ForcedColumns.coloring_row_eq_iff k r h M N i

theorem row_variance_bound (k : C → ℕ) (r : Fin 3 → ℕ)
    (h : Nonempty (ForcedColumns.FullMargins k r))
    (f : Fin 3 → ForcedColumns.FullMargins k r → ℝ)
    (hf : ∀ i M N, M.val i = N.val i → f i M = f i N) :
    FiniteVariance.variance (fun M => ∑ i, f i M) ≤
      2 * ∑ i, FiniteVariance.variance (f i) := by
  let B := BalancedBlockVariance.Balanced (ForcedColumns.One k) (ForcedColumns.Two k)
    (positive k r) (negative k r)
  let e : ForcedColumns.FullMargins k r ≃ B := fullBalanceEquiv k r h
  let : Nonempty B := h.map e
  let key (i : Fin 3) (c : B) :=
    (FixedBlock.row c.val.1 i, FixedBlock.row c.val.2 i)
  have hfac (i : Fin 3) :
      Function.FactorsThrough (fun c : B => f i (e.symm c)) (key i) := by
    intro c d hcd
    apply hf i
    apply (fullBalance_row_eq_iff k r h (e.symm c) (e.symm d) i).mpr
    change FixedBlock.row (e (e.symm c)).val.1 i =
      FixedBlock.row (e (e.symm d)).val.1 i ∧
      FixedBlock.row (e (e.symm c)).val.2 i =
      FixedBlock.row (e (e.symm d)).val.2 i
    rw [e.apply_symm_apply, e.apply_symm_apply]
    exact ⟨congrArg Prod.fst hcd, congrArg Prod.snd hcd⟩
  obtain ⟨g, hg⟩ : ∃ g : Fin 3 →
      (Finset (ForcedColumns.One k) × Finset (ForcedColumns.Two k)) → ℝ,
      ∀ i c, f i (e.symm c) = g i (key i c) := by
    have he (i : Fin 3) := (Function.factorsThrough_iff (fun c : B => f i (e.symm c))).mp
      (hfac i)
    choose g hg using he
    exact ⟨g, fun i c => congrFun (hg i) c⟩
  have hv := BalancedBlockVariance.row_variance_bound
    (positive k r) (negative k r) (offset_separated k r)
    (fun i s t => g i (s, t))
  have heq (F : ForcedColumns.FullMargins k r → ℝ) :
      FiniteVariance.variance (fun c : B => F (e.symm c)) = FiniteVariance.variance F :=
    FiniteVariance.variance_equiv e.symm F
  rw [← heq (fun M => ∑ i, f i M)]
  simp_rw [← heq (f _)]
  simp_rw [hg]
  exact hv

end Problem315.MatrixRowVariance

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/MatrixRowVariance.lean -/
