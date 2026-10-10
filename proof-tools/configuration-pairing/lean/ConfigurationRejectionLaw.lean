import ProbabilityProofBundle

/- Scope 033: generic finite law only. Constant graph fibers are NOT proved here.
   All failed complete candidates remain None; no physical RNG claim. -/
namespace ConfigurationPairing
noncomputable section
open CurveballVerified
open scoped BigOperators

variable {Ω H : Type} [Fintype Ω] [Nonempty Ω] [Fintype H] [DecidableEq H]

def candidateLaw (f : Ω → Option H) : FiniteLaw (Option H) :=
  mapLaw (uniformLaw Ω) f

def firstCandidate (f : Ω → Option H) (x : Ω × Option H) : Option H :=
  match f x.1 with
  | none => x.2
  | some y => some y

def firstCandidateLaw (f : Ω → Option H) (tail : FiniteLaw (Option H)) :
    FiniteLaw (Option H) :=
  mapLaw (productLaw (uniformLaw Ω) tail) (firstCandidate f)

def firstSuccess (f : Ω → Option H) : (cap : Nat) → BatchSpace Ω cap → Option H
  | 0, _ => none
  | cap + 1, x => firstCandidate f (x.1, firstSuccess f cap x.2)

def cappedLaw (f : Ω → Option H) (cap : Nat) : FiniteLaw (Option H) :=
  mapLaw (batchLaw (fun _ => uniformLaw Ω) cap) (firstSuccess f cap)

def failureRate (c : Nat) : ℝ :=
  1 - (Fintype.card H : ℝ) * ((c : ℝ) / Fintype.card Ω)

theorem candidate_some (f : Ω → Option H) (c : Nat)
    (hf : ∀ y, (Finset.univ.filter (fun x => f x = some y)).card = c) (y : H) :
    (candidateLaw f).mass (some y) = (c : ℝ) / Fintype.card Ω := by
  classical
  simp only [candidateLaw, mapLaw, uniformLaw]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, hf y]
  ring

theorem candidate_none (f : Ω → Option H) (c : Nat)
    (hf : ∀ y, (Finset.univ.filter (fun x => f x = some y)).card = c) :
    (candidateLaw f).mass none = failureRate (Ω := Ω) (H := H) c := by
  classical
  have h := (candidateLaw f).normalized
  rw [Fintype.sum_option] at h
  simp_rw [candidate_some f c hf] at h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  unfold failureRate
  linarith

theorem firstCandidateLaw_none (f : Ω → Option H) (tail : FiniteLaw (Option H)) :
    (firstCandidateLaw f tail).mass none = (candidateLaw f).mass none * tail.mass none := by
  classical
  simp only [firstCandidateLaw, candidateLaw, mapLaw, productLaw,
    Fintype.sum_prod_type, uniformLaw]
  have hp (x : Ω) (out : Option H) :
      (if firstCandidate f (x,out) = none then
        (1 / (Fintype.card Ω : ℝ)) * tail.mass out else 0) =
      (if f x = none then (1 : ℝ) / Fintype.card Ω else 0) *
        (if out = none then tail.mass out else 0) := by
    cases hx : f x <;> cases out <;> simp [firstCandidate, hx]
  simp_rw [hp, ← Finset.mul_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_mul]

theorem firstCandidateLaw_some (f : Ω → Option H) (tail : FiniteLaw (Option H)) (y : H) :
    (firstCandidateLaw f tail).mass (some y) =
      (candidateLaw f).mass (some y) + (candidateLaw f).mass none * tail.mass (some y) := by
  classical
  simp only [firstCandidateLaw, candidateLaw, mapLaw, productLaw,
    Fintype.sum_prod_type, uniformLaw]
  have hp (x : Ω) (out : Option H) :
      (if firstCandidate f (x,out) = some y then
        (1 / (Fintype.card Ω : ℝ)) * tail.mass out else 0) =
      (if f x = some y then (1 : ℝ) / Fintype.card Ω else 0) * tail.mass out +
      (if f x = none then (1 : ℝ) / Fintype.card Ω else 0) *
        (if out = some y then tail.mass out else 0) := by
    cases hx : f x with
    | none => simp [firstCandidate, hx]
    | some z =>
      by_cases hz : z = y <;> simp [firstCandidate, hx, hz]
  simp_rw [hp, Finset.sum_add_distrib, ← Finset.mul_sum, tail.normalized, mul_one]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_mul]

theorem cappedLaw_step (f : Ω → Option H) (cap : Nat) :
    cappedLaw f (cap + 1) = firstCandidateLaw f (cappedLaw f cap) := by
  classical
  change mapLaw
    (productLaw (uniformLaw Ω) (batchLaw (fun _ => uniformLaw Ω) cap))
    (fun x => firstCandidate f (x.1,firstSuccess f cap x.2)) =
    mapLaw (productLaw (uniformLaw Ω)
      (mapLaw (batchLaw (fun _ => uniformLaw Ω) cap) (firstSuccess f cap))) (firstCandidate f)
  have h := mapLaw_product (uniformLaw Ω)
    (batchLaw (fun _ => uniformLaw Ω) cap) id (firstSuccess f cap)
  rw [mapLaw_id] at h
  rw [← h, mapLaw_comp]
  rfl

theorem capped_failure (f : Ω → Option H) (c : Nat)
    (hf : ∀ y, (Finset.univ.filter (fun x => f x = some y)).card = c) (cap : Nat) :
    (cappedLaw f cap).mass none = failureRate (Ω := Ω) (H := H) c ^ cap := by
  induction cap with
  | zero =>
    letI : Unique (BatchSpace Ω 0) := ⟨⟨()⟩, by intro y; cases y; rfl⟩
    change (∑ _ : BatchSpace Ω 0, (1 : ℝ)) = 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_unique]
    norm_num
  | succ cap ih =>
    rw [cappedLaw_step, firstCandidateLaw_none, candidate_none f c hf, ih, pow_succ]
    ring

variable [Nonempty H]

theorem per_candidate_success_fraction (c : Nat) :
    (c : ℝ) / Fintype.card Ω =
      (1 - failureRate (Ω := Ω) (H := H) c) / Fintype.card H := by
  have hH : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold failureRate
  apply (eq_div_iff hH).mpr
  ring

theorem capped_success (f : Ω → Option H) (c : Nat)
    (hf : ∀ y, (Finset.univ.filter (fun x => f x = some y)).card = c)
    (cap : Nat) (y : H) :
    (cappedLaw f cap).mass (some y) =
      (1 - failureRate (Ω := Ω) (H := H) c ^ cap) / Fintype.card H := by
  induction cap with
  | zero => simp [cappedLaw, firstSuccess, batchLaw, mapLaw]
  | succ cap ih =>
    rw [cappedLaw_step, firstCandidateLaw_some, candidate_some f c hf,
      candidate_none f c hf, ih, per_candidate_success_fraction (Ω := Ω) (H := H) c,
      pow_succ]
    ring

theorem failure_rate_range (f : Ω → Option H) (c : Nat) (hc : 0 < c)
    (hf : ∀ y, (Finset.univ.filter (fun x => f x = some y)).card = c) :
    0 ≤ failureRate (Ω := Ω) (H := H) c ∧ failureRate (Ω := Ω) (H := H) c < 1 := by
  have hnonnegative := (candidateLaw f).nonnegative none
  rw [candidate_none f c hf] at hnonnegative
  have hH : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  refine ⟨hnonnegative, ?_⟩
  unfold failureRate
  have hp : (0 : ℝ) < (Fintype.card H : ℝ) * ((c : ℝ) / Fintype.card Ω) := by positivity
  linarith

/-- Accepted only as a GENERIC finite equal-fiber law. The graph-specific fiber
    hypothesis and matching-generation/runtime correspondence remain unproved. -/
theorem equal_fiber_capped_law (f : Ω → Option H) (c : Nat) (hc : 0 < c)
    (hf : ∀ y, (Finset.univ.filter (fun x => f x = some y)).card = c) (cap : Nat) :
    0 ≤ failureRate (Ω := Ω) (H := H) c ∧
    failureRate (Ω := Ω) (H := H) c < 1 ∧
    (cappedLaw f cap).mass none = failureRate (Ω := Ω) (H := H) c ^ cap ∧
    ∀ y, (cappedLaw f cap).mass (some y) =
      (1 - failureRate (Ω := Ω) (H := H) c ^ cap) / Fintype.card H := by
  obtain ⟨h0,h1⟩ := failure_rate_range f c hc hf
  exact ⟨h0,h1,capped_failure f c hf cap,fun y => capped_success f c hf cap y⟩

set_option pp.all true in
#check @equal_fiber_capped_law
#print axioms equal_fiber_capped_law
#print firstSuccess
#print cappedLaw
#print failureRate
end
end ConfigurationPairing
