import ProbabilityProofBundle

namespace CurveballVerified
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem mapLaw_weighted_sum {Ω α : Type} [Fintype Ω] [Fintype α]
    [DecidableEq α] (p : FiniteLaw Ω) (f : Ω → α) (w : α → ℝ) :
    (∑ a, (mapLaw p f).mass a * w a) = ∑ x, p.mass x * w (f x) := by
  simp only [mapLaw,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  have he (a : α) : (if f x = a then p.mass x else 0) * w a =
      if f x = a then p.mass x * w (f x) else 0 := by
    by_cases h : f x = a
    · subst a; simp
    · simp [h]
  simp_rw [he]
  simp

/-- A possibly infinite concrete state representation driven by finite fresh
    allocations. Only its projected graph state is finite. -/
def controlledRun {S Ω α : Type} (step : S → Ω → Option S) (project : S → α)
    (s : S) : (t : Nat) → BatchSpace Ω t → Option α
  | 0, _ => some (project s)
  | t+1, bits => (step s bits.1).bind (fun next => controlledRun step project next t bits.2)

def controlledLaw {S Ω α : Type} [Fintype Ω] [Fintype α] [DecidableEq α]
    (entropy : FiniteLaw Ω) (step : S → Ω → Option S) (project : S → α)
    (s : S) (t : Nat) : FiniteLaw (Option α) :=
  mapLaw (batchLaw (fun _ => entropy) t) (controlledRun step project s t)

theorem controlledLaw_succ_mass {S Ω α : Type} [Fintype Ω] [Fintype α]
    [DecidableEq α] (entropy : FiniteLaw Ω) (step : S → Ω → Option S)
    (project : S → α) (s : S) (t : Nat) (y : α) :
    (controlledLaw entropy step project s (t+1)).mass (some y) =
      ∑ x, entropy.mass x *
        (match step s x with
         | none => 0
         | some next => (controlledLaw entropy step project next t).mass (some y)) := by
  change (∑ bits : Ω × BatchSpace Ω t,
    if controlledRun step project s (t+1) bits = some y then
      entropy.mass bits.1 * (batchLaw (fun _ => entropy) t).mass bits.2 else 0) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  cases hs : step s x with
  | none => simp [controlledRun,hs]
  | some next =>
    simp only [controlledRun,hs,Option.bind_some]
    unfold controlledLaw
    simp only [mapLaw]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro bits hb
    by_cases h : controlledRun step project next t bits = some y <;> simp [h]

/-- Representation-level execution domination. A concrete state can retain raw
    lists/history; the proof uses fresh entropy and each derived one-step bound,
    rather than assuming that the concrete process is a projected Markov chain. -/
theorem controlledLaw_dominated {S Ω α : Type} [Fintype Ω] [Fintype α]
    [DecidableEq α] (entropy : FiniteLaw Ω) (step : S → Ω → Option S)
    (project : S → α) (ideal : α → FiniteLaw α)
    (hrow : ∀ s y,
      (mapLaw entropy (fun bits => (step s bits).map project)).mass (some y) ≤
        (ideal (project s)).mass y)
    (s : S) (t : Nat) (y : α) :
    (controlledLaw entropy step project s t).mass (some y) ≤
      (iterateKernel ideal (project s) t).mass y := by
  induction t generalizing s y with
  | zero =>
    letI : Unique (BatchSpace Ω 0) := ⟨⟨()⟩,by intro x; cases x; rfl⟩
    simp only [controlledLaw,controlledRun,iterateKernel,pointLaw,mapLaw,batchLaw,Option.some.injEq]
    rw [Finset.sum_const,Finset.card_univ,Fintype.card_unique]
    simp
  | succ t ih =>
    rw [controlledLaw_succ_mass]
    let weight : Option α → ℝ := fun out =>
      match out with
      | none => 0
      | some state => (iterateKernel ideal state t).mass y
    have hfirst : (∑ x, entropy.mass x *
        (match step s x with
         | none => 0
         | some next => (controlledLaw entropy step project next t).mass (some y))) ≤
        ∑ x, entropy.mass x * weight ((step s x).map project) := by
      apply Finset.sum_le_sum
      intro x hx
      apply mul_le_mul_of_nonneg_left _ (entropy.nonnegative x)
      cases hs : step s x with
      | none => simp [hs,weight]
      | some next => simpa [hs,weight] using ih next y
    have hweighted := mapLaw_weighted_sum entropy
      (fun bits => (step s bits).map project) weight
    rw [← hweighted,Fintype.sum_option] at hfirst
    simp only [weight,mul_zero,zero_add] at hfirst
    have hsecond : (∑ state,
        (mapLaw entropy (fun bits => (step s bits).map project)).mass (some state) *
          (iterateKernel ideal state t).mass y) ≤
        ∑ state, (ideal (project s)).mass state * (iterateKernel ideal state t).mass y := by
      apply Finset.sum_le_sum
      intro state hs
      exact mul_le_mul_of_nonneg_right (hrow s state)
        ((iterateKernel ideal state t).nonnegative y)
    have hp : (∑ state, (ideal (project s)).mass state *
        (iterateKernel ideal state t).mass y) =
        (iterateKernel ideal (project s) (t+1)).mass y := by
      simp_rw [iterateKernel_mass]
      rw [pow_succ',Matrix.mul_apply]
      rfl
    exact (hfirst.trans hsecond).trans_eq hp

#print axioms mapLaw_weighted_sum
#print axioms controlledLaw_succ_mass
#print axioms controlledLaw_dominated
end
end CurveballVerified
