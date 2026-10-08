import ProbabilityProofBundle

namespace CurveballVerified
noncomputable section
open scoped BigOperators

def bindTapeLaw {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq γ] (p : FiniteLaw (Option α)) (q : FiniteLaw β)
    (g : α → β → Option γ) : FiniteLaw (Option γ) :=
  mapLaw (productLaw p q) (fun x => x.1.bind (fun a => g a x.2))

theorem bindTapeLaw_mass {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq γ] (p : FiniteLaw (Option α)) (q : FiniteLaw β)
    (g : α → β → Option γ) (z : γ) :
    (bindTapeLaw p q g).mass (some z) =
      ∑ a, p.mass (some a) * (mapLaw q (g a)).mass (some z) := by
  simp only [bindTapeLaw,mapLaw,productLaw,Fintype.sum_prod_type,
    Fintype.sum_option,Option.bind_none,Option.bind_some]
  simp only [reduceCtorEq,ite_false,Finset.sum_const_zero,zero_add]
  have he (a : α) (b : β) :
      (if g a b = some z then p.mass (some a) * q.mass b else 0) =
        p.mass (some a) * (if g a b = some z then q.mass b else 0) := by
    by_cases h : g a b = some z <;> simp [h]
  simp_rw [he,← Finset.mul_sum]

theorem bindTapeLaw_pushforward {Ω α β γ : Type} [Fintype Ω] [Fintype α]
    [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (p : FiniteLaw Ω) (q : FiniteLaw β) (f : Ω → Option α)
    (g : α → β → Option γ) :
    mapLaw (productLaw p q) (fun x => (f x.1).bind (fun a => g a x.2)) =
      bindTapeLaw (mapLaw p f) q g := by
  unfold bindTapeLaw
  have h := mapLaw_product p q f id
  rw [mapLaw_id] at h
  rw [← h,mapLaw_comp]
  rfl

theorem bindTapeLaw_dominated {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq γ] (p : FiniteLaw (Option α)) (q : FiniteLaw β)
    (g : α → β → Option γ) (idealPair : FiniteLaw α)
    (idealRow : α → γ → ℝ)
    (hp : ∀ a, p.mass (some a) ≤ idealPair.mass a)
    (hg : ∀ a z, (mapLaw q (g a)).mass (some z) ≤ idealRow a z)
    (hrow : ∀ a z, 0 ≤ idealRow a z) (z : γ) :
    (bindTapeLaw p q g).mass (some z) ≤ ∑ a, idealPair.mass a * idealRow a z := by
  rw [bindTapeLaw_mass]
  apply Finset.sum_le_sum
  intro a ha
  exact mul_le_mul (hp a) (hg a z) ((mapLaw q (g a)).nonnegative (some z))
    (idealPair.nonnegative a)

#print axioms bindTapeLaw_mass
#print axioms bindTapeLaw_pushforward
#print axioms bindTapeLaw_dominated
end
end CurveballVerified
