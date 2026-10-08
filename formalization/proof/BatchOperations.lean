import FiniteLawMapping
import ConditionalProbability

namespace CurveballVerified
noncomputable section
open scoped BigOperators

instance {α : Type} [DecidableEq α] (b : Nat) : DecidableEq (BatchSpace α b) := by
  induction b with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ b ih => exact @instDecidableEqProd α (BatchSpace α b) _ ih

instance {α : Type} [Nonempty α] (b : Nat) : Nonempty (BatchSpace α b) := by
  induction b with
  | zero => exact ⟨()⟩
  | succ b ih =>
    letI := ih
    exact inferInstanceAs (Nonempty (α × BatchSpace α b))

def batchMap {α β : Type} (f : α → β) :
    (b : Nat) → BatchSpace α b → BatchSpace β b
  | 0, _ => ()
  | b + 1, x => (f x.1, batchMap f b x.2)

def batchEquiv {α β : Type} (e : α ≃ β) :
    (b : Nat) → BatchSpace α b ≃ BatchSpace β b
  | 0 => Equiv.refl Unit
  | b + 1 => e.prodCongr (batchEquiv e b)

theorem batchEquiv_apply {α β : Type} (e : α ≃ β) (b : Nat) (x : BatchSpace α b) :
    batchEquiv e b x = batchMap e b x := by
  induction b with
  | zero => cases x; rfl
  | succ b ih =>
    change (e x.1,batchEquiv e b x.2) = (e x.1,batchMap e b x.2)
    rw [ih]

theorem mapLaw_product {α β γ δ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq γ] [DecidableEq δ]
    (p : FiniteLaw α) (q : FiniteLaw β) (f : α → γ) (g : β → δ) :
    mapLaw (productLaw p q) (fun x => (f x.1,g x.2)) =
      productLaw (mapLaw p f) (mapLaw q g) := by
  classical
  apply FiniteLaw.ext_mass
  funext y
  obtain ⟨a,b⟩ := y
  simp only [mapLaw, productLaw, Fintype.sum_prod_type, Prod.mk.injEq]
  have hp (x : α) (y : β) :
      (if f x = a ∧ g y = b then p.mass x * q.mass y else 0) =
      (if f x = a then p.mass x else 0) * (if g y = b then q.mass y else 0) := by
    by_cases hf : f x = a <;> by_cases hg : g y = b <;> simp [hf,hg]
  simp_rw [hp, ← Finset.mul_sum]
  rw [← Finset.sum_mul]

theorem mapLaw_id {α : Type} [Fintype α] [DecidableEq α] (p : FiniteLaw α) :
    mapLaw p id = p := by
  classical
  apply FiniteLaw.ext_mass
  funext x
  simp [mapLaw]

theorem batchLaw_uniform {α : Type} [Fintype α] [Nonempty α] (b : Nat) :
    batchLaw (fun _ => uniformLaw α) b = uniformLaw (BatchSpace α b) := by
  apply FiniteLaw.ext_mass
  funext x
  induction b with
  | zero =>
    cases x
    letI : Unique (BatchSpace α 0) := ⟨⟨()⟩,by intro y; cases y; rfl⟩
    change (1 : ℝ) = 1 / (Fintype.card (BatchSpace α 0) : ℝ)
    rw [Fintype.card_unique]
    norm_num
  | succ b ih =>
    change (uniformLaw α).mass x.1 *
      (batchLaw (fun _ => uniformLaw α) b).mass x.2 = _
    rw [ih]
    simp only [uniformLaw,BatchSpace,Fintype.card_prod]
    push_cast
    ring

theorem batch_map_uniform {α β : Type} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] [DecidableEq β] (e : α ≃ β) (b : Nat) :
    mapLaw (batchLaw (fun _ => uniformLaw α) b) (batchMap e b) =
      batchLaw (fun _ => uniformLaw β) b := by
  rw [batchLaw_uniform,batchLaw_uniform]
  have h := map_uniform_bijection (batchEquiv e b)
  have he : (batchEquiv e b : BatchSpace α b → BatchSpace β b) = batchMap e b := by
    funext x; exact batchEquiv_apply e b x
  rw [he] at h
  exact h

/-- A transformed prefix remains independent of an arbitrary untouched suffix.
    The product-law entropy premise is visible in the statement. -/
theorem independent_suffix {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] (p : FiniteLaw α) (q : FiniteLaw β)
    (f : α → γ) :
    mapLaw (productLaw p q) (fun x => (f x.1,x.2)) =
      productLaw (mapLaw p f) q := by
  simpa only [mapLaw_id,id_eq] using mapLaw_product p q f id

#print axioms mapLaw_product
#print axioms batchLaw_uniform
#print axioms batch_map_uniform
#print axioms independent_suffix
end
end CurveballVerified
