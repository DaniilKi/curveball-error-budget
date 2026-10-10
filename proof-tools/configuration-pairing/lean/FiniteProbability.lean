import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace CurveballVerified
noncomputable section
open scoped BigOperators

structure FiniteLaw (α : Type) [Fintype α] where
  mass : α → ℝ
  nonnegative : ∀ x, 0 ≤ mass x
  normalized : ∑ x, mass x = 1

def tv {α : Type} [Fintype α] (p q : FiniteLaw α) : ℝ :=
  (1 / 2 : ℝ) * ∑ x, |p.mass x - q.mass x|

def productLaw {α β : Type} [Fintype α] [Fintype β]
    (p : FiniteLaw α) (q : FiniteLaw β) : FiniteLaw (α × β) where
  mass x := p.mass x.1 * q.mass x.2
  nonnegative x := mul_nonneg (p.nonnegative _) (q.nonnegative _)
  normalized := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, q.normalized, mul_one]
    exact p.normalized

theorem tv_product {α β : Type} [Fintype α] [Fintype β]
    (p q : FiniteLaw α) (r s : FiniteLaw β) :
    tv (productLaw p r) (productLaw q s) ≤ tv p q + tv r s := by
  have hpoint (x : α) (y : β) :
      |p.mass x * r.mass y - q.mass x * s.mass y| ≤
      |p.mass x - q.mass x| * r.mass y + q.mass x * |r.mass y - s.mass y| := by
    calc
      _ = |(p.mass x - q.mass x) * r.mass y + q.mass x * (r.mass y - s.mass y)| := by congr 1; ring
      _ ≤ |(p.mass x - q.mass x) * r.mass y| + |q.mass x * (r.mass y - s.mass y)| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (r.nonnegative y), abs_of_nonneg (q.nonnegative x)]
  unfold tv
  simp only [productLaw, Fintype.sum_prod_type]
  calc
    (1 / 2 : ℝ) * (∑ x, ∑ y, |p.mass x * r.mass y - q.mass x * s.mass y|) ≤
        (1 / 2 : ℝ) * (∑ x, ∑ y,
          (|p.mass x - q.mass x| * r.mass y + q.mass x * |r.mass y - s.mass y|)) := by
      gcongr with x y
      exact hpoint x y
    _ = (1 / 2 : ℝ) * (∑ x, |p.mass x - q.mass x|) +
        (1 / 2 : ℝ) * (∑ y, |r.mass y - s.mass y|) := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, r.normalized, mul_one]
      rw [← Finset.sum_mul, q.normalized]
      ring

def BatchSpace (α : Type) : Nat → Type
  | 0 => Unit
  | n + 1 => α × BatchSpace α n

instance {α : Type} [Fintype α] (n : Nat) : Fintype (BatchSpace α n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact @instFintypeProd α (BatchSpace α n) _ ih

def batchLaw {α : Type} [Fintype α] (p : Nat → FiniteLaw α) :
    (b : Nat) → FiniteLaw (BatchSpace α b)
  | 0 => ⟨fun _ => 1, fun _ => by norm_num, by
      change (∑ _ : Unit, (1 : ℝ)) = 1
      simp⟩
  | b + 1 => productLaw (p 0) (batchLaw (fun j => p (j + 1)) b)

theorem tv_batch_constant {α : Type} [Fintype α] (p q : Nat → FiniteLaw α)
    (ε : ℝ) (h : ∀ j, tv (p j) (q j) ≤ ε) (b : Nat) :
    tv (batchLaw p b) (batchLaw q b) ≤ (b : ℝ) * ε := by
  induction b generalizing p q with
  | zero => simp [batchLaw, tv]
  | succ b ih =>
    have hp := tv_product (p 0) (q 0)
      (batchLaw (fun j => p (j + 1)) b) (batchLaw (fun j => q (j + 1)) b)
    have ht := ih (fun j => p (j + 1)) (fun j => q (j + 1)) (fun j => h (j + 1))
    change tv (productLaw _ _) (productLaw _ _) ≤ _
    have h0 := h 0
    push_cast
    linarith

def eventMass {α : Type} [Fintype α] (p : FiniteLaw α) (E : α → Prop)
    [DecidablePred E] : ℝ := ∑ x, if E x then p.mass x else 0

theorem event_transfer {α : Type} [Fintype α] (p q : FiniteLaw α)
    (E : α → Prop) [DecidablePred E] :
    eventMass p E ≤ eventMass q E + tv p q := by
  have hpoint (x : α) :
      2 * ((if E x then p.mass x else 0) - (if E x then q.mass x else 0)) ≤
        (p.mass x - q.mass x) + |p.mass x - q.mass x| := by
    by_cases h : E x <;> simp only [h, ite_true, ite_false]
    · linarith [le_abs_self (p.mass x - q.mass x)]
    · linarith [neg_abs_le (p.mass x - q.mass x)]
  have h := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset α)) => hpoint x)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, p.normalized, q.normalized] at h
  unfold eventMass tv
  linarith

/-- Statistical transfer is conditional on the separately established ideal rank law. -/
theorem adjusted_event_bound {α : Type} [Fintype α] (actual ideal : FiniteLaw α)
    (reject : α → Prop) [DecidablePred reject] (alpha eta : ℝ)
    (hideal : eventMass ideal reject ≤ alpha - eta)
    (happrox : tv actual ideal ≤ eta) : eventMass actual reject ≤ alpha := by
  have h := event_transfer actual ideal reject
  linarith

#print axioms tv_product
#print axioms tv_batch_constant
#print axioms event_transfer
#print axioms adjusted_event_bound
end
end CurveballVerified
