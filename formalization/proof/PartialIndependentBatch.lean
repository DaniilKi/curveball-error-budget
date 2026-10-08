import PartialTapeBind

namespace CurveballVerified
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def executeIndependentBatch {Ω α : Type} (f : Ω → Option α) :
    (b : Nat) → BatchSpace Ω b → Option (BatchSpace α b)
  | 0, _ => some ()
  | b+1, bits => (f bits.1).bind fun a =>
      (executeIndependentBatch f b bits.2).map (fun tail => (a,tail))

theorem partial_pair_mass {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (p : FiniteLaw (Option β)) (a y : α) (z : β) :
    (mapPartialLaw p (fun b => (a,b))).mass (some (y,z)) =
      if a = y then p.mass (some z) else 0 := by
  rw [mapPartialLaw_success]
  by_cases h : a = y <;> simp [h,Prod.mk.injEq]

theorem independent_batch_success_succ {Ω α : Type} [Fintype Ω] [Fintype α]
    [DecidableEq α] (entropy : FiniteLaw Ω) (f : Ω → Option α)
    (b : Nat) (y : BatchSpace α (b+1)) :
    (mapLaw (batchLaw (fun _ => entropy) (b+1)) (executeIndependentBatch f (b+1))).mass
      (some y) = (mapLaw entropy f).mass (some y.1) *
        (mapLaw (batchLaw (fun _ => entropy) b) (executeIndependentBatch f b)).mass (some y.2) := by
  obtain ⟨head,tail⟩ := y
  let tailLaw := mapLaw (batchLaw (fun _ => entropy) b) (executeIndependentBatch f b)
  have htail (a : α) :
      mapLaw (batchLaw (fun _ => entropy) b)
        (fun bits => (executeIndependentBatch f b bits).map (fun tail => (a,tail))) =
      mapPartialLaw tailLaw (fun tail => (a,tail)) := by
    unfold mapPartialLaw tailLaw
    rw [mapLaw_comp]
    rfl
  change (mapLaw (productLaw entropy (batchLaw (fun _ => entropy) b))
      (fun bits => (f bits.1).bind fun a =>
        (executeIndependentBatch f b bits.2).map (fun tail => (a,tail)))).mass (some (head,tail)) = _
  have hb := bindTapeLaw_pushforward entropy (batchLaw (fun _ => entropy) b) f
    (fun a bits => (executeIndependentBatch f b bits).map (fun tail => (a,tail)))
  rw [hb,bindTapeLaw_mass]
  simp_rw [htail,partial_pair_mass]
  have he (a : α) : (mapLaw entropy f).mass (some a) *
      (if a = head then tailLaw.mass (some tail) else 0) =
      if a = head then (mapLaw entropy f).mass (some a) * tailLaw.mass (some tail) else 0 := by
    by_cases h : a = head <;> simp [h]
  simp_rw [he]
  simp [tailLaw]

/-- Pointwise product domination for completed independent repetitions. All
    partial failures are retained, and no success-conditioned product is used. -/
theorem independent_batch_dominated {Ω α : Type} [Fintype Ω] [Fintype α]
    [DecidableEq α] (entropy : FiniteLaw Ω) (f : Ω → Option α) (ideal : FiniteLaw α)
    (h : ∀ a, (mapLaw entropy f).mass (some a) ≤ ideal.mass a)
    (b : Nat) (y : BatchSpace α b) :
    (mapLaw (batchLaw (fun _ => entropy) b) (executeIndependentBatch f b)).mass (some y) ≤
      (batchLaw (fun _ => ideal) b).mass y := by
  induction b with
  | zero =>
    cases y
    letI : Unique (BatchSpace Ω 0) := ⟨⟨()⟩,by intro x; cases x; rfl⟩
    simp only [mapLaw,executeIndependentBatch,batchLaw,ite_true]
    rw [Finset.sum_const,Finset.card_univ,Fintype.card_unique]
    norm_num
  | succ b ih =>
    rw [independent_batch_success_succ]
    change _ ≤ ideal.mass y.1 * (batchLaw (fun _ => ideal) b).mass y.2
    exact mul_le_mul (h y.1) (ih y.2)
      ((mapLaw (batchLaw (fun _ => entropy) b) (executeIndependentBatch f b)).nonnegative _)
      (ideal.nonnegative _)

#print axioms independent_batch_success_succ
#print axioms independent_batch_dominated
end
end CurveballVerified
