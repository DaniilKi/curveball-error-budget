import ReservedBitTape
import Mathlib.Data.List.OfFn

namespace CurveballVerified
noncomputable section
open scoped BigOperators

def Tape (n : Nat) := {bits : List Bool // bits.length = n}

def tapeOfVector (n : Nat) : (Fin n → Bool) ≃ Tape n where
  toFun f := ⟨List.ofFn f,by simp⟩
  invFun x i := x.val[i.val]'(by simpa [x.property] using i.isLt)
  left_inv f := by funext i; simp
  right_inv x := by
    apply Subtype.ext
    apply List.ext_getElem
    · simp [x.property]
    · intro i hi hj
      simp

instance (n : Nat) : Fintype (Tape n) := Fintype.ofEquiv (Fin n → Bool) (tapeOfVector n)
instance (n : Nat) : Nonempty (Tape n) := ⟨tapeOfVector n (fun _ => false)⟩
instance (n : Nat) : DecidableEq (Tape n) := by unfold Tape; infer_instance

def tapeCongr {n m : Nat} (h : n = m) : Tape n ≃ Tape m where
  toFun x := ⟨x.val,x.property.trans h⟩
  invFun x := ⟨x.val,x.property.trans h.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

def appendTapeEquiv (n m : Nat) : Tape n × Tape m ≃ Tape (n + m) where
  toFun x := ⟨x.1.val ++ x.2.val,by simp [x.1.property,x.2.property]⟩
  invFun x := (⟨x.val.take n,by simp [x.property]⟩,
    ⟨x.val.drop n,by simp [x.property]⟩)
  left_inv x := by
    apply Prod.ext <;> apply Subtype.ext
    · change (x.1.val ++ x.2.val).take n = x.1.val
      have h : (x.1.val ++ x.2.val).take x.1.val.length = x.1.val := List.take_append_length
      simpa only [x.1.property] using h
    · change (x.1.val ++ x.2.val).drop n = x.2.val
      have h : (x.1.val ++ x.2.val).drop x.1.val.length = x.2.val := List.drop_append_length
      simpa only [x.1.property] using h
  right_inv x := by
    apply Subtype.ext
    exact List.take_append_drop n x.val

def blockTapeEquiv (width : Nat) : (cap : Nat) →
    BatchSpace (Fin width → Bool) cap ≃ Tape (width * cap)
  | 0 =>
    { toFun := fun _ => ⟨[],by simp⟩
      invFun := fun _ => ()
      left_inv := fun x => by cases x; rfl
      right_inv := fun x => by
        apply Subtype.ext
        have h : x.val.length = 0 := by simpa using x.property
        exact (List.eq_nil_of_length_eq_zero h).symm }
  | cap + 1 =>
    ((tapeOfVector width).prodCongr (blockTapeEquiv width cap)).trans
      ((appendTapeEquiv width (width * cap)).trans
        (tapeCongr (by simp [Nat.mul_succ,Nat.add_comm])))

theorem blockTapeEquiv_val (width cap : Nat) (bits : BatchSpace (Fin width → Bool) cap) :
    (blockTapeEquiv width cap bits).val = bitTape width cap bits := by
  induction cap with
  | zero => rfl
  | succ cap ih =>
    change List.ofFn bits.1 ++ (blockTapeEquiv width cap bits.2).val =
      List.ofFn bits.1 ++ bitTape width cap bits.2
    rw [ih]

def reservedTapeEquiv (width cap reserve : Nat) (hr : width * cap ≤ reserve) :
    (BatchSpace (Fin width → Bool) cap × (Fin (reserve-width*cap) → Bool)) ≃ Tape reserve :=
  ((blockTapeEquiv width cap).prodCongr (tapeOfVector (reserve-width*cap))).trans
    ((appendTapeEquiv (width*cap) (reserve-width*cap)).trans (tapeCongr (by omega)))

theorem reservedTapeEquiv_val (width cap reserve : Nat) (hr : width * cap ≤ reserve)
    (x : BatchSpace (Fin width → Bool) cap × (Fin (reserve-width*cap) → Bool)) :
    (reservedTapeEquiv width cap reserve hr x).val =
      bitTape width cap x.1 ++ List.ofFn x.2 := by
  change (blockTapeEquiv width cap x.1).val ++ List.ofFn x.2 = _
  rw [blockTapeEquiv_val]

theorem uniformLaw_product {α β : Type} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] :
    uniformLaw (α × β) = productLaw (uniformLaw α) (uniformLaw β) := by
  apply FiniteLaw.ext_mass
  funext x
  simp only [uniformLaw,productLaw,Fintype.card_prod]
  push_cast
  ring

theorem mapLaw_ignore_right {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq γ] (p : FiniteLaw α) (q : FiniteLaw β) (f : α → γ) :
    mapLaw (productLaw p q) (fun x => f x.1) = mapLaw p f := by
  apply FiniteLaw.ext_mass
  funext y
  simp only [mapLaw,productLaw,Fintype.sum_prod_type]
  have hp (x : α) (z : β) :
      (if f x = y then p.mass x * q.mass z else 0) =
        (if f x = y then p.mass x else 0) * q.mass z := by
    by_cases h : f x = y <;> simp [h]
  simp_rw [hp,← Finset.mul_sum,q.normalized,mul_one]

/-- A complete uniformly distributed fixed allocation induces the exact actual
    reserved draw law even when its decoded word width depends on prior state.
    Width/capacity and reservation bounds are explicit arithmetic premises. -/
theorem uniform_reserved_tape_law {n : Nat} (hn : 0 < n) (width cap reserve : Nat)
    (hwidth : n ≤ 2 ^ width) (hr : width * cap ≤ reserve) :
    mapLaw (uniformLaw (Tape reserve)) (fun tape => reservedBitsOutput n width cap reserve tape.val) =
      cappedWordLaw n (2 ^ width) cap := by
  let e := reservedTapeEquiv width cap reserve hr
  have he := map_uniform_bijection e
  rw [← he,mapLaw_comp,uniformLaw_product,← batchLaw_uniform]
  have hf : (fun x => reservedBitsOutput n width cap reserve (e x).val) =
      (fun x => cappedWords n (2 ^ width) cap (batchMap (@decodeBits width) cap x.1)) := by
    funext x
    rw [reservedTapeEquiv_val,reservedBitsOutput_refines hn width cap reserve hwidth hr]
    simp
  change mapLaw (productLaw _ _) (fun x => reservedBitsOutput n width cap reserve (e x).val) = _
  rw [hf]
  rw [mapLaw_ignore_right
    (batchLaw (fun _ => uniformLaw (Fin width → Bool)) cap)
    (uniformLaw (Fin (reserve-width*cap) → Bool))
    (fun bits => cappedWords n (2 ^ width) cap (batchMap (@decodeBits width) cap bits))]
  have hfun : (fun bits => cappedWords n (2 ^ width) cap (batchMap (@decodeBits width) cap bits)) =
      (fun bits => fixedBitsOutput n width cap (bitTape width cap bits)) := by
    funext bits
    exact (fixedBitsOutput_refines hn width cap hwidth bits).symm
  rw [hfun]
  exact actual_capped_bit_law hn width cap hwidth

#print axioms tapeOfVector
#print axioms blockTapeEquiv
#print axioms uniform_reserved_tape_law
end
end CurveballVerified
