import BatchOperations
import NativeEntropyProof
import NativeSubset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.Sublists
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Matrix.Mul
import Lean.Elab.Tactic.Omega

/- BEGIN authored body: CappedCore -/
section
namespace CurveballVerified
noncomputable section
open scoped BigOperators

/-- The exact finite-word execution, retaining cap exhaustion as none. -/
def cappedWords (n M : Nat) : (cap : Nat) → BatchSpace (Fin M) cap → Option (Fin n)
  | 0, _ => none
  | cap + 1, x =>
    if hx : x.1.val < n then some ⟨x.1.val,hx⟩ else cappedWords n M cap x.2

def cappedWordLaw (n M cap : Nat) [NeZero M] : FiniteLaw (Option (Fin n)) :=
  mapLaw (batchLaw (fun _ => uniformLaw (Fin M)) cap) (cappedWords n M cap)

theorem below_card {n M : Nat} (hn : n ≤ M) :
    (Finset.univ.filter (fun x : Fin M => x.val < n)).card = n := by
  classical
  calc
    _ = (Finset.univ : Finset (Fin n)).card := by
      apply Finset.card_bij (fun x hx => (⟨x.val,(Finset.mem_filter.mp hx).2⟩ : Fin n))
      · intro x hx; exact Finset.mem_univ _
      · intro x hx y hy h
        exact Fin.ext (congrArg (fun z : Fin n => z.val) h)
      · intro y hy
        refine ⟨⟨y.val,lt_of_lt_of_le y.isLt hn⟩,?_,?_⟩
        · simp [y.isLt]
        · exact Fin.ext rfl
    _ = n := by simp

theorem above_card {n M : Nat} (hn : n ≤ M) :
    (Finset.univ.filter (fun x : Fin M => ¬ x.val < n)).card = M - n := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin M))) (p := fun x => x.val < n)
  rw [below_card hn,Finset.card_univ,Fintype.card_fin] at h
  omega

theorem rejection_word_mass {n M : Nat} [NeZero M] (hn : n ≤ M) :
    (∑ x : Fin M, if ¬ x.val < n then (1 : ℝ) / M else 0) =
      ((M - n : Nat) : ℝ) / M := by
  rw [← Finset.sum_filter,Finset.sum_const,above_card hn,nsmul_eq_mul]
  ring

theorem cappedWords_none_succ (n M cap : Nat) (x : BatchSpace (Fin M) (cap + 1)) :
    cappedWords n M (cap + 1) x = none ↔
      ¬ x.1.val < n ∧ cappedWords n M cap x.2 = none := by
  by_cases h : x.1.val < n <;> simp [cappedWords,h]

theorem accepted_word_mass {n M : Nat} [NeZero M] (hn : n ≤ M) (y : Fin n) :
    (∑ x : Fin M, if x.val = y.val then (1 : ℝ) / M else 0) = 1 / M := by
  let z : Fin M := ⟨y.val,lt_of_lt_of_le y.isLt hn⟩
  change (∑ x : Fin M, if x.val = z.val then (1 : ℝ) / M else 0) = 1 / M
  simp only [← Fin.ext_iff]
  simp


#print axioms below_card
#print axioms above_card
#print axioms rejection_word_mass
#print axioms cappedWords_none_succ
#print axioms accepted_word_mass
end
end CurveballVerified

end
/- END authored body: CappedCore -/

/- BEGIN authored body: LawComposition -/
section
namespace CurveballVerified
noncomputable section
open scoped BigOperators

theorem mapLaw_event {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (p : FiniteLaw α) (f : α → β) (E : β → Prop) [DecidablePred E] :
    eventMass (mapLaw p f) E = eventMass p (fun x => E (f x)) := by
  unfold eventMass mapLaw
  have houter (y : β) :
      (if E y then ∑ x, if f x = y then p.mass x else 0 else 0) =
      ∑ x, if f x = y then (if E y then p.mass x else 0) else 0 := by
    by_cases hy : E y <;> simp [hy]
  simp_rw [houter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  have hinner (y : β) :
      (if f x = y then (if E y then p.mass x else 0) else 0) =
      (if f x = y then (if E (f x) then p.mass x else 0) else 0) := by
    by_cases he : f x = y
    · subst y; rfl
    · simp [he]
  simp_rw [hinner]
  simp

theorem mapLaw_comp {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] (p : FiniteLaw α) (f : α → β) (g : β → γ) :
    mapLaw (mapLaw p f) g = mapLaw p (g ∘ f) := by
  apply FiniteLaw.ext_mass
  funext y
  change eventMass (mapLaw p f) (fun x => g x = y) =
    eventMass p (fun x => g (f x) = y)
  exact mapLaw_event p f (fun x => g x = y)


#print axioms mapLaw_event
#print axioms mapLaw_comp
end
end CurveballVerified

end
/- END authored body: LawComposition -/

/- BEGIN authored body: CappedFirstStep -/
section
namespace CurveballVerified
noncomputable section
open scoped BigOperators

def firstWord (n M : Nat) (x : Fin M × Option (Fin n)) : Option (Fin n) :=
  if hx : x.1.val < n then some ⟨x.1.val,hx⟩ else x.2

def firstWordLaw (n M : Nat) [NeZero M] (tailLaw : FiniteLaw (Option (Fin n))) :
    FiniteLaw (Option (Fin n)) :=
  mapLaw (productLaw (uniformLaw (Fin M)) tailLaw) (firstWord n M)

theorem firstWordLaw_none {n M : Nat} [NeZero M] (hn : n ≤ M)
    (tailLaw : FiniteLaw (Option (Fin n))) :
    (firstWordLaw n M tailLaw).mass none =
      (((M - n : Nat) : ℝ) / M) * tailLaw.mass none := by
  simp only [firstWordLaw,mapLaw,productLaw,Fintype.sum_prod_type,uniformLaw,Fintype.card_fin]
  have hp (x : Fin M) (out : Option (Fin n)) :
      (if firstWord n M (x,out) = none then (1 / (M : ℝ)) * tailLaw.mass out else 0) =
      (if ¬ x.val < n then (1 : ℝ) / M else 0) *
      (if out = none then tailLaw.mass out else 0) := by
    by_cases hx : x.val < n <;> cases out <;> simp [firstWord,hx]
  simp_rw [hp,← Finset.mul_sum]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [← Finset.sum_mul,rejection_word_mass hn]

theorem firstWordLaw_some {n M : Nat} [NeZero M] (hn : n ≤ M)
    (tailLaw : FiniteLaw (Option (Fin n))) (y : Fin n) :
    (firstWordLaw n M tailLaw).mass (some y) =
      1 / (M : ℝ) + (((M - n : Nat) : ℝ) / M) * tailLaw.mass (some y) := by
  simp only [firstWordLaw,mapLaw,productLaw,Fintype.sum_prod_type,uniformLaw,Fintype.card_fin]
  have hp (x : Fin M) (out : Option (Fin n)) :
      (if firstWord n M (x,out) = some y then (1 / (M : ℝ)) * tailLaw.mass out else 0) =
      (if x.val = y.val then (1 : ℝ) / M else 0) * tailLaw.mass out +
      (if ¬ x.val < n then (1 : ℝ) / M else 0) *
      (if out = some y then tailLaw.mass out else 0) := by
    by_cases hx : x.val < n
    · by_cases he : x.val = y.val <;> simp [firstWord,hx,he,Fin.ext_iff]
    · have he : x.val ≠ y.val := by
        have hy := y.isLt
        omega
      simp [firstWord,hx,he]
  simp_rw [hp,Finset.sum_add_distrib,← Finset.mul_sum,tailLaw.normalized,mul_one]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [← Finset.sum_mul,rejection_word_mass hn,accepted_word_mass hn]

#print axioms firstWordLaw_none
#print axioms firstWordLaw_some
end
end CurveballVerified

end
/- END authored body: CappedFirstStep -/

/- BEGIN authored body: CappedRejection -/
section
namespace CurveballVerified
noncomputable section
open scoped BigOperators

theorem cappedWordLaw_step {n M : Nat} [NeZero M] (cap : Nat) :
    cappedWordLaw n M (cap + 1) = firstWordLaw n M (cappedWordLaw n M cap) := by
  change mapLaw
    (productLaw (uniformLaw (Fin M)) (batchLaw (fun _ => uniformLaw (Fin M)) cap))
    (fun x => firstWord n M (x.1,cappedWords n M cap x.2)) =
    mapLaw
      (productLaw (uniformLaw (Fin M))
        (mapLaw (batchLaw (fun _ => uniformLaw (Fin M)) cap) (cappedWords n M cap)))
      (firstWord n M)
  have h := mapLaw_product (uniformLaw (Fin M))
    (batchLaw (fun _ => uniformLaw (Fin M)) cap) id (cappedWords n M cap)
  rw [mapLaw_id] at h
  rw [← h,mapLaw_comp]
  rfl

theorem capped_none_recurrence {n M : Nat} [NeZero M] (hn : n ≤ M) (cap : Nat) :
    (cappedWordLaw n M (cap + 1)).mass none =
      (((M - n : Nat) : ℝ) / M) * (cappedWordLaw n M cap).mass none := by
  rw [cappedWordLaw_step]
  exact firstWordLaw_none hn _

theorem capped_some_recurrence {n M : Nat} [NeZero M] (hn : n ≤ M)
    (cap : Nat) (y : Fin n) :
    (cappedWordLaw n M (cap + 1)).mass (some y) =
      1 / (M : ℝ) + (((M - n : Nat) : ℝ) / M) * (cappedWordLaw n M cap).mass (some y) := by
  rw [cappedWordLaw_step]
  exact firstWordLaw_some hn _ y

/-- Exact cap-exhaustion mass. Success is not silently renormalized. -/
theorem capped_failure_mass {n M : Nat} [NeZero M] (hn : n ≤ M) (cap : Nat) :
    (cappedWordLaw n M cap).mass none = (((M - n : Nat) : ℝ) / M) ^ cap := by
  induction cap with
  | zero =>
    letI : Unique (BatchSpace (Fin M) 0) := ⟨⟨()⟩,by intro y; cases y; rfl⟩
    change (∑ _ : BatchSpace (Fin M) 0, (1 : ℝ)) = 1
    rw [Finset.sum_const,Finset.card_univ,Fintype.card_unique]
    norm_num
  | succ cap ih => rw [capped_none_recurrence hn,ih,pow_succ]; ring

theorem capped_success_mass_equal {n M : Nat} [NeZero M] (hn : n ≤ M)
    (cap : Nat) (x y : Fin n) :
    (cappedWordLaw n M cap).mass (some x) = (cappedWordLaw n M cap).mass (some y) := by
  induction cap with
  | zero => simp [cappedWordLaw,mapLaw,batchLaw,cappedWords,BatchSpace]
  | succ cap ih => simp only [capped_some_recurrence hn,ih]

/-- Exact unnormalized mass at each accepted value. The missing mass is the
    explicit failure outcome, rather than an implicitly retried draw. -/
theorem capped_success_mass {n M : Nat} [NeZero M] (hn : n ≤ M)
    (cap : Nat) (x : Fin n) :
    (cappedWordLaw n M cap).mass (some x) =
      (1 - (((M - n : Nat) : ℝ) / M) ^ cap) / n := by
  have h := (cappedWordLaw n M cap).normalized
  rw [Fintype.sum_option,capped_failure_mass hn] at h
  have he (y : Fin n) := capped_success_mass_equal hn cap y x
  simp_rw [he] at h
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
  have hnN : 0 < n := by have hx := x.isLt; omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnN
  apply (eq_div_iff (ne_of_gt hnR)).mpr
  linarith


#print axioms capped_failure_mass
#print axioms capped_success_mass
end
end CurveballVerified

end
/- END authored body: CappedRejection -/

/- BEGIN authored body: FailureCoupling -/
section
namespace CurveballVerified
noncomputable section
open scoped BigOperators

/-- Counterfactual completion only. The actual program keeps its failure;
    this definition must never be used to retry the scientific computation. -/
def fillFailure {α : Type} [Fintype α] [DecidableEq α]
    (p : FiniteLaw (Option α)) (fallback : FiniteLaw α) : FiniteLaw α :=
  mapLaw (productLaw p fallback) (fun x => x.1.getD x.2)

theorem fillFailure_mass {α : Type} [Fintype α] [DecidableEq α]
    (p : FiniteLaw (Option α)) (fallback : FiniteLaw α) (y : α) :
    (fillFailure p fallback).mass y = p.mass (some y) + p.mass none * fallback.mass y := by
  classical
  simp only [fillFailure,mapLaw,productLaw,Fintype.sum_prod_type,Fintype.sum_option,
    Option.getD_none,Option.getD_some]
  have hnone : (∑ x, if x = y then p.mass none * fallback.mass x else 0) =
      p.mass none * fallback.mass y := by simp
  rw [hnone]
  have hsome (x : α) :
      (∑ z, if x = y then p.mass (some x) * fallback.mass z else 0) =
      if x = y then p.mass (some x) else 0 := by
    by_cases h : x = y <;> simp [h,← Finset.mul_sum,fallback.normalized]
  simp_rw [hsome]
  simp [add_comm]

/-- Adding independent uniform values only on failure gives an exactly uniform
    counterfactual primitive. Actual success/failure mass is unchanged. -/
theorem capped_counterfactual_uniform {n M : Nat} [NeZero M] [NeZero n]
    (hn : n ≤ M) (cap : Nat) :
    fillFailure (cappedWordLaw n M cap) (uniformLaw (Fin n)) = uniformLaw (Fin n) := by
  apply FiniteLaw.ext_mass
  funext x
  rw [fillFailure_mass,capped_success_mass hn,capped_failure_mass hn]
  simp only [uniformLaw,Fintype.card_fin]
  ring

theorem abort_event_inclusion {Ω α : Type} [Fintype Ω]
    (law : FiniteLaw Ω) (actual : Ω → Option α) (ideal : Ω → α)
    (hagree : ∀ x y, actual x = some y → ideal x = y)
    (reject : α → Prop) [DecidablePred reject] :
    eventMass law (fun x => (actual x).any (fun y => decide (reject y)) = true) ≤
      eventMass law (fun x => reject (ideal x)) := by
  unfold eventMass
  apply Finset.sum_le_sum
  intro x hx
  cases ha : actual x with
  | none =>
    by_cases hr : reject (ideal x) <;> simp [ha,hr,law.nonnegative x]
  | some y =>
    have hi := hagree x y ha
    simp [ha,hi]

/-- This bound is for the unconditional experiment. It does not assert TV for
    the law selected by successful completion and it does not enable retries. -/
theorem abort_typeI_transfer {Ω α : Type} [Fintype Ω]
    (law : FiniteLaw Ω) (actual : Ω → Option α) (ideal : Ω → α)
    (hagree : ∀ x y, actual x = some y → ideal x = y)
    (reject : α → Prop) [DecidablePred reject] (alpha : ℝ)
    (hideal : eventMass law (fun x => reject (ideal x)) ≤ alpha) :
    eventMass law (fun x => (actual x).any (fun y => decide (reject y)) = true) ≤ alpha :=
  (abort_event_inclusion law actual ideal hagree reject).trans hideal

#print axioms fillFailure_mass
#print axioms capped_counterfactual_uniform
#print axioms abort_event_inclusion
#print axioms abort_typeI_transfer
end
end CurveballVerified

end
/- END authored body: FailureCoupling -/

/- BEGIN authored body: BitTapeRefinement -/
section
namespace CurveballVerified
noncomputable section
open scoped BigOperators

def bitTape (width : Nat) : (cap : Nat) → BatchSpace (Fin width → Bool) cap → List Bool
  | 0, _ => []
  | cap + 1, x => List.ofFn x.1 ++ bitTape width cap x.2

theorem bitTape_length (width cap : Nat) (bits : BatchSpace (Fin width → Bool) cap) :
    (bitTape width cap bits).length = width * cap := by
  induction cap with
  | zero => rfl
  | succ cap ih => simp [bitTape,ih,Nat.mul_succ,Nat.add_comm]

theorem drawBelowAux_block (n width cap : Nat) (block suffix : List Bool)
    (hlen : block.length = width) :
    drawBelowAux n width (cap + 1) (block ++ suffix) =
      if bitsValue block < n then some (bitsValue block,suffix)
      else drawBelowAux n width cap suffix := by
  have hshort : ¬ (block ++ suffix).length < width := by
    simp only [List.length_append]
    omega
  have ht : (block ++ suffix).take width = block := by
    rw [← hlen]
    exact List.take_append_length
  have hd : (block ++ suffix).drop width = suffix := by
    rw [← hlen]
    exact List.drop_append_length
  simp only [drawBelowAux,hshort,if_false,ht,hd]

theorem bitTape_cappedWords (n width cap : Nat)
    (bits : BatchSpace (Fin width → Bool) cap) :
    (drawBelowAux n width cap (bitTape width cap bits)).map Prod.fst =
      (cappedWords n (2 ^ width) cap (batchMap (@decodeBits width) cap bits)).map Fin.val := by
  induction cap with
  | zero => rfl
  | succ cap ih =>
    simp only [bitTape]
    rw [drawBelowAux_block n width cap (List.ofFn bits.1)
      (bitTape width cap bits.2) (by simp)]
    by_cases h : bitsValue (List.ofFn bits.1) < n
    · simp [batchMap,cappedWords,decodeBits,h]
    · simpa [batchMap,cappedWords,decodeBits,h] using ih bits.2

/-- Refinement of the executed Init-only draw, including its exact returned suffix. -/
theorem fixed_bits_refines {n : Nat} (hn : 0 < n) (width cap : Nat)
    (hwidth : n ≤ 2 ^ width) (bits : BatchSpace (Fin width → Bool) cap)
    (suffix : List Bool) :
    CurveballNative.drawBelowFixed n width cap (bitTape width cap bits ++ suffix) =
      (cappedWords n (2 ^ width) cap (batchMap (@decodeBits width) cap bits)).map
        (fun out => (out.val,suffix)) := by
  rw [CurveballNative.drawBelowFixed_prefix _ _ _ _ _ (bitTape_length width cap bits),
    CurveballNative.drawBelow_eq]
  have hbad : ¬ (n = 0 ∨ 2 ^ width < n) := by omega
  simp only [drawBelow,hbad,if_false]
  have h := congrArg (Option.map (fun value => (value,suffix)))
    (bitTape_cappedWords n width cap bits)
  simpa only [Option.map_map,Function.comp_def] using h

def fixedBitsOutput (n width cap : Nat) (bits : List Bool) : Option (Fin n) :=
  (CurveballNative.drawBelowFixed n width cap bits).bind fun out =>
    if h : out.1 < n then some ⟨out.1,h⟩ else none

theorem fixedBitsOutput_refines {n : Nat} (hn : 0 < n) (width cap : Nat)
    (hwidth : n ≤ 2 ^ width) (bits : BatchSpace (Fin width → Bool) cap) :
    fixedBitsOutput n width cap (bitTape width cap bits) =
      cappedWords n (2 ^ width) cap (batchMap (@decodeBits width) cap bits) := by
  have h := fixed_bits_refines hn width cap hwidth bits []
  simp only [List.append_nil] at h
  cases hw : cappedWords n (2 ^ width) cap (batchMap (@decodeBits width) cap bits) with
  | none =>
    simp only [hw,Option.map_none] at h
    simp [fixedBitsOutput,h]
  | some value =>
    simp only [hw,Option.map_some] at h
    simp [fixedBitsOutput,h,value.isLt]

/-- The actual finite bit-tape program has the previously derived capped word
    law under independent fair-bit blocks; failure stays in the output space. -/
theorem actual_capped_bit_law {n : Nat} (hn : 0 < n) (width cap : Nat)
    (hwidth : n ≤ 2 ^ width) :
    mapLaw (batchLaw (fun _ => uniformLaw (Fin width → Bool)) cap)
      (fun bits => fixedBitsOutput n width cap (bitTape width cap bits)) =
      cappedWordLaw n (2 ^ width) cap := by
  have hfun : (fun bits => fixedBitsOutput n width cap (bitTape width cap bits)) =
      cappedWords n (2 ^ width) cap ∘ batchMap (@decodeBits width) cap := by
    funext bits
    exact fixedBitsOutput_refines hn width cap hwidth bits
  rw [hfun,← mapLaw_comp]
  let e := Equiv.ofBijective (@decodeBits width) (decodeBits_bijective width)
  have he := batch_map_uniform e cap
  change mapLaw (mapLaw _ (batchMap e cap)) _ = _
  rw [he]
  rfl

#print axioms bitTape_cappedWords
#print axioms fixed_bits_refines
#print axioms fixedBitsOutput_refines
#print axioms actual_capped_bit_law
end
end CurveballVerified

end
/- END authored body: BitTapeRefinement -/

/- BEGIN authored body: NativeSubsetProof -/
section
namespace CurveballSubsetVerified

/-- The already accepted arithmetic invariant rechecked with minimal imports.
    NativeArithmetic and NativeArithmeticProof remain byte-for-byte frozen. -/
theorem native_chooseLoop_eq (n remaining index : Nat) :
    CurveballNative.chooseLoop n remaining index (n.choose index) =
      n.choose (index + remaining) := by
  induction remaining generalizing index with
  | zero => simp [CurveballNative.chooseLoop]
  | succ remaining ih =>
    simp only [CurveballNative.chooseLoop]
    rw [← Nat.choose_succ_right_eq,Nat.mul_div_cancel _ (Nat.succ_pos index),ih]
    congr 1
    omega

theorem native_choose_eq (n k : Nat) : CurveballNative.choose n k = n.choose k := by
  simpa only [CurveballNative.choose,Nat.choose_zero_right,Nat.zero_add]
    using native_chooseLoop_eq n k 0

theorem unrankSubset_eq (xs : List Nat) (k rank : Nat) :
    CurveballNative.unrankSubset xs k rank = (xs.sublistsLen k)[rank]? := by
  induction xs generalizing k rank with
  | nil =>
    cases k with
    | zero => cases rank <;> simp [CurveballNative.unrankSubset]
    | succ k => simp [CurveballNative.unrankSubset]
  | cons x xs ih =>
    cases k with
    | zero => cases rank <;> simp [CurveballNative.unrankSubset]
    | succ k =>
      simp only [CurveballNative.unrankSubset,native_choose_eq,List.sublistsLen_succ_cons]
      by_cases h : rank < xs.length.choose (k + 1)
      · rw [if_pos h,List.getElem?_append_left (by simpa [List.length_sublistsLen] using h)]
        exact ih (k + 1) rank
      · rw [if_neg h,List.getElem?_append_right (by simpa [List.length_sublistsLen] using Nat.le_of_not_gt h)]
        simp only [List.getElem?_map,List.length_sublistsLen,ih]

def Choice (xs : List Nat) (k : Nat) := {ys : List Nat // ys ∈ (xs.sublistsLen k).toFinset}

def subsetAt (xs : List Nat) (k : Nat) (rank : Fin (xs.length.choose k)) : Choice xs k :=
  ⟨(xs.sublistsLen k)[rank.val]'(by simpa [List.length_sublistsLen] using rank.isLt), by
    apply List.mem_toFinset.mpr
    exact List.getElem_mem _⟩

theorem subsetAt_bijective {xs : List Nat} (hx : xs.Nodup) (k : Nat) :
    Function.Bijective (subsetAt xs k) := by
  constructor
  · intro i j h
    have he := congrArg Subtype.val h
    have hn := List.nodup_sublistsLen k hx
    apply Fin.ext
    exact (hn.getElem_inj_iff).mp he
  · intro y
    have hy := List.mem_toFinset.mp y.property
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hy
    refine ⟨⟨i,by simpa [List.length_sublistsLen] using hi⟩,?_⟩
    apply Subtype.ext
    exact he

theorem unrankSubset_at (xs : List Nat) (k : Nat) (rank : Fin (xs.length.choose k)) :
    CurveballNative.unrankSubset xs k rank.val = some (subsetAt xs k rank).val := by
  rw [unrankSubset_eq]
  exact List.getElem?_eq_getElem (by simpa [List.length_sublistsLen] using rank.isLt)

theorem unrankSubset_valid {xs ys : List Nat} {k rank : Nat}
    (h : CurveballNative.unrankSubset xs k rank = some ys) :
    List.Sublist ys xs ∧ ys.length = k := by
  rw [unrankSubset_eq] at h
  exact List.mem_sublistsLen.mp (List.mem_of_getElem? h)

#print axioms native_choose_eq
#print axioms unrankSubset_eq
#print axioms subsetAt_bijective
#print axioms unrankSubset_at
#print axioms unrankSubset_valid
end CurveballSubsetVerified

end
/- END authored body: NativeSubsetProof -/

/- BEGIN authored body: SubsetAssignment -/
section
namespace CurveballSubsetVerified
noncomputable section

def Assignment (xs : List Nat) (k : Nat) :=
  {T : Finset Nat // T ∈ xs.toFinset.powersetCard k}

instance (xs : List Nat) (k : Nat) : Fintype (Assignment xs k) := by
  unfold Assignment
  exact inferInstance

instance (xs : List Nat) (k : Nat) : DecidableEq (Assignment xs k) := by
  unfold Assignment
  exact inferInstance

def choiceSet {xs : List Nat} (hx : xs.Nodup) (k : Nat) (y : Choice xs k) :
    Assignment xs k := by
  have hy := List.mem_sublistsLen.mp (List.mem_toFinset.mp y.property)
  refine ⟨y.val.toFinset,Finset.mem_powersetCard.mpr ⟨?_,?_⟩⟩
  · intro v hv
    exact List.mem_toFinset.mpr (hy.1.subset (List.mem_toFinset.mp hv))
  · exact (List.toFinset_card_of_nodup (hx.sublist hy.1)).trans hy.2

theorem choiceSet_bijective {xs : List Nat} (hx : xs.Nodup)
    (hs : xs.Pairwise (· ≤ ·)) (k : Nat) : Function.Bijective (choiceSet hx k) := by
  constructor
  · intro x y h
    have hset := congrArg Subtype.val h
    change x.val.toFinset = y.val.toFinset at hset
    have hxs := (List.mem_sublistsLen.mp (List.mem_toFinset.mp x.property)).1
    have hys := (List.mem_sublistsLen.mp (List.mem_toFinset.mp y.property)).1
    have hp : x.val.Perm y.val := (List.perm_ext_iff_of_nodup
      (hx.sublist hxs) (hx.sublist hys)).mpr (fun v => by
        simpa only [← List.mem_toFinset] using (Finset.ext_iff.mp hset v))
    apply Subtype.ext
    exact List.Perm.eq_of_pairwise
      (fun a b _ _ hab hba => Nat.le_antisymm hab hba)
      (hs.sublist hxs) (hs.sublist hys) hp
  · intro T
    have hT := Finset.mem_powersetCard.mp T.property
    let ys := xs.filter fun v => decide (v ∈ T.val)
    have hset : ys.toFinset = T.val := by
      ext v
      simp only [ys,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
      constructor
      · exact And.right
      · intro hv
        exact ⟨List.mem_toFinset.mp (hT.1 hv),hv⟩
    have hsub : List.Sublist ys xs := List.filter_sublist
    have hlen : ys.length = k := by
      rw [← List.toFinset_card_of_nodup (hx.sublist hsub),hset]
      exact hT.2
    refine ⟨⟨ys,List.mem_toFinset.mpr (List.mem_sublistsLen.mpr ⟨hsub,hlen⟩)⟩,?_⟩
    exact Subtype.ext hset

def subsetAssignmentEquiv {xs : List Nat} (hx : xs.Nodup)
    (hs : xs.Pairwise (· ≤ ·)) (k : Nat) :
    Fin (xs.length.choose k) ≃ Assignment xs k :=
  (Equiv.ofBijective (subsetAt xs k) (subsetAt_bijective hx k)).trans
    (Equiv.ofBijective (choiceSet hx k) (choiceSet_bijective hx hs k))

/-- Uniform rank decoding reaches every fixed-size assignment once. The executable
    unrankSubset refinement supplies the exact corresponding returned list. -/
theorem subset_assignment_uniform {xs : List Nat} (hx : xs.Nodup)
    (hs : xs.Pairwise (· ≤ ·)) (k : Nat) [NeZero (xs.length.choose k)]
    [Nonempty (Assignment xs k)] :
    CurveballVerified.mapLaw (CurveballVerified.uniformLaw (Fin (xs.length.choose k)))
      (subsetAssignmentEquiv hx hs k) = CurveballVerified.uniformLaw (Assignment xs k) :=
  CurveballVerified.map_uniform_bijection (subsetAssignmentEquiv hx hs k)

#print axioms choiceSet_bijective
#print axioms subsetAssignmentEquiv
#print axioms subset_assignment_uniform
end
end CurveballSubsetVerified

end
/- END authored body: SubsetAssignment -/

/- BEGIN authored body: FiniteKernelExecution -/
section
namespace CurveballVerified
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def pointLaw {α : Type} [Fintype α] [DecidableEq α] (x : α) : FiniteLaw α where
  mass y := if x = y then 1 else 0
  nonnegative y := by split_ifs <;> norm_num
  normalized := by simp

def bindLaw {α β : Type} [Fintype α] [Fintype β]
    (p : FiniteLaw α) (k : α → FiniteLaw β) : FiniteLaw β where
  mass y := ∑ x, p.mass x * (k x).mass y
  nonnegative y := Finset.sum_nonneg fun x _ =>
    mul_nonneg (p.nonnegative x) ((k x).nonnegative y)
  normalized := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum,FiniteLaw.normalized,mul_one]
    exact p.normalized

def iterateKernel {α : Type} [Fintype α] [DecidableEq α]
    (k : α → FiniteLaw α) (start : α) : Nat → FiniteLaw α
  | 0 => pointLaw start
  | t + 1 => bindLaw (iterateKernel k start t) k

def kernelMatrix {α : Type} [Fintype α] (k : α → FiniteLaw α) : Matrix α α ℝ :=
  fun x y => (k x).mass y

/-- Matrix powers describe repeated execution of the very same row laws.
    Identifying an executed sampler's row law with Curveball transition remains
    a separate refinement obligation; it is not assumed to equal a TV bound. -/
theorem iterateKernel_mass {α : Type} [Fintype α] [DecidableEq α]
    (k : α → FiniteLaw α) (start finish : α) (t : Nat) :
    (iterateKernel k start t).mass finish = (kernelMatrix k ^ t) start finish := by
  induction t generalizing finish with
  | zero => simp [iterateKernel,pointLaw,Matrix.one_apply]
  | succ t ih =>
    simp only [iterateKernel,bindLaw,pow_succ,Matrix.mul_apply,kernelMatrix]
    apply Finset.sum_congr rfl
    intro x hx
    rw [ih x]

def liftPartial {α : Type} [Fintype α] [DecidableEq α]
    (k : α → FiniteLaw (Option α)) : Option α → FiniteLaw (Option α)
  | none => pointLaw none
  | some x => k x

def iteratePartial {α : Type} [Fintype α] [DecidableEq α]
    (k : α → FiniteLaw (Option α)) (start : α) (t : Nat) : FiniteLaw (Option α) :=
  iterateKernel (liftPartial k) (some start) t

/-- Aborting rows are kept as none. Domination of successful step masses
    propagates to every completed execution without conditioning on success. -/
theorem iteratePartial_dominated {α : Type} [Fintype α] [DecidableEq α]
    (actual : α → FiniteLaw (Option α)) (ideal : α → FiniteLaw α)
    (hstep : ∀ x y, (actual x).mass (some y) ≤ (ideal x).mass y)
    (start finish : α) (t : Nat) :
    (iteratePartial actual start t).mass (some finish) ≤
      (iterateKernel ideal start t).mass finish := by
  induction t generalizing finish with
  | zero => simp [iteratePartial,iterateKernel,pointLaw]
  | succ t ih =>
    simp only [iteratePartial,iterateKernel,bindLaw,Fintype.sum_option]
    simp only [liftPartial,pointLaw,reduceCtorEq,ite_false,mul_zero,zero_add]
    apply Finset.sum_le_sum
    intro x hx
    apply mul_le_mul (ih x) (hstep x finish)
    · exact (actual x).nonnegative _
    · exact (iterateKernel ideal start t).nonnegative x

theorem partial_rejection_dominated {α : Type} [Fintype α] [DecidableEq α]
    (actual : α → FiniteLaw (Option α)) (ideal : α → FiniteLaw α)
    (hstep : ∀ x y, (actual x).mass (some y) ≤ (ideal x).mass y)
    (start : α) (t : Nat) (reject : α → Prop) [DecidablePred reject] :
    eventMass (iteratePartial actual start t) (fun x =>
      match x with | none => False | some y => reject y) ≤
    eventMass (iterateKernel ideal start t) reject := by
  unfold eventMass
  rw [Fintype.sum_option]
  simp only [ite_false,zero_add]
  apply Finset.sum_le_sum
  intro y hy
  by_cases h : reject y
  · simpa only [h,ite_true] using iteratePartial_dominated actual ideal hstep start y t
  · simp [h]

#print axioms iterateKernel_mass
#print axioms iteratePartial_dominated
#print axioms partial_rejection_dominated
end
end CurveballVerified

end
/- END authored body: FiniteKernelExecution -/

/- BEGIN authored body: PartialLawMapping -/
section
namespace CurveballVerified
noncomputable section
open scoped BigOperators

def mapPartialLaw {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (p : FiniteLaw (Option α)) (f : α → β) : FiniteLaw (Option β) :=
  mapLaw p (Option.map f)

theorem mapPartialLaw_success {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (p : FiniteLaw (Option α)) (f : α → β) (y : β) :
    (mapPartialLaw p f).mass (some y) = ∑ x, if f x = y then p.mass (some x) else 0 := by
  simp [mapPartialLaw,mapLaw,Fintype.sum_option]

/-- Native decoding/transformation can merge outcomes. Uniformity need not be
    claimed after the map; exact mass domination is preserved under that map. -/
theorem mapPartialLaw_dominated {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (actual : FiniteLaw (Option α)) (ideal : FiniteLaw α) (f : α → β)
    (h : ∀ x, actual.mass (some x) ≤ ideal.mass x) (y : β) :
    (mapPartialLaw actual f).mass (some y) ≤ (mapLaw ideal f).mass y := by
  rw [mapPartialLaw_success]
  change (∑ x, if f x = y then actual.mass (some x) else 0) ≤
    ∑ x, if f x = y then ideal.mass x else 0
  apply Finset.sum_le_sum
  intro x hx
  by_cases he : f x = y
  · simpa only [he,ite_true] using h x
  · simp [he]

theorem capped_success_dominated {n M : Nat} [NeZero n] [NeZero M] (hn : n ≤ M)
    (cap : Nat) (x : Fin n) :
    (cappedWordLaw n M cap).mass (some x) ≤ (uniformLaw (Fin n)).mass x := by
  rw [capped_success_mass hn]
  simp only [uniformLaw,Fintype.card_fin]
  have hr : 0 ≤ (((M - n : Nat) : ℝ) / M) ^ cap :=
    pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  linarith

#print axioms mapPartialLaw_success
#print axioms mapPartialLaw_dominated
#print axioms capped_success_dominated
end
end CurveballVerified

end
/- END authored body: PartialLawMapping -/

/- BEGIN authored body: BatchVectors -/
section
namespace CurveballVerified
noncomputable section

def batchVector {α : Type} : (b : Nat) → BatchSpace α b → Fin b → α
  | 0, _, i => Fin.elim0 i
  | b + 1, x, i => Fin.cases x.1 (batchVector b x.2) i

def vectorBatch {α : Type} : (b : Nat) → (Fin b → α) → BatchSpace α b
  | 0, _ => ()
  | b + 1, f => (f 0,vectorBatch b (fun i => f i.succ))

theorem batchVector_vectorBatch {α : Type} (b : Nat) (f : Fin b → α) :
    batchVector b (vectorBatch b f) = f := by
  induction b with
  | zero => funext i; exact Fin.elim0 i
  | succ b ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simpa only [batchVector,vectorBatch,Fin.cases_succ] using congrFun (ih _) j

theorem vectorBatch_batchVector {α : Type} (b : Nat) (x : BatchSpace α b) :
    vectorBatch b (batchVector b x) = x := by
  induction b with
  | zero => cases x; rfl
  | succ b ih =>
    obtain ⟨a,xs⟩ := x
    simp only [vectorBatch,batchVector,Fin.cases_zero,Fin.cases_succ,ih]
    rfl

def batchVectorEquiv (α : Type) (b : Nat) : BatchSpace α b ≃ (Fin b → α) where
  toFun := batchVector b
  invFun := vectorBatch b
  left_inv := vectorBatch_batchVector b
  right_inv := batchVector_vectorBatch b

theorem iid_batch_rank_bound {α : Type} [Fintype α] [Nonempty α]
    (b : Nat) (statistic : α → Nat) (i0 : Fin b) (p q : Nat) (hq : 0 < q) :
    eventMass (batchLaw (fun _ => uniformLaw α) b)
      (fun x => rankCount (fun j => statistic (batchVector b x j)) i0 * q ≤ p * b) ≤
      (p : ℝ) / q := by
  classical
  have he := map_uniform_bijection (batchVectorEquiv α b)
  have h := iid_rank_bound statistic i0 p q hq
  rw [batchLaw_uniform]
  rw [← he,mapLaw_event] at h
  rw [Fintype.card_fin] at h
  change eventMass (uniformLaw (BatchSpace α b))
    (fun x => rankCount (fun j => statistic (batchVector b x j)) i0 * q ≤ p * b) ≤
      (p : ℝ) / q at h
  exact h

#print axioms batchVectorEquiv
#print axioms iid_batch_rank_bound
end
end CurveballVerified

end
/- END authored body: BatchVectors -/

