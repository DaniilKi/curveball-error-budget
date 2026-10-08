import NativeSubsetCapacity

namespace CurveballVerified
noncomputable section
open CurveballNativeSampling CurveballSubsetVerified

/-- DRAFT: source-only while builder owns the compiler slot. -/
theorem sorted_find_le (xs : List Nat) (hxs : xs.Pairwise (· ≤ ·))
    (p : Nat → Bool) (a w : Nat) (hf : xs.find? p = some a)
    (hw : w ∈ xs) (hp : p w = true) : a ≤ w := by
  induction xs with
  | nil => simp at hw
  | cons x xs ih =>
    have hx := List.pairwise_cons.mp hxs
    cases hs : p x with
    | false =>
      simp only [List.find?_cons,hs] at hf
      rcases List.mem_cons.mp hw with he | hm
      · subst w; simp [hs] at hp
      · exact ih hx.2 hf hm
    | true =>
      simp only [List.find?_cons,hs] at hf
      have he : x = a := Option.some.inj hf
      subst a
      rcases List.mem_cons.mp hw with he | hm
      · subst w; exact le_rfl
      · exact hx.1 w hm

theorem sampling_width_capacity (bound : Nat) (hb : bound ≤ 2^32) :
    bound ≤ 2 ^ wordWidth bound := by
  unfold wordWidth
  cases hf : (List.range 33).find? (fun w => decide (bound ≤ 2^w)) with
  | none =>
    simp only [Option.getD_none]
    exact hb.trans (by norm_num)
  | some w =>
    simp only [Option.getD_some]
    exact of_decide_eq_true
      (List.find?_some (p := fun v => decide (bound ≤ 2^v)) hf)

theorem sampling_width_le_of_capacity (bound w : Nat) (hw : w < 33)
    (hb : bound ≤ 2^w) : wordWidth bound ≤ w := by
  cases hf : (List.range 33).find? (fun v => decide (bound ≤ 2^v)) with
  | none =>
    have hn := (List.find?_eq_none.mp hf) w (List.mem_range.mpr hw)
    simp [hb] at hn
  | some v =>
    have hle := sorted_find_le (List.range 33) List.pairwise_le_range
      (fun v => decide (bound ≤ 2^v)) v w hf (List.mem_range.mpr hw) (by simp [hb])
    simpa only [wordWidth,hf,Option.getD_some] using hle

theorem sampling_width_monotone (a b : Nat) (hab : a ≤ b) (hb : b ≤ 2^32) :
    wordWidth a ≤ wordWidth b := by
  have hw := sampling_width_le_of_capacity b 32 (by decide) hb
  exact sampling_width_le_of_capacity a (wordWidth b) (by omega)
    (hab.trans (sampling_width_capacity b hb))

theorem sampling_width_one : wordWidth 1 = 0 := by decide

theorem sampling_round_up_capacity (a : Nat) : a ≤ 8*((a+7)/8) := by
  have hm := Nat.mod_lt (a+7) (by decide : 0 < 8)
  have he := Nat.mod_add_div (a+7) 8
  omega

theorem sampling_pair_reserve_capacity (r : Request) :
    wordWidth (r.n.choose 2) * r.cap ≤ pairReserve r := by
  simpa only [pairReserve,native_choose_eq] using
    sampling_round_up_capacity (wordWidth (r.n.choose 2)*r.cap)

theorem sampling_pair_bound_capacity (r : Request) (hn : r.n ≤ 26) :
    r.n.choose 2 ≤ 2 ^ wordWidth (r.n.choose 2) := by
  apply sampling_width_capacity
  exact (Nat.choose_le_choose 2 hn).trans (by
    rw [← native_choose_eq]
    decide)

theorem sampling_central_bound_capacity (n : Nat) (hn : n ≤ 26) :
    (n-2).choose ((n-2)/2) ≤ 2^32 := by
  have hN : n-2 ≤ 24 := by omega
  exact ((Nat.choose_le_choose ((n-2)/2) hN).trans
    (Nat.choose_le_middle ((n-2)/2) 24)).trans (by
      rw [← native_choose_eq]
      decide)

theorem sampling_subset_reserve_capacity (r : Request) (hn : r.n ≤ 26)
    (bound : Nat) (hb : bound ≤ (r.n-2).choose ((r.n-2)/2)) :
    wordWidth bound * r.cap ≤ subsetReserve r := by
  have hM := sampling_central_bound_capacity r.n hn
  have hw := sampling_width_monotone bound ((r.n-2).choose ((r.n-2)/2)) hb hM
  have hr := sampling_round_up_capacity
    (wordWidth ((r.n-2).choose ((r.n-2)/2))*r.cap)
  simpa only [subsetReserve,native_choose_eq] using
    (Nat.mul_le_mul_right r.cap hw).trans hr

#print axioms sampling_width_capacity
#print axioms sampling_width_monotone
#print axioms sampling_pair_reserve_capacity
#print axioms sampling_subset_reserve_capacity
end
end CurveballVerified
