import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn

namespace CurveballVerified

/-- Little-endian bit decoder used by the finite-tape executable. -/
def bitsValue : List Bool → Nat
  | [] => 0
  | b :: bs => 2 * bitsValue bs + if b then 1 else 0

theorem bitsValue_bound (bs : List Bool) : bitsValue bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [bitsValue]
  | cons b bs ih =>
    cases b <;> simp only [bitsValue, Bool.false_eq_true, ↓reduceIte, List.length_cons,
      pow_succ] <;> omega

theorem bitsValue_injective_fixed_length {a b : List Bool}
    (hlen : a.length = b.length) (hvalue : bitsValue a = bitsValue b) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons x xs ih =>
    cases b with
    | nil => simp_all
    | cons y ys =>
      have ht : xs.length = ys.length := by simpa using hlen
      cases x <;> cases y <;> simp only [bitsValue, Bool.false_eq_true, ↓reduceIte] at hvalue
      · have hv : bitsValue xs = bitsValue ys := by omega
        simp [ih ht hv]
      · omega
      · omega
      · have hv : bitsValue xs = bitsValue ys := by omega
        simp [ih ht hv]

def decodeBits {w : Nat} (bits : Fin w → Bool) : Fin (2 ^ w) :=
  ⟨bitsValue (List.ofFn bits), by simpa using bitsValue_bound (List.ofFn bits)⟩

theorem decodeBits_bijective (w : Nat) : Function.Bijective (@decodeBits w) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro a b h
    apply List.ofFn_injective
    apply bitsValue_injective_fixed_length (by simp)
    exact congrArg Fin.val h
  · simp

/-- Structural recursion guarantees termination on every finite tape. Exhaustion
    is explicit; successful runs must not be selected and relabeled as ideal draws. -/
def drawBelowAux (n width : Nat) : Nat → List Bool → Option (Nat × List Bool)
  | 0, _ => none
  | cap + 1, bits =>
    if bits.length < width then none
    else
      let x := bitsValue (bits.take width)
      if x < n then some (x, bits.drop width)
      else drawBelowAux n width cap (bits.drop width)

def drawBelow (n width cap : Nat) (bits : List Bool) : Option (Nat × List Bool) :=
  if n = 0 ∨ 2 ^ width < n then none else drawBelowAux n width cap bits

theorem drawBelowAux_range {n width cap : Nat} {bits : List Bool} {x : Nat}
    {remaining : List Bool} (h : drawBelowAux n width cap bits = some (x,remaining)) : x < n := by
  induction cap generalizing bits with
  | zero => simp [drawBelowAux] at h
  | succ cap ih =>
    by_cases hlen : bits.length < width
    · simp [drawBelowAux, hlen] at h
    · by_cases hx : bitsValue (bits.take width) < n
      · simp [drawBelowAux, hlen, hx] at h
        obtain ⟨hv,_⟩ := h
        omega
      · exact ih (by simpa only [drawBelowAux, hlen, hx, ↓reduceIte] using h)

theorem drawBelow_range {n width cap : Nat} {bits : List Bool} {x : Nat}
    {remaining : List Bool} (h : drawBelow n width cap bits = some (x,remaining)) : x < n := by
  unfold drawBelow at h
  split_ifs at h
  exact drawBelowAux_range h

#print axioms bitsValue_bound
#print axioms bitsValue_injective_fixed_length
#print axioms decodeBits_bijective
#print axioms drawBelow_range
end CurveballVerified
