import NativeEntropy

/- UNCOMPILED SOURCE CANDIDATE. No accepted Lean theorem or axiom output is
   claimed. Check only in the isolated candidate with its NativeEntropy.lean;
   never overwrite the frozen module/source/olean or existing build seals. -/
namespace CurveballNativePrefixProof
open CurveballNative

/-- The bounded structural test has exactly the original length predicate. -/
theorem hasAtLeastPrefix_eq_decide (required : Nat) (bits : List Bool) :
    hasAtLeastPrefix required bits = decide (required ≤ bits.length) := by
  induction required generalizing bits with
  | zero => simp [hasAtLeastPrefix]
  | succ required ih =>
    cases bits with
    | nil => simp [hasAtLeastPrefix]
    | cons bit rest => simp [hasAtLeastPrefix, ih, Nat.succ_le_succ_iff]

theorem hasAtLeastPrefix_false_iff (required : Nat) (bits : List Bool) :
    hasAtLeastPrefix required bits = false ↔ bits.length < required := by
  rw [hasAtLeastPrefix_eq_decide]
  simp only [decide_eq_false_iff_not, Nat.not_le]

/-- Exact frozen reserved decoder body, renamed only for comparison. It stays
    proof-only; no reference decoder or proof object enters native linkage. -/
def drawBelowReservedLengthReference (n width cap reserve : Nat) (bits : List Bool) :
    Option (Nat × List Bool) :=
  if reserve < width * cap ∨ bits.length < reserve then none else do
    let (value, _) ← drawBelow n width cap (bits.take (width * cap))
    pure (value, bits.drop reserve)

/-- Pointwise equality includes short tapes, insufficient reserves, zero cases,
    exhausted rejection, returned value and exact unused suffix; no graph or
    resource-domain premise is needed. -/
theorem drawBelowReserved_extensional (n width cap reserve : Nat) (bits : List Bool) :
    CurveballNative.drawBelowReserved n width cap reserve bits =
      drawBelowReservedLengthReference n width cap reserve bits := by
  simp only [CurveballNative.drawBelowReserved, drawBelowReservedLengthReference,
    hasAtLeastPrefix_false_iff]

theorem drawBelowReserved_function_eq :
    CurveballNative.drawBelowReserved = drawBelowReservedLengthReference := by
  funext n width cap reserve bits
  exact drawBelowReserved_extensional n width cap reserve bits

end CurveballNativePrefixProof

#print axioms CurveballNativePrefixProof.hasAtLeastPrefix_eq_decide
#print axioms CurveballNativePrefixProof.hasAtLeastPrefix_false_iff
#print axioms CurveballNativePrefixProof.drawBelowReserved_extensional
#print axioms CurveballNativePrefixProof.drawBelowReserved_function_eq
