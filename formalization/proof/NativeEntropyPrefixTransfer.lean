import NativeEntropy

/- Proof-only namespaced copy of the accepted optimized predicate and reserved
   decoder. Unchanged lower decoder bodies are the imported frozen definitions.
   Exact source mapping is recorded in evidence/prefix-transfer-source-map.json.
   SOURCE ONLY until a matching successful compiler receipt is present. -/
namespace CurveballNativePrefixModel
open CurveballNative

def hasAtLeastPrefix : Nat → List Bool → Bool
  | 0, _ => true
  | _ + 1, [] => false
  | required + 1, _ :: rest => hasAtLeastPrefix required rest

def drawBelowReserved (n width cap reserve : Nat) (bits : List Bool) :
    Option (Nat × List Bool) :=
  if reserve < width * cap ∨ hasAtLeastPrefix reserve bits = false then none else do
    let (value, _) ← drawBelow n width cap (bits.take (width * cap))
    pure (value, bits.drop reserve)

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

/-- Equality with the actual imported frozen decoder, including failure/value/suffix. -/
theorem drawBelowReserved_eq_frozen (n width cap reserve : Nat) (bits : List Bool) :
    drawBelowReserved n width cap reserve bits =
      CurveballNative.drawBelowReserved n width cap reserve bits := by
  simp only [drawBelowReserved, CurveballNative.drawBelowReserved,
    hasAtLeastPrefix_false_iff]

theorem drawBelowReserved_function_eq_frozen :
    drawBelowReserved = CurveballNative.drawBelowReserved := by
  funext n width cap reserve bits
  exact drawBelowReserved_eq_frozen n width cap reserve bits

#print axioms drawBelowReserved_eq_frozen
#print axioms drawBelowReserved_function_eq_frozen
end CurveballNativePrefixModel
