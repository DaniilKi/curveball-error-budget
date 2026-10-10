import Init

namespace CurveballNative

/-- Tail-recursive exact binomial recurrence using only Lean core arithmetic. -/
def chooseLoop (n : Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | remaining + 1, index, acc =>
    chooseLoop n remaining (index + 1) (acc * (n - index) / (index + 1))

def choose (n k : Nat) : Nat := chooseLoop n k 0 1

def budgetCheck (n m p q k trades : Nat) : Bool :=
  decide (0 < p ∧ 2 * p < q ∧ m ≤ choose n 2 ∧
    trades = choose n 2 * k ∧
    choose (choose n 2) m * q ^ 2 ≤ 4 * p ^ 2 * 2 ^ (2 * k))

def rankCheck (b exceed etaNum etaDen alphaNum alphaDen : Nat) : Bool :=
  decide (0 < b ∧ exceed ≤ b ∧ 0 < etaDen ∧ 0 < alphaDen ∧
    0 < alphaNum ∧ alphaNum < alphaDen ∧
    etaNum * alphaDen < alphaNum * etaDen ∧
    (exceed + 1) * alphaDen * etaDen + (b + 1) * etaNum * alphaDen
      ≤ alphaNum * (b + 1) * etaDen)

end CurveballNative
