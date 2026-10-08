import NativeArithmetic

namespace CurveballNative

/-- Binomial unranking in the exact List.sublistsLen order. The exponential
    enumeration is used only in the proof specification, never in this code. -/
def unrankSubset : List Nat → Nat → Nat → Option (List Nat)
  | _, 0, rank => if rank = 0 then some [] else none
  | [], _ + 1, _ => none
  | x :: xs, k + 1, rank =>
    let cut := choose xs.length (k + 1)
    if rank < cut then unrankSubset xs (k + 1) rank
    else (unrankSubset xs k (rank - cut)).map (x :: ·)

def unrankPair (n rank : Nat) : Option (Nat × Nat) := do
  let chosen ← unrankSubset (List.range n) 2 rank
  match chosen with
  | [i,j] => some (i,j)
  | _ => none

end CurveballNative
