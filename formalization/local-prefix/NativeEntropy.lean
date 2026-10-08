import Init

namespace CurveballNative

def bitsValue : List Bool → Nat
  | [] => 0
  | b :: bs => 2 * bitsValue bs + if b then 1 else 0

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

/-- Every call allocates exactly width*cap bits. Unused words inside that allocation
    are discarded. This makes the next call's suffix independent of acceptance
    time under the product entropy law. Short tapes and exhausted caps fail. -/
def drawBelowFixed (n width cap : Nat) (bits : List Bool) : Option (Nat × List Bool) :=
  if bits.length < width * cap then none else do
    let (value, _) ← drawBelow n width cap (bits.take (width * cap))
    pure (value, bits.drop (width * cap))

/-- Checks only the required prefix; never traverses the unneeded suffix. -/
def hasAtLeastPrefix : Nat → List Bool → Bool
  | 0, _ => true
  | _ + 1, [] => false
  | required + 1, _ :: rest => hasAtLeastPrefix required rest

/-- A globally fixed reservation may exceed the state's decoded word budget.
    Padding is discarded too, so even state-dependent word widths do not change
    the next draw's tape boundary. -/
def drawBelowReserved (n width cap reserve : Nat) (bits : List Bool) :
    Option (Nat × List Bool) :=
  if reserve < width * cap ∨ hasAtLeastPrefix reserve bits = false then none else do
    let (value, _) ← drawBelow n width cap (bits.take (width * cap))
    pure (value, bits.drop reserve)

end CurveballNative
