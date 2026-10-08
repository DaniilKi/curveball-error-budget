import PairResamplingFinite
import Mathlib.Data.Matrix.Mul

namespace CurveballVerified
noncomputable section
open OAI.Problem315 OAI.Problem315.PairResampling
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def pairKernel {n : Nat} {d : Fin n → Nat} (a : Finset (Fin n))
    (G H : GraphState n d) : ℝ :=
  if SameFiber a G.val H.val then 1 / (fiberStates a G).card else 0

def transition (n : Nat) (d : Fin n → Nat) : Matrix (GraphState n d) (GraphState n d) ℝ :=
  fun G H => (∑ a ∈ pairs n, pairKernel a G H) / (n.choose 2 : ℝ)

end
end CurveballVerified
