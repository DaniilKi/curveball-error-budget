import Init

namespace CurveballNative

abbrev Edges := List (Nat × Nat)

def graphValid (n : Nat) (es : Edges) : Bool :=
  decide (n ≤ 1000 ∧ es.Nodup ∧ ∀ e ∈ es, e.1 < e.2 ∧ e.2 < n)

def adjacent (es : Edges) (u v : Nat) : Bool :=
  decide ((u,v) ∈ es ∨ (v,u) ∈ es)

def outside (i j v : Nat) : Bool := decide (v ≠ i ∧ v ≠ j)

def exclusive (n : Nat) (es : Edges) (i j : Nat) : List Nat :=
  (List.range n).filter fun v => outside i j v &&
    (adjacent es i v != adjacent es j v)

def left (n : Nat) (es : Edges) (i j : Nat) : List Nat :=
  (List.range n).filter fun v => outside i j v && adjacent es i v && !adjacent es j v

def common (n : Nat) (es : Edges) (i j : Nat) : List Nat :=
  (List.range n).filter fun v => outside i j v && adjacent es i v && adjacent es j v

def degree (n : Nat) (es : Edges) (v : Nat) : Nat :=
  ((List.range n).filter (adjacent es v)).length

def possibleEdges (n : Nat) : Edges :=
  (List.range n).flatMap fun i =>
    ((List.range n).filter fun j => decide (i < j)).map fun j => (i,j)

def tradeAdjacent (n : Nat) (es : Edges) (i j : Nat) (chosen : List Nat)
    (u v : Nat) : Bool :=
  let both := common n es i j
  let pool := exclusive n es i j
  let a := fun w => both.contains w || chosen.contains w
  let b := fun w => both.contains w || (pool.contains w && !chosen.contains w)
  (outside i j u && outside i j v && adjacent es u v) ||
  (((u == i && v == j) || (u == j && v == i)) && adjacent es i j) ||
  (u == i && a v) || (v == i && a u) ||
  (u == j && b v) || (v == j && b u)

/-- Init-only implementation draft. It needs a successful arbitrary-input
    refinement proof before integration or any verified-sampler label. -/
def trade (n : Nat) (es : Edges) (i j : Nat) (chosen : List Nat) : Option Edges :=
  if !graphValid n es then none
  else if !(decide (i < n ∧ j < n ∧ i ≠ j ∧ chosen.Nodup ∧
      ∀ v ∈ chosen, v < n ∧ v ∈ exclusive n es i j)) then none
  else if chosen.length != (left n es i j).length then none
  else
    let result := (possibleEdges n).filter fun e => tradeAdjacent n es i j chosen e.1 e.2
    if graphValid n result then some result else none

def triangles (n : Nat) (es : Edges) : Nat :=
  ((List.range n).flatMap fun i =>
    (List.range n).flatMap fun j =>
      (List.range n).filter fun k => decide (i < j) && decide (j < k) &&
        adjacent es i j && adjacent es i k && adjacent es j k).length

end CurveballNative
