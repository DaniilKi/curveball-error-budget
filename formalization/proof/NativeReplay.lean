import NativeGraph

namespace CurveballNative

structure Draw where
  first : Nat
  second : Nat
  chosen : List Nat
deriving Repr

/-- Every supplied draw is attempted, even if no edge changes. On any malformed
draw the full replay fails, instead of silently skipping or shortening it. -/
def replay (n : Nat) (es : Edges) : List Draw → Option (Edges × Nat)
  | [] => some (es,0)
  | d :: ds => do
    let hs ← trade n es d.first d.second d.chosen
    let (out,count) ← replay n hs ds
    pure (out,count+1)

theorem replay_attempted_count {n : Nat} {es out : Edges} {draws : List Draw}
    {count : Nat} (h : replay n es draws = some (out,count)) :
    count = draws.length := by
  induction draws generalizing es out count with
  | nil =>
    simp only [replay] at h
    cases h
    rfl
  | cons d ds ih =>
    cases hs : trade n es d.first d.second d.chosen with
    | none => simp [replay,hs] at h
    | some next =>
      cases ht : replay n next ds with
      | none => simp [replay,hs,ht] at h
      | some result =>
        obtain ⟨last,c⟩ := result
        simp [replay,hs,ht] at h
        obtain ⟨rfl,rfl⟩ := h
        simp [ih ht]

#print axioms replay_attempted_count
end CurveballNative
