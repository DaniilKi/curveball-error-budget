import NativeChecks

namespace CurveballNative

theorem trade_success_checks {n : Nat} {es out : Edges} {i j : Nat}
    {chosen : List Nat} (h : trade n es i j chosen = some out) :
    graphValid n es = true ∧
    (i < n ∧ j < n ∧ i ≠ j ∧ chosen.Nodup ∧
      ∀ v ∈ chosen, v < n ∧ v ∈ exclusive n es i j) ∧
    chosen.length = (left n es i j).length := by
  unfold trade at h
  split at h
  · contradiction
  · rename_i hg
    have hg' : graphValid n es = true := by
      cases hv : graphValid n es <;> simp_all
    split at h
    · contradiction
    · rename_i hv
      have hv' : i < n ∧ j < n ∧ i ≠ j ∧ chosen.Nodup ∧
          ∀ v ∈ chosen, v < n ∧ v ∈ exclusive n es i j := by
        by_cases hp : i < n ∧ j < n ∧ i ≠ j ∧ chosen.Nodup ∧
            ∀ v ∈ chosen, v < n ∧ v ∈ exclusive n es i j
        · exact hp
        · simp [hp] at hv
      split at h
      · contradiction
      · rename_i hc
        have hc' : chosen.length = (left n es i j).length := by
          by_cases hp : chosen.length = (left n es i j).length
          · exact hp
          · simp [hp] at hc
        exact ⟨hg',hv',hc'⟩

theorem common_mem (n : Nat) (es : Edges) (i j v : Nat) :
    v ∈ common n es i j ↔ v < n ∧ (v ≠ i ∧ v ≠ j) ∧
      adjacent es i v = true ∧ adjacent es j v = true := by
  simp [common,outside,Bool.and_assoc,and_assoc]

theorem left_mem (n : Nat) (es : Edges) (i j v : Nat) :
    v ∈ left n es i j ↔ v < n ∧ (v ≠ i ∧ v ≠ j) ∧
      adjacent es i v = true ∧ adjacent es j v = false := by
  simp [left,outside,Bool.and_assoc,and_assoc]

theorem exclusive_mem (n : Nat) (es : Edges) (i j v : Nat) :
    v ∈ exclusive n es i j ↔ v < n ∧ (v ≠ i ∧ v ≠ j) ∧
      ((adjacent es i v = true ∧ adjacent es j v = false) ∨
       (adjacent es j v = true ∧ adjacent es i v = false)) := by
  cases ha : adjacent es i v <;> cases hb : adjacent es j v <;>
    simp [exclusive,outside,ha,hb]

#print axioms trade_success_checks
#print axioms common_mem
#print axioms left_mem
#print axioms exclusive_mem
end CurveballNative
