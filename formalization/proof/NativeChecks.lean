import NativeGraph

namespace CurveballNative

theorem graphValid_iff (n : Nat) (es : Edges) :
    graphValid n es = true ↔ n ≤ 1000 ∧ es.Nodup ∧
      ∀ e ∈ es, e.1 < e.2 ∧ e.2 < n := by
  simp [graphValid]

theorem adjacent_iff (es : Edges) (u v : Nat) :
    adjacent es u v = true ↔ (u,v) ∈ es ∨ (v,u) ∈ es := by
  simp [adjacent]

theorem outside_iff (i j v : Nat) :
    outside i j v = true ↔ v ≠ i ∧ v ≠ j := by
  simp [outside]

theorem possibleEdges_mem (n u v : Nat) :
    (u,v) ∈ possibleEdges n ↔ u < n ∧ v < n ∧ u < v := by
  simp only [possibleEdges,List.mem_flatMap,List.mem_map,List.mem_filter,
    List.mem_range,decide_eq_true_eq]
  constructor
  · rintro ⟨a,ha,b,⟨hb,hab⟩,he⟩
    cases he
    exact ⟨ha,hb,hab⟩
  · rintro ⟨hu,hv,huv⟩
    exact ⟨u,hu,v,⟨hv,huv⟩,rfl⟩

/-- Output acceptance is an actual executed validation guard, not a supplied
assumption about the returned list. It remains distinct from degree refinement. -/
theorem trade_success_valid {n : Nat} {es out : Edges} {i j : Nat}
    {chosen : List Nat} (h : trade n es i j chosen = some out) :
    graphValid n out = true := by
  unfold trade at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · dsimp only at h
        split at h
        · rename_i hout
          cases h
          exact hout
        · contradiction

theorem trade_success_canonical {n : Nat} {es out : Edges} {i j : Nat}
    {chosen : List Nat} (h : trade n es i j chosen = some out) :
    n ≤ 1000 ∧ out.Nodup ∧ ∀ e ∈ out, e.1 < e.2 ∧ e.2 < n := by
  exact (graphValid_iff n out).mp (trade_success_valid h)

#print axioms graphValid_iff
#print axioms adjacent_iff
#print axioms outside_iff
#print axioms possibleEdges_mem
#print axioms trade_success_valid
#print axioms trade_success_canonical
end CurveballNative
