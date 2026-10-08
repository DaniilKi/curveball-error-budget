import NativeBatchLaw
import NativeTriangles
import NativeRankCounting

namespace CurveballVerified
noncomputable section
open OAI.Problem315 CurveballNativeSampling
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The literal ordered-triple triangle count on the proof-side graph. -/
def graphTriangles {n : Nat} {d : Fin n → Nat} (G : GraphState n d) : Nat :=
  ((List.finRange n).flatMap fun i =>
    (List.finRange n).flatMap fun j =>
      (List.finRange n).filter fun k => decide (i < j) && decide (j < k) &&
        decide (G.val.Adj i j) && decide (G.val.Adj i k) &&
        decide (G.val.Adj j k)).length

theorem native_model_adjacent {n : Nat} {d : Fin n → Nat}
    (s : NativeModel n d) (u v : Fin n) :
    CurveballNative.adjacent s.edges u.val v.val = decide (s.project.val.Adj u v) := by
  have h := native_adjacent_refines (canonicalOfNative_refines n s.edges s.valid) u v
  cases ha : CurveballNative.adjacent s.edges u.val v.val <;>
    simp_all [NativeModel.project]

theorem native_model_triangles {n : Nat} {d : Fin n → Nat} (s : NativeModel n d) :
    CurveballNative.triangles n s.edges = graphTriangles s.project := by
  unfold CurveballNative.triangles graphTriangles
  simp only [range_eq_finRange_values,List.flatMap_map,List.filter_map,
    ← List.map_flatMap,List.length_map,Function.comp_def,Fin.lt_def,
    native_model_adjacent s]

theorem observe_native_triangles {n : Nat} {d : Fin n → Nat}
    (es : CurveballNative.Edges) (G : GraphState n d)
    (h : (observeNativeModel n d es).map NativeModel.project = some G) :
    CurveballNative.triangles n es = graphTriangles G := by
  unfold observeNativeModel at h
  split_ifs at h with hv hd
  · simp only [Option.map_some,Option.some.injEq] at h
    subst G
    exact native_model_triangles ⟨es,hv,hd⟩
  · simp at h
  · simp at h

def batchToList {α : Type} : (b : Nat) → BatchSpace α b → List α
  | 0, _ => []
  | b+1, ys => ys.1 :: batchToList b ys.2

theorem raw_graph_batch_statistics {n : Nat} {d : Fin n → Nat}
    (b : Nat) (outs : List CurveballNative.Edges) (ys : BatchSpace (GraphState n d) b)
    (h : rawGraphBatch n d b outs = some ys) :
    outs.map (CurveballNative.triangles n) = (batchToList b ys).map graphTriangles := by
  induction b generalizing outs with
  | zero => cases outs <;> simp_all [rawGraphBatch,batchToList]
  | succ b ih =>
    cases outs with
    | nil => simp [rawGraphBatch] at h
    | cons es outs =>
      simp only [rawGraphBatch] at h
      cases hh : (observeNativeModel n d es).map NativeModel.project with
      | none => simp [hh] at h
      | some G =>
        simp only [hh,Option.bind_some] at h
        cases ht : rawGraphBatch n d b outs with
        | none =>
          simp only [ht] at h
          change (none : Option (GraphState n d × BatchSpace (GraphState n d) b)) = some ys at h
          cases h
        | some tail =>
          simp only [ht] at h
          change (some (G,tail) : Option (GraphState n d × BatchSpace (GraphState n d) b)) = some ys at h
          have h := Option.some.inj h
          subst ys
          simp only [List.map_cons,batchToList]
          rw [observe_native_triangles es G hh,ih outs tail ht]

theorem batch_list_filter_length {α : Type} (p : α → Bool)
    (b : Nat) (ys : BatchSpace α b) :
    ((batchToList b ys).filter p).length =
      (Finset.univ.filter (fun j : Fin b => p (batchVector b ys j))).card := by
  induction b with
  | zero => simp [batchToList]
  | succ b ih =>
    rw [Finset.card_filter,Fin.sum_univ_succ]
    have htail := ih ys.2
    rw [Finset.card_filter] at htail
    simp only [batchToList,List.filter_cons,batchVector,Fin.cases_zero,Fin.cases_succ]
    by_cases hp : p ys.1 = true <;> simp [hp,htail,Nat.add_comm] <;>
      rw [Finset.card_filter] <;> rfl

theorem raw_graph_batch_exceed {n : Nat} {d : Fin n → Nat}
    (s : NativeModel n d) (b : Nat) (outs : List CurveballNative.Edges)
    (ys : BatchSpace (GraphState n d) b) (h : rawGraphBatch n d b outs = some ys) :
    ((outs.map (CurveballNative.triangles n)).filter
      (fun t => decide (CurveballNative.triangles n s.edges ≤ t))).length =
    exceedCount b graphTriangles (s.project,ys) := by
  rw [raw_graph_batch_statistics b outs ys h,native_model_triangles]
  rw [List.filter_map,List.length_map,batch_list_filter_length]
  simp only [exceedCount,Function.comp_def,decide_eq_true_eq]

#print axioms native_model_triangles
#print axioms raw_graph_batch_statistics
#print axioms raw_graph_batch_exceed
end
end CurveballVerified
