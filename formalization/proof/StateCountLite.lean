import ExactBodyExtractionLite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace CurveballVerified
noncomputable section
open OAI.Problem315
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem degree_eq_graphDegree {n : Nat} (G : SimpleGraph (Fin n)) (v : Fin n) :
    G.degree v = graphDegree G v := by
  simp only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, graphDegree]

theorem edge_count {n : Nat} {d : Fin n → Nat} (G : GraphState n d) :
    G.val.edgeFinset.card = (∑ v, d v) / 2 := by
  have h := G.val.sum_degrees_eq_twice_card_edges
  have hd (v : Fin n) : G.val.degree v = d v :=
    (degree_eq_graphDegree G.val v).trans (G.property v)
  simp_rw [hd] at h
  omega

/-- Injection into m-subsets of the possible undirected edges. -/
theorem state_count_choose_bound (n : Nat) (d : Fin n → Nat) :
    stateCount n d ≤ (n.choose 2).choose ((∑ v, d v) / 2) := by
  classical
  let m := (∑ v, d v) / 2
  let possible := (⊤ : SimpleGraph (Fin n)).edgeFinset
  let encode : GraphState n d → (possible.powersetCard m) := fun G =>
    ⟨G.val.edgeFinset, Finset.mem_powersetCard.mpr
      ⟨SimpleGraph.edgeFinset_mono le_top, edge_count G⟩⟩
  have hinj : Function.Injective encode := by
    intro G H h
    apply Subtype.ext
    apply SimpleGraph.edgeFinset_inj.mp
    exact congrArg Subtype.val h
  have h := Fintype.card_le_of_injective encode hinj
  have hc : Fintype.card (possible.powersetCard m) = (n.choose 2).choose m := by
    rw [Fintype.card_coe, Finset.card_powersetCard]
    simp only [possible, SimpleGraph.card_edgeFinset_top_eq_card_choose_two,
      Fintype.card_fin]
  rw [hc] at h
  simpa only [stateCount, allGraphStates, Finset.card_univ, m] using h

#print axioms state_count_choose_bound
end
end CurveballVerified
