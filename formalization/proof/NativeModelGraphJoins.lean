import NativeCanonicalCounting
import NativeConcreteExecution
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace CurveballVerified
noncomputable section
open OAI.Problem315
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem native_simple_degree_eq_graphDegree {n : Nat}
    (G : SimpleGraph (Fin n)) (v : Fin n) :
    G.degree v = OAI.Problem315.graphDegree G v := by
  classical
  simp only [SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter,
    OAI.Problem315.graphDegree]

theorem native_model_edge_count {n : Nat} {d : Fin n → Nat}
    (s : NativeModel n d) : s.edges.length = (∑ v, d v) / 2 := by
  have hsum := s.project.val.sum_degrees_eq_twice_card_edges
  have hd (v : Fin n) : s.project.val.degree v = d v :=
    (native_simple_degree_eq_graphDegree s.project.val v).trans (s.realizes v)
  simp_rw [hd] at hsum
  have hraw := native_length_edgeFinset n s.edges s.valid
  have hcard : (canonicalOfNative n s.edges s.valid).toSimpleGraph.edgeFinset.card =
      s.project.val.edgeFinset.card := by
    apply congrArg Finset.card
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    rfl
  have hraw' := hraw.trans hcard
  omega

def nativeCanonicalOfGraph {n : Nat} (G : SimpleGraph (Fin n)) : CanonicalGraph n :=
  fromRelation G.Adj (fun _ _ h => G.adj_symm h) (fun _ => G.irrefl)

theorem native_model_dimension {n : Nat} {d : Fin n → Nat} (s : NativeModel n d) :
    n ≤ 1000 := ((native_graphValid_iff n s.edges).mp s.valid).1

theorem nativeCanonicalOfGraph_eq {n : Nat} (G : SimpleGraph (Fin n)) :
    (nativeCanonicalOfGraph G).toSimpleGraph = G := by
  ext u v
  unfold nativeCanonicalOfGraph
  exact fromRelation_refines G.Adj _ _ u v

/-- Proof-side canonical enumeration; does not add or replace a runtime API. -/
def nativeEdgesOfCanonical {n : Nat} (C : CanonicalGraph n) : CurveballNative.Edges :=
  C.edges.toList.map nativeEdgeVals

theorem nativeEdgesOfCanonical_valid {n : Nat} (C : CanonicalGraph n)
    (hn : n ≤ 1000) : CurveballNative.graphValid n (nativeEdgesOfCanonical C) = true := by
  apply (native_graphValid_iff _ _).mpr
  refine ⟨hn,?_,?_⟩
  · apply List.Nodup.map
    · exact nativeEdgeVals_injective n
    · exact C.edges.nodup_toList
  · intro e he
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
    have hpc : p ∈ C.edges := Finset.mem_toList.mp hp
    exact ⟨C.canonical p hpc,p.2.isLt⟩

theorem nativeEdgesOfCanonical_refines {n : Nat} (C : CanonicalGraph n) :
    EdgeRefines (nativeEdgesOfCanonical C) C := by
  intro u v
  constructor
  · intro h
    obtain ⟨p,hp,he⟩ := List.mem_map.mp h
    have hpv : p = (u,v) := nativeEdgeVals_injective n he
    subst p
    exact Finset.mem_toList.mp hp
  · intro h
    exact List.mem_map.mpr ⟨(u,v),Finset.mem_toList.mpr h,rfl⟩

/-- NativeModel.valid includes n≤1000, so a total witness must explicitly stay
inside that runtime universe. Actual accepted requests satisfy n≤26. -/
def nativeModelOfGraph {n : Nat} {d : Fin n → Nat} (hn : n ≤ 1000)
    (G : GraphState n d) : NativeModel n d := by
  let C := nativeCanonicalOfGraph G.val
  let es := nativeEdgesOfCanonical C
  have hv := nativeEdgesOfCanonical_valid C hn
  have heq : (canonicalOfNative n es hv).toSimpleGraph = G.val :=
    (native_canonical_eq_of_refines (canonicalOfNative_refines n es hv)
      (nativeEdgesOfCanonical_refines C)).trans (nativeCanonicalOfGraph_eq G.val)
  exact ⟨es,hv,by rw [heq]; exact G.property⟩

theorem nativeModelOfGraph_project {n : Nat} {d : Fin n → Nat}
    (hn : n ≤ 1000) (G : GraphState n d) :
    (nativeModelOfGraph hn G).project = G := by
  apply Subtype.ext
  exact (native_canonical_eq_of_refines
    (canonicalOfNative_refines n _ (nativeModelOfGraph hn G).valid)
    (nativeEdgesOfCanonical_refines (nativeCanonicalOfGraph G.val))).trans
      (nativeCanonicalOfGraph_eq G.val)

#print axioms native_model_edge_count
#print axioms nativeModelOfGraph_project
end
end CurveballVerified
