import GraphStructureOnly

namespace CurveballVerified
open scoped BigOperators
open OAI.Problem315

/-- The executed representation stores each edge exactly once, smaller endpoint first. -/
structure CanonicalGraph (n : Nat) where
  edges : Finset (Fin n × Fin n)
  canonical : ∀ e ∈ edges, e.1 < e.2

def CanonicalGraph.toSimpleGraph {n : Nat} (G : CanonicalGraph n) : SimpleGraph (Fin n) where
  Adj u v := (u,v) ∈ G.edges ∨ (v,u) ∈ G.edges
  symm := ⟨by intros u v h; exact h.elim Or.inr Or.inl⟩
  loopless := by
    constructor
    intro v h
    rcases h with h | h
    · exact (lt_irrefl v) (G.canonical (v,v) h)
    · exact (lt_irrefl v) (G.canonical (v,v) h)

instance {n : Nat} (G : CanonicalGraph n) : DecidableRel G.toSimpleGraph.Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∈ G.edges ∨ _ ∈ G.edges))

def CanonicalGraph.degree {n : Nat} (G : CanonicalGraph n) (v : Fin n) : Nat :=
  (Finset.univ.filter (G.toSimpleGraph.Adj v)).card

theorem degree_refines {n : Nat} (G : CanonicalGraph n) (v : Fin n) :
    G.degree v = graphDegree G.toSimpleGraph v := by
  classical
  unfold CanonicalGraph.degree graphDegree
  congr 1
  ext w
  simp

/-- Canonical finite relation materialization; symmetry and looplessness are proofs,
    not run-time oracle computations. -/
def fromRelation {n : Nat} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (_hs : Symmetric R) (_hl : ∀ v, ¬ R v v) : CanonicalGraph n where
  edges := Finset.univ.filter (fun e => e.1 < e.2 ∧ R e.1 e.2)
  canonical := by intro e h; exact (Finset.mem_filter.mp h).2.1

theorem fromRelation_refines {n : Nat} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (hs : Symmetric R) (hl : ∀ v, ¬ R v v) (u v : Fin n) :
    (fromRelation R hs hl).toSimpleGraph.Adj u v ↔ R u v := by
  simp only [CanonicalGraph.toSimpleGraph, fromRelation, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro (⟨_, h⟩ | ⟨_, h⟩)
    · exact h
    · exact hs h
  · intro h
    rcases lt_trichotomy u v with huv | huv | huv
    · exact Or.inl ⟨huv, h⟩
    · subst v; exact (hl u h).elim
    · exact Or.inr ⟨huv, hs h⟩

def outside {n : Nat} (i j w : Fin n) : Prop := w ≠ i ∧ w ≠ j

instance {n : Nat} (i j : Fin n) : DecidablePred (outside i j) :=
  fun _ => inferInstanceAs (Decidable (_ ≠ i ∧ _ ≠ j))

def exclusive {n : Nat} (G : CanonicalGraph n) (i j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun w => outside i j w ∧
    ((G.toSimpleGraph.Adj i w ∧ ¬ G.toSimpleGraph.Adj j w) ∨
     (G.toSimpleGraph.Adj j w ∧ ¬ G.toSimpleGraph.Adj i w)))

def left {n : Nat} (G : CanonicalGraph n) (i j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun w => outside i j w ∧ G.toSimpleGraph.Adj i w ∧
    ¬ G.toSimpleGraph.Adj j w)

def common {n : Nat} (G : CanonicalGraph n) (i j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun w => outside i j w ∧ G.toSimpleGraph.Adj i w ∧
    G.toSimpleGraph.Adj j w)

theorem exclusive_refines {n : Nat} (G : CanonicalGraph n) (i j : Fin n) :
    exclusive G i j = PairFiber.singletonSet G.toSimpleGraph i j := by
  classical
  unfold exclusive PairFiber.singletonSet
  congr 1

theorem left_refines {n : Nat} (G : CanonicalGraph n) (i j : Fin n) :
    left G i j = PairFiber.leftSet G.toSimpleGraph i j := by
  classical
  unfold left PairFiber.leftSet
  congr 1

theorem common_refines {n : Nat} (G : CanonicalGraph n) (i j : Fin n) :
    common G i j = PairFiber.commonSet G.toSimpleGraph i j := by
  classical
  unfold common PairFiber.commonSet
  congr 1

def tradeRelation {n : Nat} (G : CanonicalGraph n) (i j : Fin n)
    (T : Finset (Fin n)) (u v : Fin n) : Prop :=
    (outside i j u ∧ outside i j v ∧ G.toSimpleGraph.Adj u v) ∨
    (((u = i ∧ v = j) ∨ (u = j ∧ v = i)) ∧ G.toSimpleGraph.Adj i j) ∨
    (u = i ∧ v ∈ common G i j ∪ T) ∨ (v = i ∧ u ∈ common G i j ∪ T) ∨
    (u = j ∧ v ∈ common G i j ∪ (exclusive G i j \ T)) ∨
    (v = j ∧ u ∈ common G i j ∪ (exclusive G i j \ T))

instance {n : Nat} (G : CanonicalGraph n) (i j : Fin n) (T : Finset (Fin n)) :
    DecidableRel (tradeRelation G i j T) := by
  intro u v
  unfold tradeRelation
  infer_instance

theorem tradeRelation_refines {n : Nat} (G : CanonicalGraph n) (i j : Fin n)
    (hij : i ≠ j) (T : Finset (Fin n)) (hT : T ⊆ exclusive G i j) (u v : Fin n) :
    tradeRelation G i j T u v ↔
    (PairFiber.trade G.toSimpleGraph i j hij T (by rwa [← exclusive_refines])).Adj u v := by
  classical
  simp only [tradeRelation, PairFiber.trade, PairFiber.assemble, outside,
    PairFiber.Outside, common_refines, exclusive_refines]
  have heq : (instDecidableEqFin n : DecidableEq (Fin n)) =
      (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  rw [heq]

/-- Actual computable transformation, materializing the proved trade relation. -/
def executeTrade {n : Nat} (G : CanonicalGraph n) (i j : Fin n)
    (hij : i ≠ j) (T : Finset (Fin n)) (hT : T ⊆ exclusive G i j) : CanonicalGraph n :=
  fromRelation (tradeRelation G i j T)
    (by
      intro u v h
      rw [tradeRelation_refines G i j hij T hT] at h ⊢
      exact (PairFiber.trade G.toSimpleGraph i j hij T
        (by rwa [← exclusive_refines])).adj_symm h)
    (by
      intro v h
      rw [tradeRelation_refines G i j hij T hT] at h
      exact SimpleGraph.irrefl _ h)

theorem executeTrade_refines {n : Nat} (G : CanonicalGraph n) (i j : Fin n)
    (hij : i ≠ j) (T : Finset (Fin n)) (hT : T ⊆ exclusive G i j) :
    (executeTrade G i j hij T hT).toSimpleGraph =
      PairFiber.trade G.toSimpleGraph i j hij T (by rwa [← exclusive_refines]) := by
  ext u v
  exact (fromRelation_refines _ _ _ u v).trans (tradeRelation_refines G i j hij T hT u v)

theorem executeTrade_degree {n : Nat} (G : CanonicalGraph n) (i j : Fin n)
    (hij : i ≠ j) (T : Finset (Fin n)) (hT : T ⊆ exclusive G i j)
    (hcard : T.card = (left G i j).card) (v : Fin n) :
    (executeTrade G i j hij T hT).degree v = G.degree v := by
  rw [degree_refines, executeTrade_refines, degree_refines]
  apply PairFiber.degrees_eq_of_key_leftSet_card_eq hij
    (PairFiber.key_trade _ _ _ _ _ _)
  rw [PairFiber.leftSet_trade, ← left_refines]
  exact hcard

#print axioms degree_refines
#print axioms executeTrade_refines
#print axioms executeTrade_degree
end CurveballVerified
