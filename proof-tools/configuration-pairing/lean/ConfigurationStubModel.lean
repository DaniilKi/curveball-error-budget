import Mathlib.Combinatorics.SimpleGraph.Basic

/- Scope 033 concrete model and map skeleton. Full map inverses, fiber count,
   actual permutation-generation law and runtime correspondence are pending. -/
namespace ConfigurationPairing
noncomputable section

variable {n : Nat}

/-- Distinct labeled stubs, rather than repeated vertex labels. -/
def Stub (s : Fin n → Nat) := (v : Fin n) × Fin (s v)

/-- An independent definition of a perfect matching on distinct stubs. -/
structure StubMatching (s : Fin n → Nat) where
  partner : Stub s → Stub s
  involutive : Function.Involutive partner
  noFixed : ∀ x, partner x ≠ x

def ResidualNeighbor (G F : SimpleGraph (Fin n)) (v : Fin n) :=
  {w : Fin n // G.Adj v w ∧ ¬ F.Adj v w}

def StubAssignment (G F : SimpleGraph (Fin n)) (s : Fin n → Nat) :=
  (v : Fin n) → (Fin (s v) ≃ ResidualNeighbor G F v)

/-- Loops, repeated projected edges and wrong projected graph are excluded.
    This is a graph fiber, not a definition through assignment multiplicities. -/
def ProjectsTo (G F : SimpleGraph (Fin n)) (s : Fin n → Nat)
    (p : StubMatching s) : Prop :=
  (∀ x, (p.partner x).1 ≠ x.1) ∧
  (∀ v (i j : Fin (s v)), (p.partner ⟨v,i⟩).1 = (p.partner ⟨v,j⟩).1 → i = j) ∧
  (∀ v w, (G.Adj v w ∧ ¬ F.Adj v w) ↔
    ∃ i : Fin (s v), (p.partner ⟨v,i⟩).1 = w)

def GraphFiber (G F : SimpleGraph (Fin n)) (s : Fin n → Nat) :=
  {p : StubMatching s // ProjectsTo G F s p}

/-- Assign each stub to its target neighbor, then pair it with the reverse
    vertex's uniquely assigned stub. Validity/involutivity remains an obligation. -/
def forwardPartner (G F : SimpleGraph (Fin n)) (s : Fin n → Nat)
    (a : StubAssignment G F s) (x : Stub s) : Stub s :=
  let y := a x.1 x.2
  ⟨y.val, (a y.val).symm
    ⟨x.1, G.adj_symm y.property.1, fun h => y.property.2 (F.adj_symm h)⟩⟩

theorem forwardPartner_owner (G F : SimpleGraph (Fin n)) (s : Fin n → Nat)
    (a : StubAssignment G F s) (x : Stub s) :
    (forwardPartner G F s a x).1 = (a x.1 x.2).val := rfl

theorem forwardPartner_no_loop (G F : SimpleGraph (Fin n)) (s : Fin n → Nat)
    (a : StubAssignment G F s) (x : Stub s) :
    (forwardPartner G F s a x).1 ≠ x.1 := by
  intro h
  have ha : G.Adj x.1 (a x.1 x.2).val := (a x.1 x.2).property.1
  rw [← forwardPartner_owner G F s a x, h] at ha
  exact G.irrefl ha

/-- Recover the neighbor assigned to an actual distinct stub in a graph fiber. -/
def backwardEndpoint (G F : SimpleGraph (Fin n)) (s : Fin n → Nat)
    (p : GraphFiber G F s) (v : Fin n) (i : Fin (s v)) : ResidualNeighbor G F v :=
  ⟨(p.val.partner ⟨v,i⟩).1, (p.property.2.2 v _).mpr ⟨i,rfl⟩⟩

theorem backwardEndpoint_bijective (G F : SimpleGraph (Fin n)) (s : Fin n → Nat)
    (p : GraphFiber G F s) (v : Fin n) :
    Function.Bijective (backwardEndpoint G F s p v) := by
  constructor
  · intro i j h
    exact p.property.2.1 v i j (congrArg Subtype.val h)
  · intro w
    obtain ⟨i,hi⟩ := (p.property.2.2 v w.val).mp w.property
    exact ⟨i,Subtype.ext hi⟩

/-- Concrete reverse assignment, using proven injectivity and surjectivity. -/
def backwardAssignment (G F : SimpleGraph (Fin n)) (s : Fin n → Nat)
    (p : GraphFiber G F s) : StubAssignment G F s :=
  fun v => Equiv.ofBijective (backwardEndpoint G F s p v)
    (backwardEndpoint_bijective G F s p v)

theorem backwardAssignment_owner (G F : SimpleGraph (Fin n)) (s : Fin n → Nat)
    (p : GraphFiber G F s) (v : Fin n) (i : Fin (s v)) :
    (backwardAssignment G F s p v i).val = (p.val.partner ⟨v,i⟩).1 := rfl

-- No theorem asserting a full fiber equivalence/count or graph law is declared.
-- Exact remaining obligations are listed in OBLIGATIONS.md beside this source.
set_option pp.all true in
#check @backwardEndpoint_bijective
#print axioms backwardEndpoint_bijective
#print axioms forwardPartner_no_loop
#print axioms backwardAssignment
#print StubMatching
#print ProjectsTo
#print forwardPartner
#print backwardAssignment
end
end ConfigurationPairing
