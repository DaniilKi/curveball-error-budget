import ConfigurationStubModel
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.BigOperators

/- Parent-authorized constructive graph-fiber slice. This module does not assert
   a sampler/runtime law. Fiber multiplicity is derived from both inverse maps,
   under an explicit deterministic residual-neighbor cardinality premise. -/
namespace ConfigurationPairing
noncomputable section
open scoped BigOperators

variable {n : Nat}

def ResidualDart (G F : SimpleGraph (Fin n)) :=
  (v : Fin n) × ResidualNeighbor G F v

def reverseResidual (G F : SimpleGraph (Fin n)) {v : Fin n}
    (w : ResidualNeighbor G F v) : ResidualNeighbor G F w.val :=
  ⟨v, G.adj_symm w.property.1,
    fun h => w.property.2 (F.adj_symm h)⟩

def dartFlip (G F : SimpleGraph (Fin n))
    (z : ResidualDart G F) : ResidualDart G F :=
  ⟨z.2.val, reverseResidual G F z.2⟩

theorem dartFlip_involutive (G F : SimpleGraph (Fin n)) :
    Function.Involutive (dartFlip G F) := by
  intro z
  cases z with
  | mk v w =>
    cases w with
    | mk w hw => rfl

def assignmentDartEquiv (G F : SimpleGraph (Fin n)) (s : Fin n → Nat)
    (a : StubAssignment G F s) : Stub s ≃ ResidualDart G F where
  toFun := fun x => ⟨x.1, a x.1 x.2⟩
  invFun := fun z => ⟨z.1, (a z.1).symm z.2⟩
  left_inv := by
    intro x
    cases x with
    | mk v i =>
      change (⟨v, (a v).symm (a v i)⟩ : Stub s) = ⟨v, i⟩
      rw [(a v).symm_apply_apply i]
  right_inv := by
    intro z
    cases z with
    | mk v w =>
      change (⟨v, a v ((a v).symm w)⟩ : ResidualDart G F) = ⟨v, w⟩
      rw [(a v).apply_symm_apply w]

theorem forwardPartner_eq_dartConjugate
    (G F : SimpleGraph (Fin n)) (s : Fin n → Nat)
    (a : StubAssignment G F s) (x : Stub s) :
    forwardPartner G F s a x =
      (assignmentDartEquiv G F s a).symm
        (dartFlip G F ((assignmentDartEquiv G F s a) x)) := rfl

theorem forwardPartner_involutive
    (G F : SimpleGraph (Fin n)) (s : Fin n → Nat)
    (a : StubAssignment G F s) :
    Function.Involutive (forwardPartner G F s a) := by
  let e := assignmentDartEquiv G F s a
  have hrep : ∀ x, forwardPartner G F s a x =
      e.symm (dartFlip G F (e x)) := fun _ => rfl
  intro x
  calc
    forwardPartner G F s a (forwardPartner G F s a x) =
        e.symm (dartFlip G F (e (forwardPartner G F s a x))) := hrep _
    _ = e.symm (dartFlip G F (e (e.symm (dartFlip G F (e x))))) := by
      rw [hrep x]
    _ = e.symm (dartFlip G F (dartFlip G F (e x))) := by
      rw [e.apply_symm_apply]
    _ = e.symm (e x) := by
      rw [dartFlip_involutive G F (e x)]
    _ = x := e.symm_apply_apply x

def forwardMatching (G F : SimpleGraph (Fin n)) (s : Fin n → Nat)
    (a : StubAssignment G F s) : StubMatching s where
  partner := forwardPartner G F s a
  involutive := forwardPartner_involutive G F s a
  noFixed := by
    intro x h
    exact forwardPartner_no_loop G F s a x
      (congrArg (fun z : Stub s => z.1) h)

theorem forwardMatching_projectsTo
    (G F : SimpleGraph (Fin n)) (s : Fin n → Nat)
    (a : StubAssignment G F s) :
    ProjectsTo G F s (forwardMatching G F s a) := by
  refine ⟨forwardPartner_no_loop G F s a, ?_, ?_⟩
  · intro v i j h
    apply (a v).injective
    apply Subtype.ext
    exact h
  · intro v w
    constructor
    · intro hw
      refine ⟨(a v).symm ⟨w, hw⟩, ?_⟩
      change (a v ((a v).symm ⟨w, hw⟩)).val = w
      exact congrArg (fun z : ResidualNeighbor G F v => z.val)
        ((a v).apply_symm_apply ⟨w, hw⟩)
    · intro hw
      obtain ⟨i, hi⟩ := hw
      change (a v i).val = w at hi
      simpa only [hi] using (a v i).property

def forwardFiber (G F : SimpleGraph (Fin n)) (s : Fin n → Nat)
    (a : StubAssignment G F s) : GraphFiber G F s :=
  ⟨forwardMatching G F s a, forwardMatching_projectsTo G F s a⟩

theorem backwardAssignment_forwardFiber
    (G F : SimpleGraph (Fin n)) (s : Fin n → Nat)
    (a : StubAssignment G F s) :
    backwardAssignment G F s (forwardFiber G F s a) = a := by
  funext v
  apply Equiv.ext
  intro i
  apply Subtype.ext
  rfl

theorem backwardDart_partner
    (G F : SimpleGraph (Fin n)) (s : Fin n → Nat)
    (p : GraphFiber G F s) (x : Stub s) :
    (assignmentDartEquiv G F s (backwardAssignment G F s p)) (p.val.partner x) =
      dartFlip G F ((assignmentDartEquiv G F s (backwardAssignment G F s p)) x) := by
  cases x with
  | mk v i =>
    change (⟨(p.val.partner ⟨v, i⟩).1,
      backwardEndpoint G F s p (p.val.partner ⟨v, i⟩).1
        (p.val.partner ⟨v, i⟩).2⟩ : ResidualDart G F) =
      ⟨(p.val.partner ⟨v, i⟩).1,
        reverseResidual G F (backwardEndpoint G F s p v i)⟩
    apply congrArg (fun w : ResidualNeighbor G F (p.val.partner ⟨v, i⟩).1 =>
      (⟨(p.val.partner ⟨v, i⟩).1, w⟩ : ResidualDart G F))
    apply Subtype.ext
    exact congrArg (fun z : Stub s => z.1) (p.val.involutive ⟨v, i⟩)

theorem forwardPartner_backwardAssignment
    (G F : SimpleGraph (Fin n)) (s : Fin n → Nat)
    (p : GraphFiber G F s) (x : Stub s) :
    forwardPartner G F s (backwardAssignment G F s p) x = p.val.partner x := by
  let e := assignmentDartEquiv G F s (backwardAssignment G F s p)
  have hcomm : e (p.val.partner x) = dartFlip G F (e x) :=
    backwardDart_partner G F s p x
  calc
    forwardPartner G F s (backwardAssignment G F s p) x =
        e.symm (dartFlip G F (e x)) := rfl
    _ = e.symm (e (p.val.partner x)) := congrArg e.symm hcomm.symm
    _ = p.val.partner x := e.symm_apply_apply _

theorem stubMatching_ext (s : Fin n → Nat) {p q : StubMatching s}
    (h : p.partner = q.partner) : p = q := by
  cases p
  cases q
  cases h
  rfl

theorem forwardFiber_backwardAssignment
    (G F : SimpleGraph (Fin n)) (s : Fin n → Nat)
    (p : GraphFiber G F s) :
    forwardFiber G F s (backwardAssignment G F s p) = p := by
  apply Subtype.ext
  apply stubMatching_ext s
  funext x
  exact forwardPartner_backwardAssignment G F s p x

/-- Constructed from both actual inverse identities, without a count premise. -/
def assignmentFiberEquiv (G F : SimpleGraph (Fin n)) (s : Fin n → Nat) :
    StubAssignment G F s ≃ GraphFiber G F s where
  toFun := forwardFiber G F s
  invFun := backwardAssignment G F s
  left_inv := backwardAssignment_forwardFiber G F s
  right_inv := forwardFiber_backwardAssignment G F s

instance stubFintype (s : Fin n → Nat) : Fintype (Stub s) := by
  unfold Stub
  infer_instance

instance stubMatchingFinite (s : Fin n → Nat) : Finite (StubMatching s) :=
  Finite.of_injective (fun p : StubMatching s => p.partner)
    (fun _ _ h => stubMatching_ext s h)

instance stubMatchingFintype (s : Fin n → Nat) : Fintype (StubMatching s) :=
  Fintype.ofFinite _

instance residualNeighborFintype (G F : SimpleGraph (Fin n)) (v : Fin n) :
    Fintype (ResidualNeighbor G F v) := by
  unfold ResidualNeighbor
  exact Fintype.ofFinite _

instance graphFiberFintype (G F : SimpleGraph (Fin n)) (s : Fin n → Nat) :
    Fintype (GraphFiber G F s) := by
  unfold GraphFiber
  exact Fintype.ofFinite _

instance stubAssignmentFintype (G F : SimpleGraph (Fin n)) (s : Fin n → Nat) :
    Fintype (StubAssignment G F s) := by
  classical
  unfold StubAssignment
  infer_instance

/-- A deterministic neighbor-cardinality witness constructs an actual matching. -/
theorem graphFiber_nonempty (G F : SimpleGraph (Fin n)) (s : Fin n → Nat)
    (hdegree : ∀ v, Fintype.card (ResidualNeighbor G F v) = s v) :
    Nonempty (GraphFiber G F s) := by
  let a : StubAssignment G F s := fun v =>
    Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using (hdegree v).symm)
  exact ⟨forwardFiber G F s a⟩

/-- The graph-specific fiber cardinality is a derived conclusion, including 0!.
    No constant fiber count or uniform output law is assumed. -/
theorem graphFiber_card_factorial
    (G F : SimpleGraph (Fin n)) (s : Fin n → Nat)
    (hdegree : ∀ v, Fintype.card (ResidualNeighbor G F v) = s v) :
    Fintype.card (GraphFiber G F s) = ∏ v : Fin n, Nat.factorial (s v) := by
  classical
  calc
    Fintype.card (GraphFiber G F s) = Fintype.card (StubAssignment G F s) :=
      Fintype.card_congr (assignmentFiberEquiv G F s).symm
    _ = ∏ v : Fin n, Fintype.card (Fin (s v) ≃ ResidualNeighbor G F v) := by
      unfold StubAssignment
      exact Fintype.card_pi
    _ = ∏ v : Fin n, Nat.factorial (s v) := by
      apply Finset.prod_congr rfl
      intro v hv
      let e : Fin (s v) ≃ ResidualNeighbor G F v :=
        Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using (hdegree v).symm)
      simpa only [Fintype.card_fin] using Fintype.card_equiv e

theorem graphFiber_card_pos
    (G F : SimpleGraph (Fin n)) (s : Fin n → Nat)
    (hdegree : ∀ v, Fintype.card (ResidualNeighbor G F v) = s v) :
    0 < Fintype.card (GraphFiber G F s) :=
  Fintype.card_pos_iff.mpr (graphFiber_nonempty G F s hdegree)

set_option pp.all true in
#check @graphFiber_card_factorial
set_option pp.all true in
#check @assignmentFiberEquiv
set_option pp.all true in
#check @graphFiber_nonempty
#print axioms graphFiber_card_factorial
#print axioms assignmentFiberEquiv
#print axioms graphFiber_nonempty
#print axioms graphFiber_card_pos
#print axioms backwardAssignment_forwardFiber
#print axioms forwardFiber_backwardAssignment
#print forwardFiber
#print assignmentFiberEquiv
end
end ConfigurationPairing
