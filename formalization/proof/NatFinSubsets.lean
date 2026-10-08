import NativePairLaw
import GraphFiberOnly

namespace CurveballVerified
noncomputable section

def finSetOfNat (n : Nat) (S : Finset Nat) : Finset (Fin n) :=
  Finset.univ.filter (fun v => v.val ∈ S)

def natSetOfFin {n : Nat} (S : Finset (Fin n)) : Finset Nat := S.image Fin.val

@[simp] theorem mem_finSetOfNat (n : Nat) (S : Finset Nat) (v : Fin n) :
    v ∈ finSetOfNat n S ↔ v.val ∈ S := by simp [finSetOfNat]

theorem finSet_natSet {n : Nat} (S : Finset (Fin n)) :
    finSetOfNat n (natSetOfFin S) = S := by
  ext v
  rw [mem_finSetOfNat]
  constructor
  · intro h
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp h
    have hEq : w = v := Fin.ext he
    exact hEq ▸ hw
  · intro h
    exact Finset.mem_image.mpr ⟨v,h,rfl⟩

theorem natSet_finSet (n : Nat) (S : Finset Nat) (hr : ∀ v ∈ S, v < n) :
    natSetOfFin (finSetOfNat n S) = S := by
  ext v
  constructor
  · intro h
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp h
    exact (mem_finSetOfNat n S w).mp hw
  · intro h
    exact Finset.mem_image.mpr ⟨⟨v,hr v h⟩,(mem_finSetOfNat n S _).mpr h,rfl⟩

theorem finSetOfNat_card (n : Nat) (S : Finset Nat) (hr : ∀ v ∈ S, v < n) :
    (finSetOfNat n S).card = S.card := by
  calc
    _ = (natSetOfFin (finSetOfNat n S)).card :=
      (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ = S.card := congrArg Finset.card (natSet_finSet n S hr)

theorem natSetOfFin_card {n : Nat} (S : Finset (Fin n)) :
    (natSetOfFin S).card = S.card := Finset.card_image_of_injective _ Fin.val_injective

def FinAssignment (n : Nat) (S : Finset (Fin n)) (k : Nat) :=
  {T : Finset (Fin n) // T ⊆ S ∧ T.card = k}

instance (n : Nat) (S : Finset (Fin n)) (k : Nat) : Fintype (FinAssignment n S k) := by
  classical
  unfold FinAssignment
  infer_instance

instance (n : Nat) (S : Finset (Fin n)) (k : Nat) : DecidableEq (FinAssignment n S k) := by
  unfold FinAssignment
  infer_instance

def boundedAssignmentEquiv (n : Nat) (xs : List Nat) (k : Nat)
    (hr : ∀ v ∈ xs, v < n) :
    CurveballSubsetVerified.Assignment xs k ≃ FinAssignment n (finSetOfNat n xs.toFinset) k where
  toFun T := ⟨finSetOfNat n T.val,by
    have hT := Finset.mem_powersetCard.mp T.property
    refine ⟨?_,?_⟩
    · intro v hv
      exact (mem_finSetOfNat n _ v).mpr (hT.1 ((mem_finSetOfNat n _ v).mp hv))
    · exact (finSetOfNat_card n T.val (fun v hv => hr v (List.mem_toFinset.mp (hT.1 hv)))).trans hT.2⟩
  invFun T := ⟨natSetOfFin T.val,Finset.mem_powersetCard.mpr (by
    refine ⟨?_,?_⟩
    · intro v hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
      exact (mem_finSetOfNat n xs.toFinset w).mp (T.property.1 hw)
    · exact (natSetOfFin_card T.val).trans T.property.2)⟩
  left_inv T := by
    apply Subtype.ext
    exact natSet_finSet n T.val (fun v hv => hr v
      (List.mem_toFinset.mp ((Finset.mem_powersetCard.mp T.property).1 hv)))
  right_inv T := by apply Subtype.ext; exact finSet_natSet T.val

theorem finSetOfNat_list (n : Nat) (xs : List Nat) :
    finSetOfNat n xs.toFinset = chosenSet n xs := by
  ext v
  simp [finSetOfNat,chosenSet]

/-- The actual Nat-label exclusive pool and the upstream assignment space have
    exactly the same subsets and cardinality; no list multiplicity is assumed. -/
def nativeAssignmentEquiv {n : Nat} {es : CurveballNative.Edges}
    {C : CanonicalGraph n} (href : EdgeRefines es C)
    {d : Fin n → Nat} (G : OAI.Problem315.GraphState n d)
    (hG : C.toSimpleGraph = G.val) (i j : Fin n) :
    CurveballSubsetVerified.Assignment (CurveballNative.exclusive n es i.val j.val)
      (CurveballNative.left n es i.val j.val).length ≃
      OAI.Problem315.PairFiber.Assignment G.val i j := by
  let xs := CurveballNative.exclusive n es i.val j.val
  let k := (CurveballNative.left n es i.val j.val).length
  have hr : ∀ v ∈ xs, v < n := by
    intro v hv
    exact List.mem_range.mp (List.mem_filter.mp hv).1
  have hpool : finSetOfNat n xs.toFinset = OAI.Problem315.PairFiber.singletonSet G.val i j := by
    rw [finSetOfNat_list,native_exclusive_set href,exclusive_refines,hG]
  have hk : k = (OAI.Problem315.PairFiber.leftSet G.val i j).card := by
    dsimp only [k]
    rw [native_left_card href i j,left_refines,hG]
  let e : FinAssignment n (finSetOfNat n xs.toFinset) k ≃
      OAI.Problem315.PairFiber.Assignment G.val i j :=
    { toFun := fun T => ⟨T.val,by simpa only [hpool,hk] using T.property⟩
      invFun := fun T => ⟨T.val,by simpa only [hpool,hk] using T.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (boundedAssignmentEquiv n xs k hr).trans e

theorem nativeAssignmentEquiv_val {n : Nat} {es : CurveballNative.Edges}
    {C : CanonicalGraph n} (href : EdgeRefines es C)
    {d : Fin n → Nat} (G : OAI.Problem315.GraphState n d)
    (hG : C.toSimpleGraph = G.val) (i j : Fin n)
    (T : CurveballSubsetVerified.Assignment (CurveballNative.exclusive n es i.val j.val)
      (CurveballNative.left n es i.val j.val).length) :
    (nativeAssignmentEquiv href G hG i j T).val = finSetOfNat n T.val := rfl

#print axioms boundedAssignmentEquiv
#print axioms nativeAssignmentEquiv
end
end CurveballVerified
