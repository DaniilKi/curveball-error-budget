import ConfigurationGraphOracle

/- Executable per-output certificate. No random-input or runtime law is asserted. -/
namespace ConfigurationPairing

variable {n m : Nat}

instance certificateStubDecidableEq (s : Fin n → Nat) : DecidableEq (Stub s) := by
  unfold Stub
  infer_instance

instance certificateStubFintype (s : Fin n → Nat) : Fintype (Stub s) := by
  unfold Stub
  infer_instance

def execDegree (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) : Nat :=
  (Finset.univ.filter (fun w => G.Adj v w)).card

theorem labeledDegree_eq_execDegree (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) : labeledDegree G v = execDegree G v := by
  exact Fintype.card_subtype (fun w => G.Adj v w)

def togglePosition (z : Fin m × Bool) : Fin m × Bool := (z.1, !z.2)

@[simp] theorem togglePosition_involutive (z : Fin m × Bool) :
    togglePosition (togglePosition z) = z := by
  rcases z with ⟨i,b⟩
  simp [togglePosition]

def ownerPairGraph (owners : Fin m × Bool → Fin n) : SimpleGraph (Fin n) where
  Adj v w := v ≠ w ∧ ∃ z, owners z = v ∧ owners (togglePosition z) = w
  symm := ⟨by
    rintro v w ⟨hne,z,hv,hw⟩
    exact ⟨hne.symm,togglePosition z,hw,by simpa using hv⟩⟩
  loopless := ⟨by
    intro v h
    exact h.1 rfl⟩

instance ownerPairGraphDecidable (owners : Fin m × Bool → Fin n) :
    DecidableRel (ownerPairGraph owners).Adj := by
  intro v w
  unfold ownerPairGraph
  infer_instance

def OwnerGood (F : SimpleGraph (Fin n)) (owners : Fin m × Bool → Fin n) : Prop :=
  (∀ z, owners (togglePosition z) ≠ owners z) ∧
  (∀ z z', owners z = owners z' →
    owners (togglePosition z) = owners (togglePosition z') → z = z') ∧
  (∀ z, ¬ F.Adj (owners z) (owners (togglePosition z)))

instance ownerGoodDecidable (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (owners : Fin m × Bool → Fin n) : Decidable (OwnerGood F owners) := by
  unfold OwnerGood
  infer_instance

theorem adjacentPairing_apply_slot (s : Fin n → Nat)
    (slots : Fin m × Bool ≃ Stub s) (z : Fin m × Bool) :
    (adjacentPairing s m slots).partner (slots z) = slots (togglePosition z) := by
  simp only [adjacentPairing, Equiv.symm_apply_apply, togglePosition]

theorem projectedGraph_eq_ownerPairGraph (s : Fin n → Nat)
    (slots : Fin m × Bool ≃ Stub s) (owners : Fin m × Bool → Fin n)
    (ho : ∀ z, (slots z).1 = owners z) :
    projectedGraph s (adjacentPairing s m slots) = ownerPairGraph owners := by
  ext v w
  change (v ≠ w ∧ ∃ i : Fin (s v),
    ((adjacentPairing s m slots).partner ⟨v,i⟩).1 = w) ↔
    (v ≠ w ∧ ∃ z, owners z = v ∧ owners (togglePosition z) = w)
  constructor
  · rintro ⟨hne,i,hi⟩
    obtain ⟨z,hz⟩ := slots.surjective (⟨v,i⟩ : Stub s)
    refine ⟨hne,z,?_,?_⟩
    · rw [← ho z,hz]
    · rw [← ho (togglePosition z), ← adjacentPairing_apply_slot s slots z,hz]
      exact hi
  · rintro ⟨hne,z,hv,hw⟩
    have hx : (slots z).1 = v := (ho z).trans hv
    have hp : ((adjacentPairing s m slots).partner (slots z)).1 = w := by
      rw [adjacentPairing_apply_slot s slots z,ho (togglePosition z),hw]
    rcases hs : slots z with ⟨u,i⟩
    rw [hs] at hx hp
    change u = v at hx
    subst u
    exact ⟨hne,i,hp⟩

theorem ownerGood_matching (F : SimpleGraph (Fin n)) (s : Fin n → Nat)
    (slots : Fin m × Bool ≃ Stub s) (owners : Fin m × Bool → Fin n)
    (ho : ∀ z, (slots z).1 = owners z) (hg : OwnerGood F owners) :
    GoodMatching F s (adjacentPairing s m slots) := by
  have howner (x : Stub s) : owners (slots.symm x) = x.1 := by
    rw [← ho,slots.apply_symm_apply]
  have hpartner (x : Stub s) :
      owners (togglePosition (slots.symm x)) =
        ((adjacentPairing s m slots).partner x).1 := by
    rw [← ho, ← adjacentPairing_apply_slot s slots (slots.symm x),
      slots.apply_symm_apply]
  refine ⟨?_,?_,?_⟩
  · intro x
    simpa only [howner x,hpartner x] using hg.1 (slots.symm x)
  · intro v i j hij
    have he : slots.symm (⟨v,i⟩ : Stub s) = slots.symm ⟨v,j⟩ :=
      hg.2.1 _ _ ((howner (⟨v,i⟩ : Stub s)).trans (howner (⟨v,j⟩ : Stub s)).symm)
        ((hpartner (⟨v,i⟩ : Stub s)).trans (hij.trans (hpartner (⟨v,j⟩ : Stub s)).symm))
    have hx := slots.symm.injective he
    cases hx
    rfl
  · intro x
    simpa only [howner x,hpartner x] using hg.2.2 (slots.symm x)

/- Finite, computable checks. The residual degrees are explicit input data;
   equality to the abstract residualDegree is proved after checking. -/
def OwnerCertificateConditions (F G : SimpleGraph (Fin n))
    [DecidableRel F.Adj] [DecidableRel G.Adj] (d s : Fin n → Nat)
    (owners : Fin m × Bool → Fin n) (lift : Fin m × Bool → Stub s) : Prop :=
  (∀ v, d v = execDegree F v + s v) ∧
  (∀ z z', lift z = lift z' → z = z') ∧
  (∀ x : Stub s, ∃ z, lift z = x) ∧
  (∀ z, (lift z).1 = owners z) ∧
  OwnerGood F owners ∧
  (∀ v w, G.Adj v w ↔ F.Adj v w ∨ (ownerPairGraph owners).Adj v w) ∧
  (∀ v, execDegree G v = d v)

instance ownerCertificateDecidable (F G : SimpleGraph (Fin n))
    [DecidableRel F.Adj] [DecidableRel G.Adj] (d s : Fin n → Nat)
    (owners : Fin m × Bool → Fin n) (lift : Fin m × Bool → Stub s) :
    Decidable (OwnerCertificateConditions F G d s owners lift) := by
  unfold OwnerCertificateConditions
  infer_instance

def ownerCertificateCheck (F G : SimpleGraph (Fin n))
    [DecidableRel F.Adj] [DecidableRel G.Adj] (d s : Fin n → Nat)
    (owners : Fin m × Bool → Fin n) (lift : Fin m × Bool → Stub s) : Bool :=
  decide (OwnerCertificateConditions F G d s owners lift)

theorem ownerCertificateCheck_sound (F G : SimpleGraph (Fin n))
    [DecidableRel F.Adj] [DecidableRel G.Adj] (d s : Fin n → Nat)
    (owners : Fin m × Bool → Fin n) (lift : Fin m × Bool → Stub s)
    (hcheck : ownerCertificateCheck F G d s owners lift = true) :
    ∃ (g : TargetGraph F d) (slots : Fin m × Bool ≃ Stub (residualDegree F d)),
      g.val = G ∧ (∀ z, (slots z).1 = owners z) ∧
      graphDecoder F d (adjacentPairing (residualDegree F d) m slots) = some g := by
  classical
  have h : OwnerCertificateConditions F G d s owners lift := of_decide_eq_true hcheck
  rcases h with ⟨hdegree,hinj,hsurj,ho,hgood,hgraph,hfinal⟩
  have hs : s = residualDegree F d := by
    funext v
    unfold residualDegree
    rw [labeledDegree_eq_execDegree]
    have hv := hdegree v
    omega
  subst s
  let slots : Fin m × Bool ≃ Stub (residualDegree F d) := Equiv.ofBijective lift ⟨hinj,hsurj⟩
  have hslots : ∀ z, (slots z).1 = owners z := ho
  have he : G = decodedGraph F (residualDegree F d)
      (adjacentPairing (residualDegree F d) m slots) := by
    unfold decodedGraph
    rw [projectedGraph_eq_ownerPairGraph _ slots owners hslots]
    ext v w
    exact hgraph v w
  have hFG : F ≤ G := by
    rw [he]
    exact le_sup_left
  have hd : ∀ v, labeledDegree G v = d v := by
    intro v
    rw [labeledDegree_eq_execDegree]
    exact hfinal v
  let g : TargetGraph F d := ⟨G,hFG,hd⟩
  refine ⟨g,slots,rfl,hslots,?_⟩
  apply (graphDecoder_some_iff F d _ g).mpr
  change ProjectsTo G F (residualDegree F d) _
  rw [he]
  exact good_projectsTo F _ _ (ownerGood_matching F _ slots owners hslots hgood)

/-- Explicit finite edge-list graph used to reify a captured adjacency result. -/
def edgeListGraph (edges : List (Fin n × Fin n)) : SimpleGraph (Fin n) where
  Adj v w := v ≠ w ∧ ((v,w) ∈ edges ∨ (w,v) ∈ edges)
  symm := ⟨by
    rintro v w ⟨hne,h⟩
    exact ⟨hne.symm,h.symm⟩⟩
  loopless := ⟨by
    intro v h
    exact h.1 rfl⟩

instance edgeListGraphDecidable (edges : List (Fin n × Fin n)) :
    DecidableRel (edgeListGraph edges).Adj := by
  intro v w
  unfold edgeListGraph
  infer_instance

def CanonicalEdgeEncoding (edges : List (Fin n × Fin n)) : Prop :=
  edges.Nodup ∧ ∀ e ∈ edges, e.1.val < e.2.val

instance canonicalEdgeEncodingDecidable (edges : List (Fin n × Fin n)) :
    Decidable (CanonicalEdgeEncoding edges) := by
  unfold CanonicalEdgeEncoding
  infer_instance

set_option pp.all true in
#check @ownerCertificateCheck_sound
set_option pp.all true in
#check @projectedGraph_eq_ownerPairGraph
#print axioms ownerCertificateCheck_sound
#print axioms projectedGraph_eq_ownerPairGraph
#print axioms ownerGood_matching
#print axioms ownerCertificateCheck
#print ownerCertificateCheck
end ConfigurationPairing
