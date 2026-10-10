import ConfigurationFiber
import ConfigurationRejectionLaw

/- Ideal distinct-stub permutation law. No physical/seeded RNG claim. -/
namespace ConfigurationPairing
noncomputable section
open CurveballVerified
open scoped BigOperators

variable {n : Nat}

def stubRank (s : Fin n → Nat) : Stub s ≃ Fin (Fintype.card (Stub s)) :=
  Fintype.equivFin _

def IsLower (s : Fin n → Nat) (p : StubMatching s) (x : Stub s) : Prop :=
  stubRank s x < stubRank s (p.partner x)

def PairRepresentative (s : Fin n → Nat) (p : StubMatching s) :=
  {x : Stub s // IsLower s p x}

instance pairRepresentativeFintype (s : Fin n → Nat) (p : StubMatching s) :
    Fintype (PairRepresentative s p) := by
  unfold PairRepresentative
  exact Fintype.ofFinite _

theorem lower_partner_of_not_lower (s : Fin n → Nat) (p : StubMatching s)
    (x : Stub s) (h : ¬ IsLower s p x) : IsLower s p (p.partner x) := by
  have hne : stubRank s (p.partner x) ≠ stubRank s x :=
    fun he => p.noFixed x ((stubRank s).injective he)
  have hlt : stubRank s (p.partner x) < stubRank s x :=
    lt_of_le_of_ne (le_of_not_gt h) hne
  simpa only [IsLower, p.involutive x] using hlt

theorem not_lower_partner (s : Fin n → Nat) (p : StubMatching s)
    (r : PairRepresentative s p) : ¬ IsLower s p (p.partner r.val) := by
  change ¬ stubRank s (p.partner r.val) < stubRank s (p.partner (p.partner r.val))
  rw [p.involutive]
  exact not_lt_of_gt r.property

def orientedStub (s : Fin n → Nat) (p : StubMatching s)
    (z : PairRepresentative s p × Bool) : Stub s :=
  if z.2 then p.partner z.1.val else z.1.val

def stubOrientation (s : Fin n → Nat) (p : StubMatching s) (x : Stub s) :
    PairRepresentative s p × Bool := by
  classical
  exact if h : IsLower s p x then (⟨x,h⟩,false)
    else (⟨p.partner x,lower_partner_of_not_lower s p x h⟩,true)

def orientationEquiv (s : Fin n → Nat) (p : StubMatching s) :
    PairRepresentative s p × Bool ≃ Stub s where
  toFun := orientedStub s p
  invFun := stubOrientation s p
  left_inv := by
    classical
    rintro ⟨r,b⟩
    cases b <;> simp [orientedStub, stubOrientation, r.property,
      not_lower_partner s p r]
    · apply Prod.ext
      · apply Subtype.ext
        rfl
      · rfl
    · apply Prod.ext
      · apply Subtype.ext
        exact p.involutive r.val
      · rfl
  right_inv := by
    classical
    intro x
    by_cases h : IsLower s p x <;>
      simp [stubOrientation, orientedStub, h, p.involutive x]

theorem orientationEquiv_flip (s : Fin n → Nat) (p : StubMatching s)
    (z : PairRepresentative s p × Bool) :
    orientationEquiv s p (z.1,!z.2) = p.partner (orientationEquiv s p z) := by
  rcases z with ⟨r,b⟩
  cases b <;> simp [orientationEquiv, orientedStub, p.involutive r.val]

theorem representative_card_eq (s : Fin n → Nat) (p q : StubMatching s) :
    Fintype.card (PairRepresentative s p) = Fintype.card (PairRepresentative s q) := by
  have hp := Fintype.card_congr (orientationEquiv s p)
  have hq := Fintype.card_congr (orientationEquiv s q)
  simp only [Fintype.card_prod, Fintype.card_bool] at hp hq
  omega

def matchingTransport (s : Fin n → Nat) (p q : StubMatching s) : Equiv.Perm (Stub s) :=
  (orientationEquiv s p).symm.trans
    ((Equiv.prodCongr (Fintype.equivOfCardEq (representative_card_eq s p q))
      (Equiv.refl Bool)).trans (orientationEquiv s q))

theorem matchingTransport_intertwines (s : Fin n → Nat) (p q : StubMatching s)
    (x : Stub s) :
    matchingTransport s p q (p.partner x) = q.partner (matchingTransport s p q x) := by
  let k : PairRepresentative s p ≃ PairRepresentative s q :=
    Fintype.equivOfCardEq (representative_card_eq s p q)
  have hrep (z : PairRepresentative s p × Bool) :
      matchingTransport s p q (orientationEquiv s p z) =
        orientationEquiv s q (k z.1,z.2) := by
    rcases z with ⟨r,b⟩
    simp [matchingTransport, k]
  obtain ⟨z,rfl⟩ := (orientationEquiv s p).surjective x
  rw [← orientationEquiv_flip s p z, hrep, hrep]
  exact orientationEquiv_flip s q (k z.1,z.2)

def relabelMatching (s : Fin n → Nat) (e : Equiv.Perm (Stub s))
    (p : StubMatching s) : StubMatching s where
  partner x := e (p.partner (e.symm x))
  involutive := by
    intro x
    change e (p.partner (e.symm (e (p.partner (e.symm x))))) = x
    rw [e.symm_apply_apply, p.involutive, e.apply_symm_apply]
  noFixed := by
    intro x h
    apply p.noFixed (e.symm x)
    have he := congrArg e.symm h
    simpa only [e.symm_apply_apply] using he

theorem relabelMatching_comp (s : Fin n → Nat) (e t : Equiv.Perm (Stub s))
    (p : StubMatching s) :
    relabelMatching s (e.trans t) p = relabelMatching s t (relabelMatching s e p) := by
  apply stubMatching_ext s
  rfl

theorem relabelMatching_inverse (s : Fin n → Nat) (e : Equiv.Perm (Stub s))
    (p : StubMatching s) : relabelMatching s e.symm (relabelMatching s e p) = p := by
  apply stubMatching_ext s
  funext x
  simp [relabelMatching]

theorem relabelMatching_transport (s : Fin n → Nat) (p q : StubMatching s) :
    relabelMatching s (matchingTransport s p q) p = q := by
  apply stubMatching_ext s
  funext x
  change matchingTransport s p q (p.partner ((matchingTransport s p q).symm x)) =
    q.partner x
  rw [matchingTransport_intertwines, Equiv.apply_symm_apply]

def RelabelFiber (s : Fin n → Nat) (base p : StubMatching s) :=
  {e : Equiv.Perm (Stub s) // relabelMatching s e base = p}

instance relabelFiberFintype (s : Fin n → Nat) (base p : StubMatching s) :
    Fintype (RelabelFiber s base p) := by
  unfold RelabelFiber
  exact Fintype.ofFinite _

def relabelFiberEquiv (s : Fin n → Nat) (base p q : StubMatching s) :
    RelabelFiber s base p ≃ RelabelFiber s base q := by
  let t := matchingTransport s p q
  have ht : relabelMatching s t p = q := relabelMatching_transport s p q
  have hti : relabelMatching s t.symm q = p := by
    rw [← ht]
    exact relabelMatching_inverse s t p
  exact {
    toFun := fun e => ⟨e.val.trans t, by rw [relabelMatching_comp, e.property, ht]⟩
    invFun := fun e => ⟨e.val.trans t.symm, by rw [relabelMatching_comp, e.property, hti]⟩
    left_inv := by
      intro e
      apply Subtype.ext
      apply Equiv.ext
      intro x
      simp
    right_inv := by
      intro e
      apply Subtype.ext
      apply Equiv.ext
      intro x
      simp }

def idealMatchingLaw (s : Fin n → Nat) (base : StubMatching s) :
    FiniteLaw (StubMatching s) := by
  classical
  exact mapLaw (uniformLaw (Equiv.Perm (Stub s))) (fun e => relabelMatching s e base)

def uniformMatchingLaw (s : Fin n → Nat) (base : StubMatching s) :
    FiniteLaw (StubMatching s) :=
  @uniformLaw (StubMatching s) (stubMatchingFintype s) ⟨base⟩

theorem idealMatchingLaw_uniform (s : Fin n → Nat) (base : StubMatching s) :
    idealMatchingLaw s base = uniformMatchingLaw s base := by
  classical
  let c := Fintype.card (RelabelFiber s base base)
  have hf (p : StubMatching s) :
      (Finset.univ.filter (fun e : Equiv.Perm (Stub s) =>
        relabelMatching s e base = p)).card = c := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (relabelFiberEquiv s base p base)
  have hm (p : StubMatching s) :
      (idealMatchingLaw s base).mass p = (c : ℝ) / Fintype.card (Equiv.Perm (Stub s)) := by
    simp only [idealMatchingLaw, mapLaw, uniformLaw]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, hf p]
    ring
  have hn := (idealMatchingLaw s base).normalized
  simp_rw [hm] at hn
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hn
  have hcard : (Fintype.card (StubMatching s) : ℝ) ≠ 0 := by
    letI : Nonempty (StubMatching s) := ⟨base⟩
    exact_mod_cast Fintype.card_ne_zero
  apply FiniteLaw.ext_mass
  funext p
  change (idealMatchingLaw s base).mass p = (1 : ℝ) / Fintype.card (StubMatching s)
  rw [hm]
  apply (eq_div_iff hcard).mpr
  simpa only [mul_comm] using hn

/-- The two Boolean slots are the adjacent endpoints of each ordered pair. -/
def adjacentPairing (s : Fin n → Nat) (m : Nat) (slots : Fin m × Bool ≃ Stub s) :
    StubMatching s where
  partner x := slots ((slots.symm x).1, !(slots.symm x).2)
  involutive := by
    intro x
    simp only [slots.symm_apply_apply, Bool.not_not, slots.apply_symm_apply]
  noFixed := by
    intro x h
    have hb := congrArg (fun y => (slots.symm y).2) h
    simp only [slots.symm_apply_apply] at hb
    cases hx : (slots.symm x).2 <;> simp [hx] at hb

theorem relabelMatching_adjacent (s : Fin n → Nat) (m : Nat)
    (slots : Fin m × Bool ≃ Stub s) (e : Equiv.Perm (Stub s)) :
    relabelMatching s e (adjacentPairing s m slots) = adjacentPairing s m (slots.trans e) := by
  apply stubMatching_ext s
  rfl

def idealAdjacentLaw (s : Fin n → Nat) (m : Nat) (slots : Fin m × Bool ≃ Stub s) :
    FiniteLaw (StubMatching s) := by
  classical
  exact mapLaw (uniformLaw (Equiv.Perm (Stub s)))
    (fun e => adjacentPairing s m (slots.trans e))

theorem idealAdjacentLaw_uniform (s : Fin n → Nat) (m : Nat)
    (slots : Fin m × Bool ≃ Stub s) :
    idealAdjacentLaw s m slots = uniformMatchingLaw s (adjacentPairing s m slots) := by
  have h : idealAdjacentLaw s m slots = idealMatchingLaw s (adjacentPairing s m slots) := by
    rfl
  rw [h, idealMatchingLaw_uniform]

set_option pp.all true in
#check @idealMatchingLaw_uniform
set_option pp.all true in
#check @idealAdjacentLaw_uniform
#print axioms orientationEquiv
#print axioms matchingTransport_intertwines
#print axioms relabelFiberEquiv
#print axioms idealMatchingLaw_uniform
#print axioms idealAdjacentLaw_uniform
end
end ConfigurationPairing
