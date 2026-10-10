import IIDRank
import RandomBits

namespace CurveballVerified
noncomputable section
open scoped BigOperators

theorem FiniteLaw.ext_mass {α : Type} [Fintype α] {p q : FiniteLaw α}
    (h : p.mass = q.mass) : p = q := by
  cases p
  cases q
  cases h
  rfl

def mapLaw {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (p : FiniteLaw α) (f : α → β) : FiniteLaw β where
  mass y := ∑ x, if f x = y then p.mass x else 0
  nonnegative y := Finset.sum_nonneg fun x _ => by
    split_ifs <;> first | exact p.nonnegative x | exact le_rfl
  normalized := by
    rw [Finset.sum_comm]
    simpa using p.normalized

theorem map_uniform_bijection {α β : Type} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] [DecidableEq β] (e : α ≃ β) :
    mapLaw (uniformLaw α) e = uniformLaw β := by
  classical
  apply FiniteLaw.ext_mass
  funext y
  have hf : Finset.univ.filter (fun x : α => e x = y) = {e.symm y} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact e.apply_eq_iff_eq_symm_apply
  simp only [mapLaw, uniformLaw]
  rw [← Finset.sum_filter, hf]
  simp [Fintype.card_congr e]

/-- A uniform independent fair-bit block is sent by the actual decoder to the
    uniform word law. The entropy premise is the source law, not an axiom asserting
    that this decoder's result is uniform. -/
theorem fair_bits_uniform_word (w : Nat) :
    mapLaw (uniformLaw (Fin w → Bool)) (@decodeBits w) =
      uniformLaw (Fin (2 ^ w)) := by
  have hp : 0 < 2 ^ w := by positivity
  letI : Nonempty (Fin (2 ^ w)) := ⟨⟨0,hp⟩⟩
  exact map_uniform_bijection (Equiv.ofBijective (@decodeBits w) (decodeBits_bijective w))

#print axioms mapLaw
#print axioms map_uniform_bijection
#print axioms fair_bits_uniform_word
end
end CurveballVerified
