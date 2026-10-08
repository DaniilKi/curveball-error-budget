import GraphStructureOnly

namespace OAI.Problem315.PairResampling
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def SameFiber {n : ℕ} (a : Finset (Fin n)) (G H : SimpleGraph (Fin n)) : Prop :=
  (∀ u ∉ a, ∀ v ∉ a, G.Adj u v ↔ H.Adj u v) ∧
  (∀ u ∈ a, ∀ v ∈ a, G.Adj u v ↔ H.Adj u v) ∧
  (∀ w ∉ a, (a.filter (G.Adj w)).card = (a.filter (H.Adj w)).card)

@[refl] theorem SameFiber.refl {n : ℕ} (a : Finset (Fin n))
    (G : SimpleGraph (Fin n)) : SameFiber a G G := by
  unfold SameFiber
  exact ⟨fun _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl, fun _ _ => rfl⟩

@[symm] theorem SameFiber.symm {n : ℕ} {a : Finset (Fin n)}
    {G H : SimpleGraph (Fin n)} (h : SameFiber a G H) : SameFiber a H G :=
  ⟨fun u hu v hv => (h.1 u hu v hv).symm,
   fun u hu v hv => (h.2.1 u hu v hv).symm,
   fun w hw => (h.2.2 w hw).symm⟩

@[trans] theorem SameFiber.trans {n : ℕ} {a : Finset (Fin n)}
    {G H K : SimpleGraph (Fin n)} (h : SameFiber a G H) (k : SameFiber a H K) :
    SameFiber a G K :=
  ⟨fun u hu v hv => (h.1 u hu v hv).trans (k.1 u hu v hv),
   fun u hu v hv => (h.2.1 u hu v hv).trans (k.2.1 u hu v hv),
   fun w hw => (h.2.2 w hw).trans (k.2.2 w hw)⟩

theorem graphDegree_partition {n : ℕ} (a : Finset (Fin n))
    (G : SimpleGraph (Fin n)) (w : Fin n) :
    (a.filter (G.Adj w)).card + ((Finset.univ \ a).filter (G.Adj w)).card =
      graphDegree G w := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (G.Adj w)) (p := fun v => v ∈ a)
  have heq : (Finset.univ.filter (G.Adj w)).filter (fun v => v ∈ a) = a.filter (G.Adj w) := by
    ext v
    simp [and_comm]
  have hneq : (Finset.univ.filter (G.Adj w)).filter (fun v => v ∉ a) =
      (Finset.univ \ a).filter (G.Adj w) := by
    ext v
    simp [and_comm]
  rw [heq, hneq] at h
  exact h

theorem sameFiber_of_fixed_edges {n : ℕ} (a : Finset (Fin n))
    {G H : SimpleGraph (Fin n)}
    (hdeg : ∀ w, graphDegree G w = graphDegree H w)
    (hout : ∀ u ∉ a, ∀ v ∉ a, G.Adj u v ↔ H.Adj u v)
    (hin : ∀ u ∈ a, ∀ v ∈ a, G.Adj u v ↔ H.Adj u v) :
    SameFiber a G H := by
  refine ⟨hout, hin, ?_⟩
  intro w hw
  have hext : (Finset.univ \ a).filter (G.Adj w) =
      (Finset.univ \ a).filter (H.Adj w) := by
    apply Finset.filter_congr
    intro v hv
    exact hout w hw v (Finset.mem_sdiff.mp hv).2
  have hG := graphDegree_partition a G w
  have hH := graphDegree_partition a H w
  rw [hext, hdeg w] at hG
  omega

theorem sameFiber_state_iff {n : ℕ} {d : Fin n → ℕ} (a : Finset (Fin n))
    (G H : GraphState n d) :
    SameFiber a G.val H.val ↔
      (∀ u ∉ a, ∀ v ∉ a, G.val.Adj u v ↔ H.val.Adj u v) ∧
      (∀ u ∈ a, ∀ v ∈ a, G.val.Adj u v ↔ H.val.Adj u v) := by
  refine ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ?_⟩
  apply sameFiber_of_fixed_edges a _ h.1 h.2
  intro w
  exact (G.property w).trans (H.property w).symm

def pairs (n : ℕ) : Finset (Finset (Fin n)) := Finset.univ.powersetCard 2

variable {n : ℕ} {d : Fin n → ℕ} (a : Finset (Fin n))

def fiberStates (a : Finset (Fin n)) (G : GraphState n d) : Finset (GraphState n d) :=
  Finset.univ.filter (fun H => SameFiber a G.val H.val)

@[simp] theorem mem_fiberStates (G H : GraphState n d) :
    H ∈ fiberStates a G ↔ SameFiber a G.val H.val := by
  simp [fiberStates]

@[simp] theorem self_mem_fiberStates (G : GraphState n d) : G ∈ fiberStates a G := by
  exact (mem_fiberStates a G G).mpr (SameFiber.refl a G.val)

theorem fiberStates_nonempty (G : GraphState n d) : (fiberStates a G).Nonempty :=
  ⟨G, self_mem_fiberStates a G⟩

end
end OAI.Problem315.PairResampling
