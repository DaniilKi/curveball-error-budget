import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Tauto
import Lean.Elab.Tactic.Omega

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/Definitions.lean -/
section

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem315

def graphDegree {n : Nat} (G : SimpleGraph (Fin n)) (v : Fin n) : Nat := by
  classical
  exact (Finset.univ.filter (fun w => G.Adj v w)).card

def Realizes (n : Nat) (d : Fin n → Nat) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v, graphDegree G v = d v

abbrev GraphState (n : Nat) (d : Fin n → Nat) :=
  {G : SimpleGraph (Fin n) // Realizes n d G}

def Graphical (n : Nat) (d : Fin n → Nat) : Prop :=
  Nonempty (GraphState n d)

abbrev FourSet (n : Nat) := {S : Finset (Fin n) // S.card = 4}

def IsPerfectMatchingOn {n : Nat} (S : Finset (Fin n))
    (M : SimpleGraph (Fin n)) : Prop :=
  ∀ v, (v ∈ S → ∃! w, M.Adj v w) ∧
    (v ∉ S → ∀ w, ¬ M.Adj v w)

abbrev PerfectMatching {n : Nat} (S : FourSet n) :=
  {M : SimpleGraph (Fin n) // IsPerfectMatchingOn S.1 M}

abbrev SwitchProposal (n : Nat) :=
  Σ S : FourSet n,
    {p : PerfectMatching S × PerfectMatching S // p.1 ≠ p.2}

def removedMatching {n : Nat} (p : SwitchProposal n) : SimpleGraph (Fin n) :=
  p.2.val.1.val

def addedMatching {n : Nat} (p : SwitchProposal n) : SimpleGraph (Fin n) :=
  p.2.val.2.val

def validSwitch {n : Nat} (G : SimpleGraph (Fin n))
    (p : SwitchProposal n) : Prop :=
  (∀ ⦃u v⦄, (removedMatching p).Adj u v → G.Adj u v) ∧
  (∀ ⦃u v⦄, (addedMatching p).Adj u v → ¬ G.Adj u v)

def replaceEdges {n : Nat} (G M N : SimpleGraph (Fin n)) :
    SimpleGraph (Fin n) where
  Adj u v := (G.Adj u v ∧ ¬ M.Adj u v) ∨ N.Adj u v
  symm := by
    constructor
    intro u v h
    rcases h with h | h
    · left
      exact ⟨G.symm.symm u v h.1, fun hm => h.2 (M.symm.symm v u hm)⟩
    · right
      exact N.symm.symm u v h
  loopless := by
    constructor
    intro v h
    rcases h with h | h
    · exact G.loopless.irrefl v h.1
    · exact N.loopless.irrefl v h

def proposalResult {n : Nat} (G : SimpleGraph (Fin n))
    (p : SwitchProposal n) : SimpleGraph (Fin n) := by
  classical
  exact
    if validSwitch G p then
      replaceEdges G (removedMatching p) (addedMatching p)
    else G

def allGraphStates (n : Nat) (d : Fin n → Nat) :
    Finset (GraphState n d) := by
  classical
  exact Finset.univ

def allProposals (n : Nat) : Finset (SwitchProposal n) := by
  classical
  exact Finset.univ

def stateCount (n : Nat) (d : Fin n → Nat) : Nat :=
  (allGraphStates n d).card

def switchKernel (n : Nat) (d : Fin n → Nat)
    (G H : GraphState n d) : ℝ := by
  classical
  exact
    (if G = H then (1 : ℝ) / 2 else 0) +
      (((allProposals n).filter
          (fun p => proposalResult G.val p = H.val)).card : ℝ) /
        (12 * (Nat.choose n 4 : ℝ))

def kernelPow (n : Nat) (d : Fin n → Nat) :
    Nat → GraphState n d → GraphState n d → ℝ := by
  classical
  intro t
  induction t with
  | zero =>
      exact fun G H => if G = H then 1 else 0
  | succ t previous =>
      exact fun G H =>
        Finset.sum (allGraphStates n d)
          (fun K => previous G K * switchKernel n d K H)

def uniformAverage (n : Nat) (d : Fin n → Nat)
    (f : GraphState n d → ℝ) : ℝ :=
  Finset.sum (allGraphStates n d) (fun G => f G) /
    (stateCount n d : ℝ)

def uniformInner (n : Nat) (d : Fin n → Nat)
    (f g : GraphState n d → ℝ) : ℝ :=
  uniformAverage n d (fun G => f G * g G)

def uniformVariance (n : Nat) (d : Fin n → Nat)
    (f : GraphState n d → ℝ) : ℝ :=
  uniformAverage n d
    (fun G => (f G - uniformAverage n d f) ^ 2)

def markovApply (n : Nat) (d : Fin n → Nat)
    (f : GraphState n d → ℝ) (G : GraphState n d) : ℝ :=
  Finset.sum (allGraphStates n d)
    (fun H => switchKernel n d G H * f H)

def dirichletEnergy (n : Nat) (d : Fin n → Nat)
    (f : GraphState n d → ℝ) : ℝ :=
  uniformInner n d f (fun G => f G - markovApply n d f G)

def hasSpectralGapAtLeast (n : Nat) (d : Fin n → Nat) (γ : ℝ) : Prop :=
  ∀ f : GraphState n d → ℝ,
    γ * uniformVariance n d f ≤ dirichletEnergy n d f

def tvDistanceFrom (n : Nat) (d : Fin n → Nat)
    (t : Nat) (G : GraphState n d) : ℝ :=
  (1 / 2 : ℝ) *
    Finset.sum (allGraphStates n d)
      (fun H =>
        |kernelPow n d t G H - (1 : ℝ) / (stateCount n d : ℝ)|)

def MixedAt (n : Nat) (d : Fin n → Nat) (t : Nat) : Prop :=
  ∀ G : GraphState n d, tvDistanceFrom n d t G ≤ (1 : ℝ) / 4

def mixingTime (n : Nat) (d : Fin n → Nat)
    (h : ∃ t : Nat, MixedAt n d t) : Nat := by
  classical
  exact Nat.find h

def SwitchStep (n : Nat) (d : Fin n → Nat)
    (G H : GraphState n d) : Prop :=
  ∃ p : SwitchProposal n,
    validSwitch G.val p ∧ proposalResult G.val p = H.val

end Problem315

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/Definitions.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairFiber.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairFiber

variable {V : Type*} [sectionFintypeV : Fintype V]

def Outside (i j w : V) : Prop := w ≠ i ∧ w ≠ j

def edgeBit (G : SimpleGraph V) (u v : V) : Nat := by
  classical
  exact if G.Adj u v then 1 else 0

def key (i j : V) (G : SimpleGraph V) :
    (V → V → Prop) × Prop × (V → Nat) :=
  (fun u v => Outside i j u ∧ Outside i j v ∧ G.Adj u v,
   G.Adj i j, fun w => edgeBit G i w + edgeBit G j w)

def singletonSet (G : SimpleGraph V) (i j : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun w => Outside i j w ∧ Xor (G.Adj i w) (G.Adj j w))

def leftSet (G : SimpleGraph V) (i j : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun w => Outside i j w ∧ G.Adj i w ∧ ¬ G.Adj j w)

def commonSet (G : SimpleGraph V) (i j : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun w => Outside i j w ∧ G.Adj i w ∧ G.Adj j w)

@[simp] theorem mem_singletonSet (G : SimpleGraph V) (i j w : V) :
    w ∈ singletonSet G i j ↔ Outside i j w ∧ Xor (G.Adj i w) (G.Adj j w) := by
  classical
  simp [singletonSet]

@[simp] theorem mem_leftSet (G : SimpleGraph V) (i j w : V) :
    w ∈ leftSet G i j ↔ Outside i j w ∧ G.Adj i w ∧ ¬ G.Adj j w := by
  classical
  simp [leftSet]

@[simp] theorem mem_commonSet (G : SimpleGraph V) (i j w : V) :
    w ∈ commonSet G i j ↔ Outside i j w ∧ G.Adj i w ∧ G.Adj j w := by
  classical
  simp [commonSet]

theorem leftSet_subset_singletonSet (G : SimpleGraph V) (i j : V) :
    leftSet G i j ⊆ singletonSet G i j := by
  intro w hw
  rcases (mem_leftSet G i j w).mp hw with ⟨ho, hi, hj⟩
  exact (mem_singletonSet G i j w).mpr ⟨ho, Or.inl ⟨hi, hj⟩⟩

include sectionFintypeV in
theorem key_count {i j : V} {G H : SimpleGraph V}
    (h : key i j G = key i j H) (w : V) :
    edgeBit G i w + edgeBit G j w = edgeBit H i w + edgeBit H j w := by
  have retainedsectionFintypeV := sectionFintypeV
  exact
  congrFun (congrArg (fun k => k.2.2) h) w

include sectionFintypeV in
theorem key_internal {i j : V} {G H : SimpleGraph V}
    (h : key i j G = key i j H) : G.Adj i j ↔ H.Adj i j := by
  have retainedsectionFintypeV := sectionFintypeV
  exact
  Iff.of_eq (congrArg (fun k => k.2.1) h)

include sectionFintypeV in
theorem key_outside {i j u v : V} {G H : SimpleGraph V}
    (h : key i j G = key i j H) (hu : Outside i j u) (hv : Outside i j v) :
    G.Adj u v ↔ H.Adj u v := by
  have retainedsectionFintypeV := sectionFintypeV
  have hh := congrFun (congrFun (congrArg Prod.fst h) u) v
  change (Outside i j u ∧ Outside i j v ∧ G.Adj u v) =
    (Outside i j u ∧ Outside i j v ∧ H.Adj u v) at hh
  simpa only [hu, hv, true_and] using Iff.of_eq hh

theorem singletonSet_eq_of_key_eq {i j : V} {G H : SimpleGraph V}
    (h : key i j G = key i j H) : singletonSet G i j = singletonSet H i j := by
  classical
  ext w
  have hc := key_count h w
  by_cases gi : G.Adj i w <;> by_cases gj : G.Adj j w <;>
    by_cases hi : H.Adj i w <;> by_cases hj : H.Adj j w <;>
    simp_all [edgeBit, Xor]

theorem commonSet_eq_of_key_eq {i j : V} {G H : SimpleGraph V}
    (h : key i j G = key i j H) : commonSet G i j = commonSet H i j := by
  classical
  ext w
  have hc := key_count h w
  by_cases gi : G.Adj i w <;> by_cases gj : G.Adj j w <;>
    by_cases hi : H.Adj i w <;> by_cases hj : H.Adj j w <;>
    simp_all [edgeBit]

theorem key_left_adj {i j w : V} {G H : SimpleGraph V}
    (h : key i j G = key i j H)
    (hl : leftSet G i j = leftSet H i j) (ho : Outside i j w) :
    G.Adj i w ↔ H.Adj i w := by
  classical
  have hc := key_count h w
  have hm : w ∈ leftSet G i j ↔ w ∈ leftSet H i j := by rw [hl]
  simp only [mem_leftSet] at hm
  by_cases gi : G.Adj i w <;> by_cases gj : G.Adj j w <;>
    by_cases hi : H.Adj i w <;> by_cases hj : H.Adj j w <;>
    simp_all [edgeBit]

theorem key_right_adj {i j w : V} {G H : SimpleGraph V}
    (h : key i j G = key i j H)
    (hl : leftSet G i j = leftSet H i j) (ho : Outside i j w) :
    G.Adj j w ↔ H.Adj j w := by
  classical
  have hc := key_count h w
  have hm := key_left_adj h hl ho
  by_cases gi : G.Adj i w <;> by_cases gj : G.Adj j w <;>
    by_cases hi : H.Adj i w <;> by_cases hj : H.Adj j w <;>
    simp_all [edgeBit]

theorem graph_eq_of_key_leftSet_eq {i j : V} {G H : SimpleGraph V}
    (h : key i j G = key i j H)
    (hl : leftSet G i j = leftSet H i j) : G = H := by
  classical
  ext u v
  by_cases ui : u = i
  · subst u
    by_cases vi : v = i
    · subst v; simp
    by_cases vj : v = j
    · subst v; exact key_internal h
    exact key_left_adj h hl ⟨vi, vj⟩
  by_cases uj : u = j
  · subst u
    by_cases vi : v = i
    · subst v; simpa only [G.adj_comm, H.adj_comm] using key_internal h
    by_cases vj : v = j
    · subst v; simp
    exact key_right_adj h hl ⟨vi, vj⟩
  by_cases vi : v = i
  · subst v
    simpa only [G.adj_comm, H.adj_comm] using key_left_adj h hl (show Outside i j u from ⟨ui, uj⟩)
  by_cases vj : v = j
  · subst v
    simpa only [G.adj_comm, H.adj_comm] using key_right_adj h hl (show Outside i j u from ⟨ui, uj⟩)
  exact key_outside h ⟨ui, uj⟩ ⟨vi, vj⟩

include sectionFintypeV in
theorem key_swap (G : SimpleGraph V) (i j : V) : key i j G = key j i G := by
  have retainedsectionFintypeV := sectionFintypeV
  apply Prod.ext
  · funext u v
    apply propext
    dsimp [key, Outside]
    tauto
  · apply Prod.ext
    · exact propext (G.adj_comm i j)
    · funext w
      exact Nat.add_comm _ _

def assemble (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (A B : Finset V)
    (hA : ∀ w ∈ A, Outside i j w)
    (hB : ∀ w ∈ B, Outside i j w) : SimpleGraph V where
  Adj u v :=
    (Outside i j u ∧ Outside i j v ∧ G.Adj u v) ∨
    (((u = i ∧ v = j) ∨ (u = j ∧ v = i)) ∧ G.Adj i j) ∨
    (u = i ∧ v ∈ A) ∨ (v = i ∧ u ∈ A) ∨
    (u = j ∧ v ∈ B) ∨ (v = j ∧ u ∈ B)
  symm := by
    constructor
    intro u v h
    rcases h with h | h | h | h | h | h
    · exact Or.inl ⟨h.2.1, h.1, G.symm.symm u v h.2.2⟩
    · exact Or.inr (Or.inl ⟨by tauto, h.2⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, h.2⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨h.1, h.2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1, h.2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, h.2⟩))))
  loopless := by
    constructor
    intro v h
    rcases h with h | h | h | h | h | h
    · exact G.irrefl h.2.2
    · rcases h.1 with ⟨hi, hj⟩ | ⟨hj, hi⟩ <;> exact hij (hi.symm.trans hj)
    · exact (hA v h.2).1 h.1
    · exact (hA v h.2).1 h.1
    · exact (hB v h.2).2 h.1
    · exact (hB v h.2).2 h.1

include sectionFintypeV in
theorem assemble_adj_left (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (A B : Finset V) (hA : ∀ w ∈ A, Outside i j w)
    (hB : ∀ w ∈ B, Outside i j w) {w : V} (hw : Outside i j w) :
    (assemble G i j hij A B hA hB).Adj i w ↔ w ∈ A := by
  have retainedsectionFintypeV := sectionFintypeV
  simp [assemble, Outside, hij, hw.1, hw.2]

include sectionFintypeV in
theorem assemble_adj_right (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (A B : Finset V) (hA : ∀ w ∈ A, Outside i j w)
    (hB : ∀ w ∈ B, Outside i j w) {w : V} (hw : Outside i j w) :
    (assemble G i j hij A B hA hB).Adj j w ↔ w ∈ B := by
  have retainedsectionFintypeV := sectionFintypeV
  simp [assemble, Outside, Ne.symm hij, hw.1, hw.2]

include sectionFintypeV in
theorem assemble_adj_internal (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (A B : Finset V) (hA : ∀ w ∈ A, Outside i j w)
    (hB : ∀ w ∈ B, Outside i j w) :
    (assemble G i j hij A B hA hB).Adj i j ↔ G.Adj i j := by
  have retainedsectionFintypeV := sectionFintypeV
  have hja : j ∉ A := fun h => (hA j h).2 rfl
  have hib : i ∉ B := fun h => (hB i h).1 rfl
  simp [assemble, Outside, hij, Ne.symm hij, hja, hib]

include sectionFintypeV in
theorem assemble_adj_outside (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (A B : Finset V) (hA : ∀ w ∈ A, Outside i j w)
    (hB : ∀ w ∈ B, Outside i j w) {u v : V}
    (hu : Outside i j u) (hv : Outside i j v) :
    (assemble G i j hij A B hA hB).Adj u v ↔ G.Adj u v := by
  have retainedsectionFintypeV := sectionFintypeV
  simp [assemble, hu, hv, hu.1, hu.2, hv.1, hv.2]

def trade (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (T : Finset V) (hT : T ⊆ singletonSet G i j) : SimpleGraph V := by
  classical
  refine assemble G i j hij (commonSet G i j ∪ T)
    (commonSet G i j ∪ (singletonSet G i j \ T)) ?_ ?_
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact ((mem_commonSet G i j w).mp hw).1
    · exact ((mem_singletonSet G i j w).mp (hT hw)).1
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact ((mem_commonSet G i j w).mp hw).1
    · exact ((mem_singletonSet G i j w).mp (Finset.mem_sdiff.mp hw).1).1

theorem trade_adj_left (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (T : Finset V) (hT : T ⊆ singletonSet G i j)
    {w : V} (hw : Outside i j w) :
    (trade G i j hij T hT).Adj i w ↔ (G.Adj i w ∧ G.Adj j w) ∨ w ∈ T := by
  classical
  unfold trade
  rw [assemble_adj_left _ _ _ _ _ _ _ _ hw]
  simp [hw]

theorem trade_adj_right (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (T : Finset V) (hT : T ⊆ singletonSet G i j)
    {w : V} (hw : Outside i j w) :
    (trade G i j hij T hT).Adj j w ↔
      (G.Adj i w ∧ G.Adj j w) ∨ (Xor (G.Adj i w) (G.Adj j w) ∧ w ∉ T) := by
  classical
  unfold trade
  rw [assemble_adj_right _ _ _ _ _ _ _ _ hw]
  simp [hw]

theorem trade_adj_internal (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (T : Finset V) (hT : T ⊆ singletonSet G i j) :
    (trade G i j hij T hT).Adj i j ↔ G.Adj i j := by
  unfold trade
  exact assemble_adj_internal _ _ _ _ _ _ _ _

theorem trade_adj_outside (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (T : Finset V) (hT : T ⊆ singletonSet G i j)
    {u v : V} (hu : Outside i j u) (hv : Outside i j v) :
    (trade G i j hij T hT).Adj u v ↔ G.Adj u v := by
  unfold trade
  exact assemble_adj_outside _ _ _ _ _ _ _ _ hu hv

include sectionFintypeV in
theorem key_eq_of {i j : V} {G H : SimpleGraph V}
    (ho : ∀ u v, Outside i j u → Outside i j v → (G.Adj u v ↔ H.Adj u v))
    (hi : G.Adj i j ↔ H.Adj i j)
    (hc : ∀ w, edgeBit G i w + edgeBit G j w = edgeBit H i w + edgeBit H j w) :
    key i j G = key i j H := by
  have retainedsectionFintypeV := sectionFintypeV
  apply Prod.ext
  · funext u v
    apply propext
    change (Outside i j u ∧ Outside i j v ∧ G.Adj u v) ↔
      (Outside i j u ∧ Outside i j v ∧ H.Adj u v)
    constructor
    · intro h; exact ⟨h.1, h.2.1, (ho u v h.1 h.2.1).mp h.2.2⟩
    · intro h; exact ⟨h.1, h.2.1, (ho u v h.1 h.2.1).mpr h.2.2⟩
  · exact Prod.ext (propext hi) (funext hc)

theorem key_trade (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (T : Finset V) (hT : T ⊆ singletonSet G i j) :
    key i j (trade G i j hij T hT) = key i j G := by
  classical
  apply key_eq_of
  · intro u v hu hv
    exact trade_adj_outside G i j hij T hT hu hv
  · exact trade_adj_internal G i j hij T hT
  · intro w
    by_cases wi : w = i
    · subst w
      have hi := trade_adj_internal G i j hij T hT
      simp only [edgeBit, SimpleGraph.irrefl, ↓reduceIte, zero_add]
      rw [(trade G i j hij T hT).adj_comm, G.adj_comm, hi]
    by_cases wj : w = j
    · subst w
      have hi := trade_adj_internal G i j hij T hT
      simp [edgeBit, hi]
    have ho : Outside i j w := ⟨wi, wj⟩
    have hl := trade_adj_left G i j hij T hT ho
    have hr := trade_adj_right G i j hij T hT ho
    have ht : w ∈ T → Xor (G.Adj i w) (G.Adj j w) :=
      fun hw => ((mem_singletonSet G i j w).mp (hT hw)).2
    simp only [edgeBit, hl, hr]
    by_cases gi : G.Adj i w <;> by_cases gj : G.Adj j w <;>
      by_cases wt : w ∈ T <;> simp_all [Xor]

theorem leftSet_trade (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (T : Finset V) (hT : T ⊆ singletonSet G i j) :
    leftSet (trade G i j hij T hT) i j = T := by
  classical
  ext w
  by_cases ho : Outside i j w
  · have hl := trade_adj_left G i j hij T hT ho
    have hr := trade_adj_right G i j hij T hT ho
    have ht : w ∈ T → Xor (G.Adj i w) (G.Adj j w) :=
      fun hw => ((mem_singletonSet G i j w).mp (hT hw)).2
    simp only [mem_leftSet, ho, true_and, hl, hr]
    by_cases gi : G.Adj i w <;> by_cases gj : G.Adj j w <;>
      by_cases wt : w ∈ T <;> simp_all [Xor]
  · have ht : w ∉ T := fun hw => ho ((mem_singletonSet G i j w).mp (hT hw)).1
    simp [ho, ht]

end Problem315.PairFiber

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairFiber.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairFiberDegree.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace Problem315.PairFiber

theorem edgeBit_symm {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u v : V) : edgeBit G u v = edgeBit G v u := by
  unfold edgeBit
  congr 1
  exact propext (G.adj_comm u v)

theorem graphDegree_eq_sum_edgeBit {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) :
    graphDegree G u = ∑ w, edgeBit G u w := by
  classical
  simp [graphDegree, edgeBit]

theorem degree_left_formula {n : ℕ} (G : SimpleGraph (Fin n))
    {i j : Fin n} (hij : i ≠ j) :
    graphDegree G i = edgeBit G i j + (commonSet G i j).card + (leftSet G i j).card := by
  classical
  have hp (w : Fin n) : edgeBit G i w =
      (if w = j then edgeBit G i j else 0) +
      (if w ∈ commonSet G i j then 1 else 0) +
      (if w ∈ leftSet G i j then 1 else 0) := by
    by_cases hwi : w = i
    · subst w
      simp [edgeBit, Outside, hij]
    by_cases hwj : w = j
    · subst w
      simp [edgeBit, Outside, Ne.symm hij]
    by_cases hiw : G.Adj i w <;> by_cases hjw : G.Adj j w <;>
      simp [edgeBit, Outside, hwi, hwj, hiw, hjw]
  rw [graphDegree_eq_sum_edgeBit]
  calc
    (∑ w, edgeBit G i w) = ∑ w, ((if w = j then edgeBit G i j else 0) +
      (if w ∈ commonSet G i j then 1 else 0) +
      (if w ∈ leftSet G i j then 1 else 0)) :=
        Finset.sum_congr rfl (fun w _ => hp w)
    _ = _ := by simp [Finset.sum_add_distrib, commonSet, leftSet]

theorem leftSet_card_eq_iff_degree_eq {n : ℕ} {G H : SimpleGraph (Fin n)}
    {i j : Fin n} (hij : i ≠ j) (hk : key i j G = key i j H) :
    (leftSet G i j).card = (leftSet H i j).card ↔ graphDegree G i = graphDegree H i := by
  have hi : edgeBit G i j = edgeBit H i j := by
    unfold edgeBit
    congr 1
    exact propext (key_internal hk)
  have hc := commonSet_eq_of_key_eq hk
  rw [degree_left_formula G hij, degree_left_formula H hij, hi, hc]
  omega

theorem singleton_card_split {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) :
    (singletonSet G i j).card = (leftSet G i j).card + (leftSet G j i).card := by
  classical
  have hu : singletonSet G i j = leftSet G i j ∪ leftSet G j i := by
    ext w
    simp only [mem_singletonSet, Finset.mem_union, mem_leftSet, Outside, Xor]
    tauto
  have hd : Disjoint (leftSet G i j) (leftSet G j i) := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    exact ((mem_leftSet G i j w).mp hw).2.2 ((mem_leftSet G j i w).mp hw').2.1
  rw [hu, Finset.card_union_of_disjoint hd]

theorem degree_outside_formula {n : ℕ} (G : SimpleGraph (Fin n))
    {i j : Fin n} (hij : i ≠ j) (w : Fin n) :
    graphDegree G w = edgeBit G w i + edgeBit G w j +
      ∑ x ∈ Finset.univ.filter (Outside i j), edgeBit G w x := by
  classical
  have hp (x : Fin n) : edgeBit G w x =
      (if x = i then edgeBit G w i else 0) +
      (if x = j then edgeBit G w j else 0) +
      (if Outside i j x then edgeBit G w x else 0) := by
    by_cases hxi : x = i
    · subst x
      simp [Outside, hij]
    by_cases hxj : x = j
    · subst x
      simp [Outside, Ne.symm hij]
    simp [Outside, hxi, hxj]
  rw [graphDegree_eq_sum_edgeBit]
  calc
    (∑ x, edgeBit G w x) =
        ∑ x, ((if x = i then edgeBit G w i else 0) +
          (if x = j then edgeBit G w j else 0) +
          (if Outside i j x then edgeBit G w x else 0)) :=
      Finset.sum_congr rfl (fun x _ => hp x)
    _ = _ := by simp [Finset.sum_filter, Finset.sum_add_distrib]

theorem degree_outside_eq_of_key_eq {n : ℕ} {G H : SimpleGraph (Fin n)}
    {i j w : Fin n} (hij : i ≠ j) (hk : key i j G = key i j H)
    (hw : Outside i j w) : graphDegree G w = graphDegree H w := by
  classical
  have hc := key_count hk w
  have hc' : edgeBit G w i + edgeBit G w j = edgeBit H w i + edgeBit H w j := by
    simpa only [edgeBit_symm G i w, edgeBit_symm G j w,
      edgeBit_symm H i w, edgeBit_symm H j w] using hc
  rw [degree_outside_formula G hij w, degree_outside_formula H hij w, hc']
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  have hxo := (Finset.mem_filter.mp hx).2
  unfold edgeBit
  congr 1
  exact propext (key_outside hk hw hxo)

theorem degrees_eq_of_key_leftSet_card_eq {n : ℕ} {G H : SimpleGraph (Fin n)}
    {i j : Fin n} (hij : i ≠ j) (hk : key i j G = key i j H)
    (hl : (leftSet G i j).card = (leftSet H i j).card) :
    ∀ v, graphDegree G v = graphDegree H v := by
  have hi := (leftSet_card_eq_iff_degree_eq hij hk).mp hl
  have hs := congrArg Finset.card (singletonSet_eq_of_key_eq hk)
  have hr : (leftSet G j i).card = (leftSet H j i).card := by
    rw [singleton_card_split G i j, singleton_card_split H i j, hl] at hs
    omega
  have hks : key j i G = key j i H :=
    (key_swap G i j).symm.trans (hk.trans (key_swap H i j))
  have hj := (leftSet_card_eq_iff_degree_eq (Ne.symm hij) hks).mp hr
  intro v
  by_cases hvi : v = i
  · simpa [hvi] using hi
  by_cases hvj : v = j
  · simpa [hvj] using hj
  exact degree_outside_eq_of_key_eq hij hk ⟨hvi, hvj⟩

end Problem315.PairFiber

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairFiberDegree.lean -/
