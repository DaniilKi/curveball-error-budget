import AnalyticDisjointEncoding

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/CrossCellMoments.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.CrossCellMoments

attribute [local instance] Classical.propDecidable

variable {α β : Type*} [sectionFintypeα : Fintype α] [sectionFintypeβ : Fintype β]

abbrev Cell (s : ℕ) (r : α → Fin 3) (c : β → Fin 3) :=
  {z : CrossBlock.Matrix × α × β //
    CrossBlock.total z.1 = s ∧ CrossBlock.row z.1 0 = (r z.2.1).val ∧
      CrossBlock.col z.1 0 = (c z.2.2).val}

instance cellFintype (s : ℕ) (r : α → Fin 3) (c : β → Fin 3) :
    Fintype (Cell s r c) := Fintype.ofFinite _

theorem sum_cell (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (F : α → β → ℝ) :
    (∑ z : Cell s r c, F z.val.2.1 z.val.2.2) =
      ∑ x, ∑ y, (CrossBlock.count s (r x) (c y) : ℝ) * F x y := by
  classical
  rw [← Finset.sum_subtype
    (Finset.univ.filter (fun z : CrossBlock.Matrix × α × β =>
      CrossBlock.total z.1 = s ∧ CrossBlock.row z.1 0 = (r z.2.1).val ∧
        CrossBlock.col z.1 0 = (c z.2.2).val))
    (by intro z; simp)
    (fun z : CrossBlock.Matrix × α × β => F z.2.1 z.2.2)]
  rw [Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.sum_filter]
  simp [CrossBlock.count]

def offCenter (r : α → Fin 3) (x : α) : ℝ := if r x = 1 then 0 else 1

omit [Fintype α] in
theorem offCenter_boolean (r : α → Fin 3) (x : α) :
    offCenter r x = 0 ∨ offCenter r x = 1 := by
  unfold offCenter
  split_ifs <;> simp

theorem sum_cell_two_product (r : α → Fin 3) (c : β → Fin 3)
    (f : α → ℝ) (g : β → ℝ) :
    (∑ z : Cell 2 r c, f z.val.2.1 * g z.val.2.2) =
      CrossCovariance.jointMoment (fun _ : α => 1) (fun _ : β => 1)
        (offCenter r) (offCenter c) f g := by
  rw [sum_cell 2 r c (fun x y => f x * g y)]
  unfold CrossCovariance.jointMoment
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [CrossBlock.count_two_real]
  simp only [offCenter, one_mul, mul_assoc]

theorem card_cell_two (r : α → Fin 3) (c : β → Fin 3) :
    (Fintype.card (Cell 2 r c) : ℝ) =
      CrossCovariance.mass (fun _ : α => 1) (fun _ : β => 1)
        (offCenter r) (offCenter c) := by
  simpa only [CrossCovariance.mass, one_mul, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one] using
    sum_cell_two_product r c (fun _ => 1) (fun _ => 1)

def average (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (F : α → β → ℝ) : ℝ :=
  (∑ z : Cell s r c, F z.val.2.1 z.val.2.2) / Fintype.card (Cell s r c)

theorem average_product_eq (r : α → Fin 3) (c : β → Fin 3)
    (f : α → ℝ) (g : β → ℝ) :
    average 2 r c (fun x y => f x * g y) =
      CrossCovariance.jointAverage (fun _ : α => 1) (fun _ : β => 1)
        (offCenter r) (offCenter c) f g := by
  unfold average CrossCovariance.jointAverage
  rw [sum_cell_two_product, card_cell_two]

theorem average_offCenter_product (r : α → Fin 3) (c : β → Fin 3) :
    average 2 r c (fun x y => offCenter r x * offCenter c y) = 0 := by
  rw [average_product_eq]
  unfold CrossCovariance.jointAverage
  rw [CrossCovariance.offCenter_jointMoment_zero _ _ _ _
    (offCenter_boolean r) (offCenter_boolean c), zero_div]

theorem sum_first_fiber (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (x : α) (g : β → ℝ) :
    (∑ z : Cell s r c, if z.val.2.1 = x then g z.val.2.2 else 0) =
      ∑ y, (CrossBlock.count s (r x) (c y) : ℝ) * g y := by
  classical
  rw [sum_cell s r c (fun u y => if u = x then g y else 0)]
  simp only [mul_ite, mul_zero]
  simp

def conditionalRight (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (x : α) (g : β → ℝ) : ℝ := by
  classical
  exact (∑ z ∈ (Finset.univ : Finset (Cell s r c)).filter
    (fun z => z.val.2.1 = x), g z.val.2.2) /
      ((Finset.univ : Finset (Cell s r c)).filter
        (fun z => z.val.2.1 = x)).card

theorem conditionalRight_eq_table (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (x : α) (g : β → ℝ) :
    conditionalRight s r c x g =
      (∑ y, (CrossBlock.count s (r x) (c y) : ℝ) * g y) /
        (∑ y, (CrossBlock.count s (r x) (c y) : ℝ)) := by
  classical
  unfold conditionalRight
  rw [Finset.sum_filter, sum_first_fiber]
  congr 1
  have h := sum_first_fiber s r c x (fun _ => 1)
  simpa only [Finset.sum_boole, mul_one] using h

theorem conditionalRight_two (r : α → Fin 3) (c : β → Fin 3)
    (x : α) (g : β → ℝ) :
    conditionalRight 2 r c x g =
      CrossCovariance.rightSliceAverage (fun _ : β => 1)
        (offCenter c) (offCenter r x) g := by
  rw [conditionalRight_eq_table]
  unfold CrossCovariance.rightSliceAverage
  simp only [CrossBlock.count_two_real, offCenter, one_mul]

theorem conditionalRight_two_span (r : α → Fin 3) (c : β → Fin 3)
    (g : β → ℝ) :
    ∃ A B : ℝ, ∀ x, conditionalRight 2 r c x g = A + B * offCenter r x := by
  refine ⟨CrossCovariance.rightSliceAverage (fun _ : β => 1) (offCenter c) 0 g,
    CrossCovariance.rightSliceAverage (fun _ : β => 1) (offCenter c) 1 g -
      CrossCovariance.rightSliceAverage (fun _ : β => 1) (offCenter c) 0 g, ?_⟩
  intro x
  rw [conditionalRight_two]
  exact CrossCovariance.rightSliceAverage_span _ _ _ (offCenter_boolean r) g x

theorem covariance_rank_one (r : α → Fin 3) (c : β → Fin 3)
    (f : α → ℝ) (g : β → ℝ) :
    average 2 r c (fun x y => f x * g y) -
        average 2 r c (fun x _ => f x) * average 2 r c (fun _ y => g y) =
      - ((Fintype.card α : ℝ) * (∑ x, offCenter r x * f x) -
          (∑ x, offCenter r x) * (∑ x, f x)) *
        ((Fintype.card β : ℝ) * (∑ y, offCenter c y * g y) -
          (∑ y, offCenter c y) * (∑ y, g y)) /
        (Fintype.card (Cell 2 r c) : ℝ) ^ 2 := by
  have hleft := average_product_eq r c f (fun _ => 1)
  have hright := average_product_eq r c (fun _ => 1) g
  simp only [mul_one] at hleft
  simp only [one_mul] at hright
  rw [average_product_eq, hleft, hright, card_cell_two]
  simpa only [one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
    CrossCovariance.covariance_rank_one (fun _ : α => 1) (fun _ : β => 1)
      (offCenter r) (offCenter c) f g

theorem sum_second_fiber (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (y : β) (f : α → ℝ) :
    (∑ z : Cell s r c, if z.val.2.2 = y then f z.val.2.1 else 0) =
      ∑ x, (CrossBlock.count s (r x) (c y) : ℝ) * f x := by
  classical
  rw [sum_cell s r c (fun x v => if v = y then f x else 0)]
  simp only [mul_ite, mul_zero]
  simp

def conditionalLeft (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (y : β) (f : α → ℝ) : ℝ := by
  classical
  exact (∑ z ∈ (Finset.univ : Finset (Cell s r c)).filter
    (fun z => z.val.2.2 = y), f z.val.2.1) /
      ((Finset.univ : Finset (Cell s r c)).filter
        (fun z => z.val.2.2 = y)).card

theorem conditionalLeft_eq_table (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (y : β) (f : α → ℝ) :
    conditionalLeft s r c y f =
      (∑ x, (CrossBlock.count s (r x) (c y) : ℝ) * f x) /
        (∑ x, (CrossBlock.count s (r x) (c y) : ℝ)) := by
  classical
  unfold conditionalLeft
  rw [Finset.sum_filter, sum_second_fiber]
  congr 1
  have h := sum_second_fiber s r c y (fun _ => 1)
  simpa only [Finset.sum_boole, mul_one] using h

theorem conditionalLeft_two (r : α → Fin 3) (c : β → Fin 3)
    (y : β) (f : α → ℝ) :
    conditionalLeft 2 r c y f =
      CrossCovariance.rightSliceAverage (fun _ : α => 1)
        (offCenter r) (offCenter c y) f := by
  rw [conditionalLeft_eq_table]
  unfold CrossCovariance.rightSliceAverage
  congr 1
  · apply Finset.sum_congr rfl
    intro x _
    rw [CrossBlock.count_two_real]
    simp only [offCenter, one_mul]
    ring
  · apply Finset.sum_congr rfl
    intro x _
    rw [CrossBlock.count_two_real]
    simp only [offCenter, one_mul]
    ring

theorem conditionalLeft_two_span (r : α → Fin 3) (c : β → Fin 3)
    (f : α → ℝ) :
    ∃ A B : ℝ, ∀ y, conditionalLeft 2 r c y f = A + B * offCenter c y := by
  refine ⟨CrossCovariance.rightSliceAverage (fun _ : α => 1) (offCenter r) 0 f,
    CrossCovariance.rightSliceAverage (fun _ : α => 1) (offCenter r) 1 f -
      CrossCovariance.rightSliceAverage (fun _ : α => 1) (offCenter r) 0 f, ?_⟩
  intro y
  rw [conditionalLeft_two]
  exact CrossCovariance.rightSliceAverage_span _ _ _ (offCenter_boolean c) f y

include sectionFintypeα sectionFintypeβ in
theorem offCenter_disjoint (r : α → Fin 3) (c : β → Fin 3)
    (z : Cell 2 r c) (hr : r z.val.2.1 ≠ 1) : c z.val.2.2 = 1 := by
  have retainedsectionFintypeα := sectionFintypeα
  have retainedsectionFintypeβ := sectionFintypeβ
  apply Fin.ext
  have hrow : CrossBlock.row z.val.1 0 ≠ 1 := by
    intro h
    apply hr
    apply Fin.ext
    exact z.property.2.1.symm.trans h
  exact z.property.2.2.symm.trans
    (CrossBlock.off_center_disjoint z.val.1 z.property.1 hrow)

theorem offCenter_disjoint_symm (r : α → Fin 3) (c : β → Fin 3)
    (z : Cell 2 r c) (hc : c z.val.2.2 ≠ 1) : r z.val.2.1 = 1 := by
  by_contra hr
  exact hc (offCenter_disjoint r c z hr)

theorem exists_center_of_both_offCenter (r : α → Fin 3) (c : β → Fin 3)
    (hrow : ∃ z : Cell 2 r c, r z.val.2.1 ≠ 1)
    (hcol : ∃ z : Cell 2 r c, c z.val.2.2 ≠ 1) :
    ∃ z : Cell 2 r c, r z.val.2.1 = 1 ∧ c z.val.2.2 = 1 := by
  obtain ⟨u, hu⟩ := hrow
  obtain ⟨v, hv⟩ := hcol
  have hr := offCenter_disjoint_symm r c v hv
  have hc := offCenter_disjoint r c u hu
  let M : CrossBlock.Matrix := fun i j => decide (i = j)
  have hM : CrossBlock.total M = 2 ∧ CrossBlock.row M 0 = 1 ∧
      CrossBlock.col M 0 = 1 := by decide
  refine ⟨⟨(M, v.val.2.1, u.val.2.2), hM.1, ?_, ?_⟩, hr, hc⟩
  · simpa only [hr, Fin.val_one] using hM.2.1
  · simpa only [hc, Fin.val_one] using hM.2.2

end Problem315.CrossCellMoments

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/CrossCellMoments.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/DisjointCrossCellEquiv.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.DisjointMarginal
attribute [local instance] Classical.propDecidable
open DisjointEncoding

variable {V : Type*} [Fintype V]

def jointCrossEquiv (e : Fin 4 ↪ V) (G : SimpleGraph V) :
    JointData e G ≃ CrossCellMoments.Cell (CrossBlock.total (crossCode e G))
      (fun x : LeftData e G => x.val.1) (fun y : RightData e G => y.val.1) where
  toFun z := ⟨(z.2.2.val, z.1, z.2.1), z.2.2.property⟩
  invFun z := ⟨z.val.2.1, z.val.2.2, z.val.1, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def degreeCellCrossEquiv (e : Fin 4 ↪ V) (G : SimpleGraph V) :
    DegreeCell e G ≃ CrossCellMoments.Cell (CrossBlock.total (crossCode e G))
      (fun x : LeftData e G => x.val.1) (fun y : RightData e G => y.val.1) :=
  (degreeCellJointEquiv e G).trans (jointCrossEquiv e G)

variable {n : Nat} {d : Fin n → Nat}

abbrev CrossCell (e : Fin 4 ↪ Fin n) (G : GraphState n d) :=
  CrossCellMoments.Cell (CrossBlock.total (crossCode e G.val))
    (fun x : LeftData e G.val => x.val.1) (fun y : RightData e G.val => y.val.1)

def stateCellCrossEquiv (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    StateCell e G ≃ CrossCell e G :=
  (stateCellJointEquiv e G).trans (jointCrossEquiv e G.val)

@[simp] theorem stateCellCrossEquiv_left (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    (stateCellCrossEquiv e G H).val.2.1 = stateLeftData e G H := rfl

@[simp] theorem stateCellCrossEquiv_right (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    (stateCellCrossEquiv e G H).val.2.2 = stateRightData e G H := rfl

@[simp] theorem stateCellCrossEquiv_matrix (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    (stateCellCrossEquiv e G H).val.1 = crossCode e H.val.val := rfl

theorem sameFiber_left_iff_crossCell_right (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H K : StateCell e G) :
    PairResampling.SameFiber {e 0, e 1} H.val.val K.val.val ↔
      (stateCellCrossEquiv e G H).val.2.2 = (stateCellCrossEquiv e G K).val.2.2 :=
  sameFiber_left_iff_stateRightData_eq e G H K

theorem sameFiber_right_iff_crossCell_left (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H K : StateCell e G) :
    PairResampling.SameFiber {e 2, e 3} H.val.val K.val.val ↔
      (stateCellCrossEquiv e G H).val.2.1 = (stateCellCrossEquiv e G K).val.2.1 :=
  sameFiber_right_iff_stateLeftData_eq e G H K

end Problem315.DisjointMarginal

namespace Problem315.PairFibers
attribute [local instance] Classical.propDecidable

theorem expectation_ker_pullback {α β ι : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (key : β → ι) (f : EuclideanSpace ℝ β) (x : α) :
    expectation (Setoid.ker (key ∘ e)) (WithLp.toLp 2 (fun y => f (e y))) x =
      expectation (Setoid.ker key) f (e x) := by
  classical
  have hcell : (cell (Setoid.ker (key ∘ e)) x).map e.toEmbedding =
      cell (Setoid.ker key) (e x) := by
    ext y
    simp only [Finset.mem_map, mem_cell, Setoid.ker_def, Function.comp_apply,
      Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨e.symm y, by simpa using hy, by simp⟩
  have hcard := congrArg Finset.card hcell
  rw [Finset.card_map] at hcard
  rw [expectation_apply, expectation_apply, hcard]
  congr 1
  rw [← hcell, Finset.sum_map]
  rfl

end Problem315.PairFibers

namespace Problem315.DisjointMarginal
attribute [local instance] Classical.propDecidable
open DisjointEncoding
variable {n : Nat} {d : Fin n → Nat}

theorem expectation_stateLeftData_crossCell (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (f : EuclideanSpace ℝ (CrossCell e G)) (H : StateCell e G) :
    PairFibers.expectation (Setoid.ker (stateLeftData e G))
      (WithLp.toLp 2 (fun K => f (stateCellCrossEquiv e G K))) H =
      PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.1))
        f (stateCellCrossEquiv e G H) :=
by
  have h := PairFibers.expectation_ker_pullback (stateCellCrossEquiv e G)
    (fun z : CrossCell e G => z.val.2.1) f H
  simpa only [Function.comp_def, stateCellCrossEquiv_left] using h

theorem expectation_stateRightData_crossCell (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (f : EuclideanSpace ℝ (CrossCell e G)) (H : StateCell e G) :
    PairFibers.expectation (Setoid.ker (stateRightData e G))
      (WithLp.toLp 2 (fun K => f (stateCellCrossEquiv e G K))) H =
      PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.2))
        f (stateCellCrossEquiv e G H) :=
by
  have h := PairFibers.expectation_ker_pullback (stateCellCrossEquiv e G)
    (fun z : CrossCell e G => z.val.2.2) f H
  simpa only [Function.comp_def, stateCellCrossEquiv_right] using h

end Problem315.DisjointMarginal

namespace Problem315.PairResampling
attribute [local instance] Classical.propDecidable
variable {n : Nat} {d : Fin n → Nat}

theorem expectation_eq_subtype_key {ι : Type*}
    (a : Finset (Fin n)) (C : GraphState n d → Prop) (key : {G // C G} → ι)
    (hclosed : ∀ (H : {G // C G}) (K : GraphState n d),
      SameFiber a H.val.val K.val → C K)
    (hkey : ∀ H K : {G // C G}, SameFiber a H.val.val K.val.val ↔ key H = key K)
    (f : StateSpace n d) (H : {G // C G}) :
    expectation n d a f H.val =
      PairFibers.expectation (Setoid.ker key) (WithLp.toLp 2 (fun K => f K.val)) H := by
  classical
  let emb : {G // C G} ↪ GraphState n d := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : (PairFibers.cell (Setoid.ker key) H).map emb = fiberStates a H.val := by
    ext K
    simp only [Finset.mem_map, PairFibers.mem_cell, Setoid.ker_def, mem_fiberStates]
    constructor
    · rintro ⟨L, hL, hLK⟩
      have hrel := (hkey H L).mpr hL
      change L.val = K at hLK
      simpa only [hLK] using hrel
    · intro hK
      refine ⟨⟨K, hclosed H K hK⟩, ?_, rfl⟩
      exact (hkey H ⟨K, hclosed H K hK⟩).mp hK
  rw [expectation_eq_average, PairFibers.expectation_apply, ← hmap,
    Finset.sum_map, Finset.card_map]
  rfl

end Problem315.PairResampling

namespace Problem315.DisjointMarginal
attribute [local instance] Classical.propDecidable
open DisjointEncoding
variable {n : Nat} {d : Fin n → Nat}

theorem expectation_leftPair_eq_stateRightData (e : Fin 4 ↪ Fin n)
    (G : GraphState n d) (f : PairResampling.StateSpace n d) (H : StateCell e G) :
    PairResampling.expectation n d {e 0, e 1} f H.val =
      PairFibers.expectation (Setoid.ker (stateRightData e G))
        (WithLp.toLp 2 (fun K => f K.val)) H := by
  exact PairResampling.expectation_eq_subtype_key {e 0, e 1}
    (fun K => SameCell e G.val K.val) (stateRightData e G)
    (stateCell_of_leftFiber e G) (sameFiber_left_iff_stateRightData_eq e G) f H

theorem expectation_rightPair_eq_stateLeftData (e : Fin 4 ↪ Fin n)
    (G : GraphState n d) (f : PairResampling.StateSpace n d) (H : StateCell e G) :
    PairResampling.expectation n d {e 2, e 3} f H.val =
      PairFibers.expectation (Setoid.ker (stateLeftData e G))
        (WithLp.toLp 2 (fun K => f K.val)) H := by
  exact PairResampling.expectation_eq_subtype_key {e 2, e 3}
    (fun K => SameCell e G.val K.val) (stateLeftData e G)
    (stateCell_of_rightFiber e G) (sameFiber_right_iff_stateLeftData_eq e G) f H

end Problem315.DisjointMarginal

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/DisjointCrossCellEquiv.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/DisjointEqualityFlags.lean -/
section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.DisjointMarginal
open DisjointEncoding
variable {n : Nat} {d : Fin n → Nat}

private theorem row_crossCode (e : Fin 4 ↪ Fin n) (H : SimpleGraph (Fin n)) (i : Fin 2) :
    CrossBlock.row (crossCode e H) i =
      edgeBit H (e (leftIndex i)) (e 2) + edgeBit H (e (leftIndex i)) (e 3) := by
  simp only [CrossBlock.row, Fin.sum_univ_two, CrossBlock.entry, crossCode,
    decide_eq_true_eq, edgeBit]
  rfl

private theorem col_crossCode (e : Fin 4 ↪ Fin n) (H : SimpleGraph (Fin n)) (j : Fin 2) :
    CrossBlock.col (crossCode e H) j =
      edgeBit H (e 0) (e (rightIndex j)) + edgeBit H (e 1) (e (rightIndex j)) := by
  simp only [CrossBlock.col, Fin.sum_univ_two, CrossBlock.entry, crossCode,
    decide_eq_true_eq, edgeBit]
  rfl

theorem equality_crossTotal_eq (e : Fin 4 ↪ Fin n) (H : GraphState n d) :
    PairEquality.crossTotal (e 0) (e 1) (e 2) (e 3) H =
      CrossBlock.total (crossCode e H.val) := by
  rw [CrossBlock.total_eq_row_add, row_crossCode, row_crossCode]
  change (PairFiber.edgeBit H.val (e 0) (e 2) + PairFiber.edgeBit H.val (e 1) (e 2)) +
      (PairFiber.edgeBit H.val (e 0) (e 3) + PairFiber.edgeBit H.val (e 1) (e 3)) =
    (edgeBit H.val (e 0) (e 2) + edgeBit H.val (e 0) (e 3)) +
      (edgeBit H.val (e 1) (e 2) + edgeBit H.val (e 1) (e 3))
  simp only [PairFiber.edgeBit, edgeBit]
  omega

theorem stateLeftData_margin (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    (stateLeftData e G H).val.1.val = CrossBlock.row (crossCode e H.val.val) 0 := rfl

theorem stateRightData_margin (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    (stateRightData e G H).val.1.val = CrossBlock.col (crossCode e H.val.val) 0 := rfl

theorem stateLeftFlag_eq_observable (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    flag (stateLeftData e G H).val.1 =
      PairEquality.observable (e 0) (e 2) (e 3) H.val := by
  have hmargin := stateLeftData_margin e G H
  have heq : (stateLeftData e G H).val.1 = 1 ↔
      CrossBlock.row (crossCode e H.val.val) 0 = 1 := by
    exact (Fin.ext_iff).trans (by rw [hmargin]; rfl)
  unfold flag
  simp only [heq]
  change (if CrossBlock.row (crossCode e H.val.val) 0 = 1 then (0 : ℝ) else 1) =
    if H.val.val.Adj (e 0) (e 2) ↔ H.val.val.Adj (e 0) (e 3) then 1 else 0
  rw [row_crossCode]
  change (if edgeBit H.val.val (e 0) (e 2) + edgeBit H.val.val (e 0) (e 3) = 1 then (0 : ℝ) else 1) = _
  by_cases h0 : H.val.val.Adj (e 0) (e 2) <;>
    by_cases h1 : H.val.val.Adj (e 0) (e 3) <;>
    simp [edgeBit, h0, h1]

theorem stateRightFlag_eq_observable (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    flag (stateRightData e G H).val.1 =
      PairEquality.observable (e 2) (e 0) (e 1) H.val := by
  have hmargin := stateRightData_margin e G H
  have heq : (stateRightData e G H).val.1 = 1 ↔
      CrossBlock.col (crossCode e H.val.val) 0 = 1 := by
    exact (Fin.ext_iff).trans (by rw [hmargin]; rfl)
  unfold flag
  simp only [heq]
  change (if CrossBlock.col (crossCode e H.val.val) 0 = 1 then (0 : ℝ) else 1) =
    if H.val.val.Adj (e 2) (e 0) ↔ H.val.val.Adj (e 2) (e 1) then 1 else 0
  have hc0 : H.val.val.Adj (e 2) (e 0) ↔ H.val.val.Adj (e 0) (e 2) :=
    H.val.val.adj_comm _ _
  have hc1 : H.val.val.Adj (e 2) (e 1) ↔ H.val.val.Adj (e 1) (e 2) :=
    H.val.val.adj_comm _ _
  rw [hc0,hc1]
  rw [col_crossCode]
  change (if edgeBit H.val.val (e 0) (e 2) + edgeBit H.val.val (e 1) (e 2) = 1 then (0 : ℝ) else 1) = _
  by_cases h0 : H.val.val.Adj (e 0) (e 2) <;>
    by_cases h1 : H.val.val.Adj (e 1) (e 2) <;>
    simp [edgeBit, h0, h1]

theorem stateCell_crossTotal_eq (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    CrossBlock.total (crossCode e H.val.val) = CrossBlock.total (crossCode e G.val) :=
  ((coordinate_degrees_iff e G.val
    (graphStateCellEquiv e G H).matrix (graphStateCellEquiv e G H).left
    (graphStateCellEquiv e G H).right (graphStateCellEquiv e G H).left_subset
    (graphStateCellEquiv e G H).right_subset).mp (graphStateCellEquiv e G H).degrees).1

theorem equality_crossTotal_on_cell (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    PairEquality.crossTotal (e 0) (e 1) (e 2) (e 3) H.val =
      CrossBlock.total (crossCode e G.val) := by
  rw [equality_crossTotal_eq, stateCell_crossTotal_eq]

theorem equality_crossTotal_reverse_eq (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    PairEquality.crossTotal (e 2) (e 3) (e 0) (e 1) G =
      CrossBlock.total (crossCode e G.val) := by
  rw [← equality_crossTotal_eq e G]
  unfold PairEquality.crossTotal PairFiber.edgeBit
  simp only [G.val.adj_comm (e 2) (e 0), G.val.adj_comm (e 3) (e 0),
    G.val.adj_comm (e 2) (e 1), G.val.adj_comm (e 3) (e 1)]
  omega

theorem equality_crossTotal_reverse_on_cell
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (H : StateCell e G) :
    PairEquality.crossTotal (e 2) (e 3) (e 0) (e 1) H.val =
      CrossBlock.total (crossCode e G.val) := by
  rw [equality_crossTotal_reverse_eq, stateCell_crossTotal_eq]

end Problem315.DisjointMarginal

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/DisjointEqualityFlags.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/CrossCellConditionalExpectation.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.CrossCellMoments

attribute [local instance] Classical.propDecidable
variable {α β : Type*} [Fintype α] [Fintype β]

def firstPartition (s : ℕ) (r : α → Fin 3) (c : β → Fin 3) : Setoid (Cell s r c) :=
  Setoid.ker (fun z => z.val.2.1)

def secondPartition (s : ℕ) (r : α → Fin 3) (c : β → Fin 3) : Setoid (Cell s r c) :=
  Setoid.ker (fun z => z.val.2.2)

theorem expectation_factors_key
    {Ω κ : Type*} [Fintype Ω] (key : Ω → κ) (f : EuclideanSpace ℝ Ω) :
    ∃ g : κ → ℝ, PairFibers.expectation (Setoid.ker key) f =
      WithLp.toLp 2 (fun z => g (key z)) := by
  have hf : Function.FactorsThrough
      (fun z => PairFibers.expectation (Setoid.ker key) f z) key := by
    intro x y hxy
    exact PairFibers.expectation_constant (Setoid.ker key) f hxy
  obtain ⟨g,hg⟩ := (Function.factorsThrough_iff _).mp hf
  refine ⟨g, ?_⟩
  ext z
  exact congrFun hg z

theorem expectation_first_right_apply (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (g : β → ℝ) (z : Cell s r c) :
    PairFibers.expectation (firstPartition s r c)
      (WithLp.toLp 2 (fun w : Cell s r c => g w.val.2.2)) z =
        conditionalRight s r c z.val.2.1 g := by
  rw [PairFibers.expectation_apply]
  have hcell : PairFibers.cell (firstPartition s r c) z =
      Finset.univ.filter (fun w : Cell s r c => w.val.2.1 = z.val.2.1) := by
    ext w
    simp only [PairFibers.mem_cell, Finset.mem_filter, Finset.mem_univ, true_and]
    change z.val.2.1 = w.val.2.1 ↔ w.val.2.1 = z.val.2.1
    exact eq_comm
  rw [hcell]
  rfl

theorem expectation_second_left_apply (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (g : α → ℝ) (z : Cell s r c) :
    PairFibers.expectation (secondPartition s r c)
      (WithLp.toLp 2 (fun w : Cell s r c => g w.val.2.1)) z =
        conditionalLeft s r c z.val.2.2 g := by
  rw [PairFibers.expectation_apply]
  have hcell : PairFibers.cell (secondPartition s r c) z =
      Finset.univ.filter (fun w : Cell s r c => w.val.2.2 = z.val.2.2) := by
    ext w
    simp only [PairFibers.mem_cell, Finset.mem_filter, Finset.mem_univ, true_and]
    change z.val.2.2 = w.val.2.2 ↔ w.val.2.2 = z.val.2.2
    exact eq_comm
  rw [hcell]
  rfl

end Problem315.CrossCellMoments

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/CrossCellConditionalExpectation.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/CrossIndependent.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.CrossBlock

def independentMargin (s : ℕ) (r : Fin 3) : ℝ :=
  match s with
  | 0 => if r = 0 then 1 else 0
  | 1 => if r ≤ 1 then 1 else 0
  | 3 => if 1 ≤ r then 1 else 0
  | 4 => if r = 2 then 1 else 0
  | _ => 0

theorem count_eq_independent_product (s : ℕ) (hs : s ≠ 2) (r c : Fin 3) :
    (count s r c : ℝ) = independentMargin s r * independentMargin s c := by
  by_cases hsmall : s ≤ 4
  · interval_cases s
    · rw [count_zero]
      simp only [independentMargin]
      split_ifs <;> simp_all
    · rw [count_one]
      simp only [independentMargin]
      split_ifs <;> simp_all
    · exact (hs rfl).elim
    · rw [count_three]
      simp only [independentMargin]
      split_ifs <;> simp_all
    · rw [count_four]
      simp only [independentMargin]
      split_ifs <;> simp_all
  · have hcount : count s r c = 0 := by
      unfold count
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro M hM
      have ht := (Finset.mem_filter.mp hM).2.1
      have hb := total_le_four M
      omega
    have hmargin (t : Fin 3) : independentMargin s t = 0 := by
      match s with
      | 0 | 1 | 2 | 3 | 4 => omega
      | k + 5 => rfl
    rw [hcount, hmargin, hmargin]
    norm_num

variable {α β : Type*} [Fintype α] [Fintype β]

def countMoment (s : ℕ) (a : α → ℝ) (b : β → ℝ)
    (r : α → Fin 3) (c : β → Fin 3) (f : α → ℝ) (g : β → ℝ) : ℝ :=
  ∑ x, ∑ y, a x * b y * (count s (r x) (c y) : ℝ) * f x * g y

def countAverage (s : ℕ) (a : α → ℝ) (b : β → ℝ)
    (r : α → Fin 3) (c : β → Fin 3) (f : α → ℝ) (g : β → ℝ) : ℝ :=
  countMoment s a b r c f g / countMoment s a b r c (fun _ => 1) (fun _ => 1)

theorem countMoment_factor (s : ℕ) (hs : s ≠ 2) (a : α → ℝ) (b : β → ℝ)
    (r : α → Fin 3) (c : β → Fin 3) (f : α → ℝ) (g : β → ℝ) :
    countMoment s a b r c f g =
      (∑ x, a x * independentMargin s (r x) * f x) *
        (∑ y, b y * independentMargin s (c y) * g y) := by
  unfold countMoment
  simp_rw [count_eq_independent_product s hs]
  calc
    _ = ∑ x, ∑ y, (a x * independentMargin s (r x) * f x) *
        (b y * independentMargin s (c y) * g y) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul]

theorem countAverage_independent (s : ℕ) (hs : s ≠ 2)
    (a : α → ℝ) (b : β → ℝ) (r : α → Fin 3) (c : β → Fin 3)
    (f : α → ℝ) (g : β → ℝ) :
    countAverage s a b r c f g =
      countAverage s a b r c f (fun _ => 1) *
        countAverage s a b r c (fun _ => 1) g := by
  unfold countAverage
  simp only [countMoment_factor s hs, mul_one]
  by_cases h : (∑ x, a x * independentMargin s (r x)) *
      (∑ y, b y * independentMargin s (c y)) = 0
  · simp [h]
  · field_simp

end Problem315.CrossBlock

namespace Problem315.CrossCovariance

variable {α β : Type*} [Fintype α] [Fintype β]

theorem independent_of_left_flag_constant
    (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (k : ℝ) (hk : ∀ x, a x ≠ 0 → p x = k)
    (f : α → ℝ) (g : β → ℝ) :
    jointAverage a b p q f g = jointAverage a b p q f (fun _ => 1) *
      jointAverage a b p q (fun _ => 1) g := by
  have hpf : (∑ x, a x * p x * f x) = k * ∑ x, a x * f x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : a x = 0
    · simp [hx]
    · rw [hk x hx]
      ring
  have hp : (∑ x, a x * p x) = k * ∑ x, a x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : a x = 0
    · simp [hx]
    · rw [hk x hx]
      ring
  have h := covariance_rank_one a b p q f g
  rw [hpf, hp] at h
  have hz : (∑ x, a x) * (k * ∑ x, a x * f x) -
      (k * ∑ x, a x) * (∑ x, a x * f x) = 0 := by ring
  rw [hz] at h
  simpa only [neg_zero, zero_mul, zero_div, sub_eq_zero] using h

theorem independent_of_right_flag_constant
    (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (k : ℝ) (hk : ∀ y, b y ≠ 0 → q y = k)
    (f : α → ℝ) (g : β → ℝ) :
    jointAverage a b p q f g = jointAverage a b p q f (fun _ => 1) *
      jointAverage a b p q (fun _ => 1) g := by
  have hqg : (∑ y, b y * q y * g y) = k * ∑ y, b y * g y := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : b y = 0
    · simp [hy]
    · rw [hk y hy]
      ring
  have hq : (∑ y, b y * q y) = k * ∑ y, b y := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : b y = 0
    · simp [hy]
    · rw [hk y hy]
      ring
  have h := covariance_rank_one a b p q f g
  rw [hqg, hq] at h
  have hz : (∑ y, b y) * (k * ∑ y, b y * g y) -
      (k * ∑ y, b y) * (∑ y, b y * g y) = 0 := by ring
  rw [hz] at h
  simpa only [mul_zero, zero_div, sub_eq_zero] using h

theorem independent_of_left_event_zero
    (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ y, 0 ≤ b y)
    (hp : ∀ x, p x = 0 ∨ p x = 1) (hq : ∀ y, q y = 0 ∨ q y = 1)
    (hprob : jointAverage a b p q p (fun _ => 1) = 0)
    (f : α → ℝ) (g : β → ℝ) :
    jointAverage a b p q f g = jointAverage a b p q f (fun _ => 1) *
      jointAverage a b p q (fun _ => 1) g := by
  by_cases hmass : mass a b p q = 0
  · simp [jointAverage, hmass]
  have hm : jointMoment a b p q p (fun _ => 1) = 0 :=
    (div_eq_zero_iff.mp hprob).resolve_right hmass
  have hnn (x : α) (y : β) :
      0 ≤ a x * b y * (2 - p x - q y) * p x * 1 := by
    have hax := ha x
    have hby := hb y
    rcases hp x with hx | hx <;> rcases hq y with hy | hy <;>
      simp only [hx, hy] <;> positivity
  have hterm (x : α) (y : β) :
      a x * b y * (2 - p x - q y) * p x * 1 = 0 := by
    have hx := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _ => Finset.sum_nonneg (fun y _ => hnn x y))).mp hm x (Finset.mem_univ x)
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hnn x y)).mp hx y
      (Finset.mem_univ y)
  by_cases hconst : ∀ x, a x ≠ 0 → p x = 0
  · exact independent_of_left_flag_constant a b p q 0 hconst f g
  · push Not at hconst
    obtain ⟨x, hax, hpx⟩ := hconst
    have hp1 : p x = 1 := (hp x).resolve_left hpx
    apply independent_of_right_flag_constant a b p q 1 _ f g
    intro y hby
    rcases hq y with hy | hy
    · have hz := hterm x y
      simp only [hp1, hy] at hz
      norm_num at hz
      exact (hz.elim hax hby).elim
    · exact hy

theorem jointMoment_swap (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (f : α → ℝ) (g : β → ℝ) :
    jointMoment a b p q f g = jointMoment b a q p g f := by
  unfold jointMoment
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem jointAverage_swap (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (f : α → ℝ) (g : β → ℝ) :
    jointAverage a b p q f g = jointAverage b a q p g f := by
  unfold jointAverage mass
  rw [jointMoment_swap a b p q f g,
    jointMoment_swap a b p q (fun _ => 1) (fun _ => 1)]

theorem independent_of_right_event_zero
    (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ y, 0 ≤ b y)
    (hp : ∀ x, p x = 0 ∨ p x = 1) (hq : ∀ y, q y = 0 ∨ q y = 1)
    (hprob : jointAverage a b p q (fun _ => 1) q = 0)
    (f : α → ℝ) (g : β → ℝ) :
    jointAverage a b p q f g = jointAverage a b p q f (fun _ => 1) *
      jointAverage a b p q (fun _ => 1) g := by
  rw [jointAverage_swap] at hprob
  have h := independent_of_left_event_zero b a q p hb ha hq hp hprob g f
  rw [jointAverage_swap b a q p g f,
    jointAverage_swap b a q p g (fun _ => 1),
    jointAverage_swap b a q p (fun _ => 1) f] at h
  simpa only [mul_comm] using h

theorem independent_of_center_zero
    (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ y, 0 ≤ b y)
    (hp : ∀ x, p x = 0 ∨ p x = 1) (hq : ∀ y, q y = 0 ∨ q y = 1)
    (hprob : jointAverage a b p q (fun x => 1 - p x) (fun y => 1 - q y) = 0)
    (f : α → ℝ) (g : β → ℝ) :
    jointAverage a b p q f g = jointAverage a b p q f (fun _ => 1) *
      jointAverage a b p q (fun _ => 1) g := by
  by_cases hmass : mass a b p q = 0
  · simp [jointAverage, hmass]
  have hm : jointMoment a b p q (fun x => 1 - p x) (fun y => 1 - q y) = 0 :=
    (div_eq_zero_iff.mp hprob).resolve_right hmass
  have hnn (x : α) (y : β) :
      0 ≤ a x * b y * (2 - p x - q y) * (1 - p x) * (1 - q y) := by
    have hax := ha x
    have hby := hb y
    rcases hp x with hx | hx <;> rcases hq y with hy | hy <;>
      simp only [hx, hy] <;> positivity
  have hterm (x : α) (y : β) :
      a x * b y * (2 - p x - q y) * (1 - p x) * (1 - q y) = 0 := by
    have hx := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _ => Finset.sum_nonneg (fun y _ => hnn x y))).mp hm x (Finset.mem_univ x)
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hnn x y)).mp hx y
      (Finset.mem_univ y)
  by_cases hconst : ∀ x, a x ≠ 0 → p x = 1
  · exact independent_of_left_flag_constant a b p q 1 hconst f g
  · push Not at hconst
    obtain ⟨x, hax, hpx⟩ := hconst
    have hp0 : p x = 0 := (hp x).resolve_right hpx
    apply independent_of_right_flag_constant a b p q 1 _ f g
    intro y hby
    rcases hq y with hy | hy
    · have hz := hterm x y
      simp only [hp0, hy] at hz
      norm_num at hz
      exact (hz.elim hax hby).elim
    · exact hy

end Problem315.CrossCovariance

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/CrossIndependent.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/CrossCellAffineComposition.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.CrossCellMoments
attribute [local instance] Classical.propDecidable
variable {α β : Type*} [sectionFintypeα : Fintype α] [sectionFintypeβ : Fintype β]

include sectionFintypeα sectionFintypeβ in
theorem count_pos_of_state (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (z : Cell s r c) : 0 < CrossBlock.count s (r z.val.2.1) (c z.val.2.2) := by
  have retainedsectionFintypeα := sectionFintypeα
  have retainedsectionFintypeβ := sectionFintypeβ
  unfold CrossBlock.count
  apply Finset.card_pos.mpr
  exact ⟨z.val.1, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact z.property⟩

theorem conditionalRight_constant_of_ne_two (s : ℕ) (hs : s ≠ 2)
    (r : α → Fin 3) (c : β → Fin 3) (g : β → ℝ) (z : Cell s r c) :
    conditionalRight s r c z.val.2.1 g =
      (∑ y, CrossBlock.independentMargin s (c y) * g y) /
        (∑ y, CrossBlock.independentMargin s (c y)) := by
  have hp : (0 : ℝ) < CrossBlock.count s (r z.val.2.1) (c z.val.2.2) :=
    by exact_mod_cast count_pos_of_state s r c z
  rw [CrossBlock.count_eq_independent_product s hs] at hp
  have ha : CrossBlock.independentMargin s (r z.val.2.1) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hp
    exact (lt_irrefl 0 hp)
  rw [conditionalRight_eq_table]
  simp_rw [CrossBlock.count_eq_independent_product s hs, mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ ha

theorem conditionalLeft_constant_of_ne_two (s : ℕ) (hs : s ≠ 2)
    (r : α → Fin 3) (c : β → Fin 3) (g : α → ℝ) (z : Cell s r c) :
    conditionalLeft s r c z.val.2.2 g =
      (∑ x, CrossBlock.independentMargin s (r x) * g x) /
        (∑ x, CrossBlock.independentMargin s (r x)) := by
  have hp : (0 : ℝ) < CrossBlock.count s (r z.val.2.1) (c z.val.2.2) :=
    by exact_mod_cast count_pos_of_state s r c z
  rw [CrossBlock.count_eq_independent_product s hs] at hp
  have hb : CrossBlock.independentMargin s (c z.val.2.2) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hp
    exact (lt_irrefl 0 hp)
  rw [conditionalLeft_eq_table]
  simp_rw [CrossBlock.count_eq_independent_product s hs]
  have hn : (∑ x, CrossBlock.independentMargin s (r x) *
      CrossBlock.independentMargin s (c z.val.2.2) * g x) =
      (∑ x, CrossBlock.independentMargin s (r x) * g x) *
        CrossBlock.independentMargin s (c z.val.2.2) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hn, ← Finset.sum_mul]
  exact mul_div_mul_right _ _ hb

theorem expectation_first_second_affine (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (f : EuclideanSpace ℝ (Cell s r c)) :
    ∃ a b : ℝ, (s ≠ 2 → b = 0) ∧ ∀ z : Cell s r c,
      PairFibers.expectation (firstPartition s r c)
        (PairFibers.expectation (secondPartition s r c) f) z =
          a + b * offCenter r z.val.2.1 := by
  obtain ⟨g,hg⟩ := expectation_factors_key (fun z : Cell s r c => z.val.2.2) f
  by_cases hs : s = 2
  · subst s
    obtain ⟨a,b,hab⟩ := conditionalRight_two_span r c g
    refine ⟨a,b,fun h => (h rfl).elim, ?_⟩
    intro z
    change PairFibers.expectation (firstPartition 2 r c)
      (PairFibers.expectation (Setoid.ker (fun z : Cell 2 r c => z.val.2.2)) f) z = _
    rw [hg, expectation_first_right_apply]
    exact hab z.val.2.1
  · refine ⟨(∑ y, CrossBlock.independentMargin s (c y) * g y) /
      (∑ y, CrossBlock.independentMargin s (c y)), 0, fun _ => rfl, ?_⟩
    intro z
    change PairFibers.expectation (firstPartition s r c)
      (PairFibers.expectation (Setoid.ker (fun z : Cell s r c => z.val.2.2)) f) z = _
    rw [hg, expectation_first_right_apply, zero_mul, add_zero]
    exact conditionalRight_constant_of_ne_two s hs r c g z

theorem expectation_second_first_affine (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (f : EuclideanSpace ℝ (Cell s r c)) :
    ∃ a b : ℝ, (s ≠ 2 → b = 0) ∧ ∀ z : Cell s r c,
      PairFibers.expectation (secondPartition s r c)
        (PairFibers.expectation (firstPartition s r c) f) z =
          a + b * offCenter c z.val.2.2 := by
  obtain ⟨g,hg⟩ := expectation_factors_key (fun z : Cell s r c => z.val.2.1) f
  by_cases hs : s = 2
  · subst s
    obtain ⟨a,b,hab⟩ := conditionalLeft_two_span r c g
    refine ⟨a,b,fun h => (h rfl).elim, ?_⟩
    intro z
    change PairFibers.expectation (secondPartition 2 r c)
      (PairFibers.expectation (Setoid.ker (fun z : Cell 2 r c => z.val.2.1)) f) z = _
    rw [hg, expectation_second_left_apply]
    exact hab z.val.2.2
  · refine ⟨(∑ x, CrossBlock.independentMargin s (r x) * g x) /
      (∑ x, CrossBlock.independentMargin s (r x)), 0, fun _ => rfl, ?_⟩
    intro z
    change PairFibers.expectation (secondPartition s r c)
      (PairFibers.expectation (Setoid.ker (fun z : Cell s r c => z.val.2.1)) f) z = _
    rw [hg, expectation_second_left_apply, zero_mul, add_zero]
    exact conditionalLeft_constant_of_ne_two s hs r c g z

end Problem315.CrossCellMoments

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/CrossCellAffineComposition.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/DisjointGraphAffine.lean -/
section

namespace OAI

noncomputable section
open scoped Classical

namespace Problem315.DisjointMarginal
open DisjointEncoding
variable {n : Nat} {d : Fin n → Nat}

def crossCellRestriction (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (f : PairResampling.StateSpace n d) : EuclideanSpace ℝ (CrossCell e G) :=
  WithLp.toLp 2 (fun z => f ((stateCellCrossEquiv e G).symm z).val)

@[simp] theorem crossCellRestriction_apply_equiv
    (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (f : PairResampling.StateSpace n d) (H : StateCell e G) :
    crossCellRestriction e G f (stateCellCrossEquiv e G H) = f H.val := by
  simp [crossCellRestriction]

theorem left_expectation_eq_crossCell (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (f : PairResampling.StateSpace n d) (H : StateCell e G) :
    PairResampling.expectation n d {e 0,e 1} f H.val =
      PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.2))
        (crossCellRestriction e G f) (stateCellCrossEquiv e G H) := by
  rw [expectation_leftPair_eq_stateRightData e G f H]
  have heq : (WithLp.toLp 2 (fun K : StateCell e G => f K.val)) =
      WithLp.toLp 2 (fun K => crossCellRestriction e G f (stateCellCrossEquiv e G K)) := by
    ext K
    change f K.val = crossCellRestriction e G f (stateCellCrossEquiv e G K)
    rw [crossCellRestriction_apply_equiv]
  rw [heq, expectation_stateRightData_crossCell]

theorem right_expectation_eq_crossCell (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (f : PairResampling.StateSpace n d) (H : StateCell e G) :
    PairResampling.expectation n d {e 2,e 3} f H.val =
      PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.1))
        (crossCellRestriction e G f) (stateCellCrossEquiv e G H) := by
  rw [expectation_rightPair_eq_stateLeftData e G f H]
  have heq : (WithLp.toLp 2 (fun K : StateCell e G => f K.val)) =
      WithLp.toLp 2 (fun K => crossCellRestriction e G f (stateCellCrossEquiv e G K)) := by
    ext K
    change f K.val = crossCellRestriction e G f (stateCellCrossEquiv e G K)
    rw [crossCellRestriction_apply_equiv]
  rw [heq, expectation_stateLeftData_crossCell]

theorem crossCellRestriction_left_expectation
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (f : PairResampling.StateSpace n d) :
    crossCellRestriction e G (PairResampling.expectation n d {e 0,e 1} f) =
      PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.2))
        (crossCellRestriction e G f) := by
  ext z
  have h := left_expectation_eq_crossCell e G f ((stateCellCrossEquiv e G).symm z)
  simpa only [Equiv.apply_symm_apply, crossCellRestriction] using h

theorem crossCellRestriction_right_expectation
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (f : PairResampling.StateSpace n d) :
    crossCellRestriction e G (PairResampling.expectation n d {e 2,e 3} f) =
      PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.1))
        (crossCellRestriction e G f) := by
  ext z
  have h := right_expectation_eq_crossCell e G f ((stateCellCrossEquiv e G).symm z)
  simpa only [Equiv.apply_symm_apply, crossCellRestriction] using h

theorem right_left_expectation_cell_affine
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (f : PairResampling.StateSpace n d) :
    ∃ A B : ℝ, (CrossBlock.total (crossCode e G.val) ≠ 2 → B = 0) ∧
      ∀ H : StateCell e G,
        PairResampling.expectation n d {e 2,e 3}
          (PairResampling.expectation n d {e 0,e 1} f) H.val =
            A + B * PairEquality.observable (e 0) (e 2) (e 3) H.val := by
  obtain ⟨A,B,hB,hAB⟩ := CrossCellMoments.expectation_first_second_affine
    (CrossBlock.total (crossCode e G.val))
    (fun x : LeftData e G.val => x.val.1) (fun y : RightData e G.val => y.val.1)
    (crossCellRestriction e G f)
  refine ⟨A,B,hB,?_⟩
  intro H
  rw [right_expectation_eq_crossCell, crossCellRestriction_left_expectation]
  have h := hAB (stateCellCrossEquiv e G H)
  change PairFibers.expectation
    (Setoid.ker (fun z : CrossCell e G => z.val.2.1))
    (PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.2))
      (crossCellRestriction e G f)) (stateCellCrossEquiv e G H) =
        A + B * flag (stateLeftData e G H).val.1 at h
  rw [stateLeftFlag_eq_observable] at h
  exact h

theorem left_right_expectation_cell_affine
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (f : PairResampling.StateSpace n d) :
    ∃ A B : ℝ, (CrossBlock.total (crossCode e G.val) ≠ 2 → B = 0) ∧
      ∀ H : StateCell e G,
        PairResampling.expectation n d {e 0,e 1}
          (PairResampling.expectation n d {e 2,e 3} f) H.val =
            A + B * PairEquality.observable (e 2) (e 0) (e 1) H.val := by
  obtain ⟨A,B,hB,hAB⟩ := CrossCellMoments.expectation_second_first_affine
    (CrossBlock.total (crossCode e G.val))
    (fun x : LeftData e G.val => x.val.1) (fun y : RightData e G.val => y.val.1)
    (crossCellRestriction e G f)
  refine ⟨A,B,hB,?_⟩
  intro H
  rw [left_expectation_eq_crossCell, crossCellRestriction_right_expectation]
  have h := hAB (stateCellCrossEquiv e G H)
  change PairFibers.expectation
    (Setoid.ker (fun z : CrossCell e G => z.val.2.2))
    (PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.1))
      (crossCellRestriction e G f)) (stateCellCrossEquiv e G H) =
        A + B * flag (stateRightData e G H).val.1 at h
  rw [stateRightFlag_eq_observable] at h
  exact h

end Problem315.DisjointMarginal

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/DisjointGraphAffine.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/DisjointProjectionCell.lean -/
section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.DisjointEncoding

attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

private theorem pair_count_eq (G : SimpleGraph (Fin n)) (i j w : Fin n)
    (hij : i ≠ j) :
    (({i, j} : Finset (Fin n)).filter (G.Adj w)).card =
      edgeBit G i w + edgeBit G j w := by
  by_cases hi : G.Adj i w <;> by_cases hj : G.Adj j w <;>
    simp [edgeBit, Finset.filter_insert, Finset.filter_singleton,
      G.adj_comm w i, G.adj_comm w j, hi, hj, hij]

theorem sameCell_of_sameFiber_left (e : Fin 4 ↪ Fin n)
    (G H : SimpleGraph (Fin n))
    (h : PairResampling.SameFiber {e 0, e 1} G H) : SameCell e G H := by
  have he (a b : Fin 4) (hab : a ≠ b) : e a ≠ e b := fun h => hab (e.injective h)
  have hout (w : Fin n) (hw : Outside e w) : w ∉ ({e 0, e 1} : Finset (Fin n)) := by
    simp [hw 0, hw 1]
  have h2 : e 2 ∉ ({e 0, e 1} : Finset (Fin n)) := by
    simp [he 2 0 (by decide), he 2 1 (by decide)]
  have h3 : e 3 ∉ ({e 0, e 1} : Finset (Fin n)) := by
    simp [he 3 0 (by decide), he 3 1 (by decide)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun u v hu hv => h.1 u (hout u hu) v (hout v hv)
  · exact h.2.1 (e 0) (by simp) (e 1) (by simp)
  · exact h.1 (e 2) h2 (e 3) h3
  · intro w hw
    have hc := h.2.2 w (hout w hw)
    simpa only [pair_count_eq G _ _ _ (he 0 1 (by decide)),
      pair_count_eq H _ _ _ (he 0 1 (by decide))] using hc
  · intro w hw
    rw [(edgeBit_eq_iff G H (e 2) w).mpr (h.1 (e 2) h2 w (hout w hw)),
      (edgeBit_eq_iff G H (e 3) w).mpr (h.1 (e 3) h3 w (hout w hw))]

theorem sameCell_of_sameFiber_right (e : Fin 4 ↪ Fin n)
    (G H : SimpleGraph (Fin n))
    (h : PairResampling.SameFiber {e 2, e 3} G H) : SameCell e G H := by
  have he (a b : Fin 4) (hab : a ≠ b) : e a ≠ e b := fun h => hab (e.injective h)
  have hout (w : Fin n) (hw : Outside e w) : w ∉ ({e 2, e 3} : Finset (Fin n)) := by
    simp [hw 2, hw 3]
  have h0 : e 0 ∉ ({e 2, e 3} : Finset (Fin n)) := by
    simp [he 0 2 (by decide), he 0 3 (by decide)]
  have h1 : e 1 ∉ ({e 2, e 3} : Finset (Fin n)) := by
    simp [he 1 2 (by decide), he 1 3 (by decide)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun u v hu hv => h.1 u (hout u hu) v (hout v hv)
  · exact h.1 (e 0) h0 (e 1) h1
  · exact h.2.1 (e 2) (by simp) (e 3) (by simp)
  · intro w hw
    rw [(edgeBit_eq_iff G H (e 0) w).mpr (h.1 (e 0) h0 w (hout w hw)),
      (edgeBit_eq_iff G H (e 1) w).mpr (h.1 (e 1) h1 w (hout w hw))]
  · intro w hw
    have hc := h.2.2 w (hout w hw)
    simpa only [pair_count_eq G _ _ _ (he 2 3 (by decide)),
      pair_count_eq H _ _ _ (he 2 3 (by decide))] using hc

def stateCellSetoid (e : Fin 4 ↪ Fin n) : Setoid (GraphState n d) where
  r G H := SameCell e G.val H.val
  iseqv := ⟨fun G => SameCell.refl e G.val,
    fun h => h.symm, fun h h' => h.trans h'⟩

abbrev CellIndex (e : Fin 4 ↪ Fin n) (d : Fin n → ℕ) := Quotient (stateCellSetoid (d := d) e)

noncomputable instance (e : Fin 4 ↪ Fin n) : Fintype (CellIndex e d) := Fintype.ofFinite _

def cellIndex (e : Fin 4 ↪ Fin n) (G : GraphState n d) : CellIndex e d := Quotient.mk _ G

@[simp] theorem cellIndex_eq_iff (e : Fin 4 ↪ Fin n) (G H : GraphState n d) :
    cellIndex e G = cellIndex e H ↔ SameCell e G.val H.val :=
  Quotient.eq

theorem cellInvariant_left (e : Fin 4 ↪ Fin n) (c : CellIndex e d) :
    PairResampling.CellInvariant {e 0, e 1} (fun G => cellIndex e G = c) := by
  intro G H h
  have heq := (cellIndex_eq_iff e G H).mpr (sameCell_of_sameFiber_left e G.val H.val h)
  change cellIndex e G = c ↔ cellIndex e H = c
  rw [heq]

theorem cellInvariant_right (e : Fin 4 ↪ Fin n) (c : CellIndex e d) :
    PairResampling.CellInvariant {e 2, e 3} (fun G => cellIndex e G = c) := by
  intro G H h
  have heq := (cellIndex_eq_iff e G H).mpr (sameCell_of_sameFiber_right e G.val H.val h)
  change cellIndex e G = c ↔ cellIndex e H = c
  rw [heq]

theorem interaction_eq_sum_cells (e : Fin 4 ↪ Fin n) (f : PairResampling.StateSpace n d) :
    ⟪PairResampling.fluctuation n d {e 0, e 1} f,
      PairResampling.fluctuation n d {e 2, e 3} f⟫ =
    ∑ c : CellIndex e d,
      ⟪PairResampling.fluctuation n d {e 0, e 1}
          (PairResampling.restrictCell (fun G => cellIndex e G = c) f),
        PairResampling.fluctuation n d {e 2, e 3}
          (PairResampling.restrictCell (fun G => cellIndex e G = c) f)⟫ :=
  PairResampling.fluctuation_interaction_eq_sum_cells (cellIndex e) _ _
    (cellInvariant_left e) (cellInvariant_right e) f

theorem interaction_bound_of_cell_bounds (e : Fin 4 ↪ Fin n)
    (g r s : PairResampling.StateSpace n d → PairResampling.StateSpace n d)
    (f : PairResampling.StateSpace n d)
    (hg : ∀ c : CellIndex e d,
      g (PairResampling.restrictCell (fun G => cellIndex e G = c) f) =
        PairResampling.restrictCell (fun G => cellIndex e G = c) (g f))
    (hr : ∀ c : CellIndex e d,
      r (PairResampling.restrictCell (fun G => cellIndex e G = c) f) =
        PairResampling.restrictCell (fun G => cellIndex e G = c) (r f))
    (hs : ∀ c : CellIndex e d,
      s (PairResampling.restrictCell (fun G => cellIndex e G = c) f) =
        PairResampling.restrictCell (fun G => cellIndex e G = c) (s f))
    (hlocal : ∀ c : CellIndex e d,
      let fc := PairResampling.restrictCell (fun G => cellIndex e G = c) f
      2 * ‖g fc‖ ^ 2 - ‖r fc‖ ^ 2 - ‖s fc‖ ^ 2 ≤
        2 * ⟪PairResampling.fluctuation n d {e 0, e 1} fc,
          PairResampling.fluctuation n d {e 2, e 3} fc⟫) :
    2 * ‖g f‖ ^ 2 - ‖r f‖ ^ 2 - ‖s f‖ ^ 2 ≤
      2 * ⟪PairResampling.fluctuation n d {e 0, e 1} f,
        PairResampling.fluctuation n d {e 2, e 3} f⟫ := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun c _ => hlocal c)
  simp_rw [hg, hr, hs] at hsum
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← PairResampling.norm_sq_eq_sum_cell_norm_sq,
    ← interaction_eq_sum_cells] at hsum
  exact hsum

end Problem315.DisjointEncoding

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/DisjointProjectionCell.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/RankOneInteraction.lean -/
section

namespace OAI

namespace Problem315
namespace RankOneInteraction

theorem interaction_identity
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f p q u v : E) (c x y : ℝ)
    (huu : inner ℝ u u = 1) (hvv : inner ℝ v v = 1)
    (huv : inner ℝ u v = c)
    (hfu : inner ℝ f u = x + c * y)
    (hfv : inner ℝ f v = c * x + y)
    (hfp : inner ℝ f p = inner ℝ p p)
    (hfq : inner ℝ f q = inner ℝ q q)
    (hpu : inner ℝ p u = x + c * y)
    (hpv : inner ℝ p v = c * (x + c * y))
    (hqu : inner ℝ q u = c * (c * x + y))
    (hqv : inner ℝ q v = c * x + y)
    (hpq : inner ℝ p q = c * (x + c * y) * (c * x + y)) :
    inner ℝ (f - p) (f - q) =
      ‖f - p - q + (c * y) • u + (c * x) • v‖ ^ 2 +
        inner ℝ (y • (v - c • u)) (x • (u - c • v)) := by
  have huf : inner ℝ u f = x + c * y := by rw [real_inner_comm, hfu]
  have hvf : inner ℝ v f = c * x + y := by rw [real_inner_comm, hfv]
  have hpf : inner ℝ p f = inner ℝ p p := by rw [real_inner_comm, hfp]
  have hqf : inner ℝ q f = inner ℝ q q := by rw [real_inner_comm, hfq]
  have hup : inner ℝ u p = x + c * y := by rw [real_inner_comm, hpu]
  have hvp : inner ℝ v p = c * (x + c * y) := by rw [real_inner_comm, hpv]
  have huq : inner ℝ u q = c * (c * x + y) := by rw [real_inner_comm, hqu]
  have hvq : inner ℝ v q = c * x + y := by rw [real_inner_comm, hqv]
  have hvu : inner ℝ v u = c := by rw [real_inner_comm, huv]
  have hqp : inner ℝ q p = c * (x + c * y) * (c * x + y) := by
    rw [real_inner_comm, hpq]
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [huu, hvv, huv, hfu, hfv, hfp, hfq, hpu, hpv, hqu, hqv, hpq,
    huf, hvf, hpf, hqf, hup, hvp, huq, hvq, hvu, hqp]
  ring

theorem interaction_lower_bound
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b j h k : E)
    (hid : inner ℝ h k = ‖j‖ ^ 2 + inner ℝ a b) :
    2 * ‖j‖ ^ 2 - ‖a‖ ^ 2 - ‖b‖ ^ 2 ≤ 2 * inner ℝ h k := by
  have hn : 0 ≤ ‖a‖ ^ 2 + 2 * inner ℝ a b + ‖b‖ ^ 2 := by
    rw [← norm_add_sq_real]
    exact sq_nonneg _
  linarith

theorem exists_plane_coefficients (α β c : ℝ) (hc : 1 - c ^ 2 ≠ 0) :
    ∃ x y : ℝ, α = x + c * y ∧ β = c * x + y := by
  refine ⟨(α - c * β) / (1 - c ^ 2), (β - c * α) / (1 - c ^ 2), ?_, ?_⟩
  · field_simp
    ring
  · field_simp
    ring

theorem projection_interaction_identity
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P Q : E →ₗ[ℝ] E) (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (u v : E) (c : ℝ)
    (huu : inner ℝ u u = 1) (hvv : inner ℝ v v = 1) (huv : inner ℝ u v = c)
    (hPu : P u = u) (hPv : P v = c • u)
    (hQu : Q u = c • v) (hQv : Q v = v)
    (hPQ : ∀ z, P (Q z) = (c * inner ℝ z v) • u)
    (f : E) (x y : ℝ)
    (hfu : inner ℝ f u = x + c * y) (hfv : inner ℝ f v = c * x + y) :
    inner ℝ (f - P f) (f - Q f) =
      ‖f - P f - Q f + (c * y) • u + (c * x) • v‖ ^ 2 +
        inner ℝ (y • (v - c • u)) (x • (u - c • v)) := by
  apply interaction_identity f (P f) (Q f) u v c x y huu hvv huv hfu hfv
  · simpa only [hPi] using (hPs f (P f)).symm
  · simpa only [hQi] using (hQs f (Q f)).symm
  · rw [hPs, hPu, hfu]
  · rw [hPs, hPv, real_inner_smul_right, hfu]
  · rw [hQs, hQu, real_inner_smul_right, hfv]
  · rw [hQs, hQv, hfv]
  · rw [hPs, hPQ, real_inner_smul_right, hfu, hfv]
    ring

theorem projection_remainder_mem_common_kernel
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P Q : E →ₗ[ℝ] E)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (u v f : E) (c x y : ℝ)
    (hPu : P u = u) (hPv : P v = c • u)
    (hQu : Q u = c • v) (hQv : Q v = v)
    (hPQ : P (Q f) = (c * (c * x + y)) • u)
    (hQP : Q (P f) = (c * (x + c * y)) • v) :
    P (f - P f - Q f + (c * y) • u + (c * x) • v) = 0 ∧
    Q (f - P f - Q f + (c * y) • u + (c * x) • v) = 0 := by
  constructor
  · simp only [map_add, map_sub, map_smul, hPi, hPQ, hPu, hPv]
    module
  · simp only [map_add, map_sub, map_smul, hQi, hQP, hQu, hQv]
    module

theorem norm_sq_le_of_inner_eq_self
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w z : E) (h : inner ℝ z w = inner ℝ w w) : ‖w‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  have hn := sq_nonneg ‖z - w‖
  rw [norm_sub_sq_real, h, real_inner_self_eq_norm_sq] at hn
  nlinarith

theorem projection_norm_sq_le
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : E →ₗ[ℝ] E) (hPs : P.IsSymmetric) (hPi : ∀ z, P (P z) = P z)
    (z : E) : ‖P z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  apply norm_sq_le_of_inner_eq_self
  simpa only [hPi] using (hPs z (P z)).symm

theorem error_inner_self
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f u v : E) (c y : ℝ)
    (huu : inner ℝ u u = 1) (hvv : inner ℝ v v = 1) (huv : inner ℝ u v = c)
    (hcoordinate : inner ℝ f v - c * inner ℝ f u = y * (1 - c ^ 2)) :
    inner ℝ f (y • (v - c • u)) =
      inner ℝ (y • (v - c • u)) (y • (v - c • u)) := by
  have hvu : inner ℝ v u = c := by rw [real_inner_comm, huv]
  simp only [real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_sub_right,
    huu, hvv, huv, hvu]
  rw [hcoordinate]
  ring

theorem error_norm_sq_le
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R : E →ₗ[ℝ] E) (hRs : R.IsSymmetric) (f w : E)
    (hRw : R w = w) (hfw : inner ℝ f w = inner ℝ w w) :
    ‖w‖ ^ 2 ≤ ‖R f‖ ^ 2 := by
  apply norm_sq_le_of_inner_eq_self
  rw [hRs, hRw, hfw]

theorem rank_one_disjoint_interaction
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P Q G R S : E →ₗ[ℝ] E)
    (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric) (hGs : G.IsSymmetric)
    (hRs : R.IsSymmetric) (hSs : S.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (hGi : ∀ z, G (G z) = G z)
    (u v : E) (c : ℝ) (hc : 1 - c ^ 2 ≠ 0)
    (huu : inner ℝ u u = 1) (hvv : inner ℝ v v = 1) (huv : inner ℝ u v = c)
    (hPu : P u = u) (hPv : P v = c • u)
    (hQu : Q u = c • v) (hQv : Q v = v)
    (hPQ : ∀ z, P (Q z) = (c * inner ℝ z v) • u)
    (hGP : ∀ z, G (P z) = 0) (hGQ : ∀ z, G (Q z) = 0)
    (hRline : R (v - c • u) = v - c • u)
    (hSline : S (u - c • v) = u - c • v)
    (f : E) :
    2 * ‖G f‖ ^ 2 - ‖R f‖ ^ 2 - ‖S f‖ ^ 2 ≤
      2 * inner ℝ (f - P f) (f - Q f) := by
  obtain ⟨x, y, hfu, hfv⟩ := exists_plane_coefficients (inner ℝ f u) (inner ℝ f v) c hc
  let j := f - P f - Q f + (c * y) • u + (c * x) • v
  let a := y • (v - c • u)
  let b := x • (u - c • v)
  have hid : inner ℝ (f - P f) (f - Q f) = ‖j‖ ^ 2 + inner ℝ a b :=
    projection_interaction_identity P Q hPs hQs hPi hQi u v c huu hvv huv
      hPu hPv hQu hQv hPQ f x y hfu hfv
  have hGu : G u = 0 := by rw [← hPu, hGP]
  have hGv : G v = 0 := by rw [← hQv, hGQ]
  have hGj : G j = G f := by
    simp only [j, map_add, map_sub, map_smul, hGP, hGQ, hGu, hGv,
      smul_zero, sub_zero, add_zero]
  have hg : ‖G f‖ ^ 2 ≤ ‖j‖ ^ 2 := by
    rw [← hGj]
    exact projection_norm_sq_le G hGs hGi j
  have hfa : inner ℝ f a = inner ℝ a a := by
    apply error_inner_self f u v c y huu hvv huv
    rw [hfu, hfv]
    ring
  have hfb : inner ℝ f b = inner ℝ b b := by
    apply error_inner_self f v u c x hvv huu
      (by rw [real_inner_comm, huv])
    rw [hfu, hfv]
    ring
  have hra : ‖a‖ ^ 2 ≤ ‖R f‖ ^ 2 :=
    error_norm_sq_le R hRs f a (by simp only [a, map_smul, hRline]) hfa
  have hsb : ‖b‖ ^ 2 ≤ ‖S f‖ ^ 2 :=
    error_norm_sq_le S hSs f b (by simp only [b, map_smul, hSline]) hfb
  have hlocal := interaction_lower_bound a b j (f - P f) (f - Q f) hid
  linarith

theorem composition_of_covariance
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P Q : E →ₗ[ℝ] E) (hPs : P.IsSymmetric) (u v : E) (c : ℝ)
    (hcov : ∀ z w, inner ℝ (P z) (Q w) = c * inner ℝ z u * inner ℝ w v)
    (f : E) : P (Q f) = (c * inner ℝ f v) • u := by
  apply ext_inner_left ℝ
  intro z
  rw [← hPs, hcov, real_inner_smul_right]
  ring

theorem rank_one_disjoint_interaction_of_covariance
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P Q G R S : E →ₗ[ℝ] E)
    (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric) (hGs : G.IsSymmetric)
    (hRs : R.IsSymmetric) (hSs : S.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (hGi : ∀ z, G (G z) = G z)
    (u v : E) (c : ℝ) (hc : 1 - c ^ 2 ≠ 0)
    (huu : inner ℝ u u = 1) (hvv : inner ℝ v v = 1)
    (hPu : P u = u) (hQv : Q v = v)
    (hcov : ∀ z w, inner ℝ (P z) (Q w) = c * inner ℝ z u * inner ℝ w v)
    (hGP : ∀ z, G (P z) = 0) (hGQ : ∀ z, G (Q z) = 0)
    (hRline : R (v - c • u) = v - c • u)
    (hSline : S (u - c • v) = u - c • v)
    (f : E) :
    2 * ‖G f‖ ^ 2 - ‖R f‖ ^ 2 - ‖S f‖ ^ 2 ≤
      2 * inner ℝ (f - P f) (f - Q f) := by
  have hPQ := composition_of_covariance P Q hPs u v c hcov
  have hcov' : ∀ z w, inner ℝ (Q z) (P w) = c * inner ℝ z v * inner ℝ w u := by
    intro z w
    rw [real_inner_comm, hcov]
    ring
  have hQP := composition_of_covariance Q P hQs v u c hcov'
  have hPv : P v = c • u := by simpa only [hQv, hvv, mul_one] using hPQ v
  have hQu : Q u = c • v := by simpa only [hPu, huu, mul_one] using hQP u
  have huv : inner ℝ u v = c := by
    simpa only [hPu, hQv, huu, hvv, mul_one] using hcov u v
  exact rank_one_disjoint_interaction P Q G R S hPs hQs hGs hRs hSs hPi hQi hGi
    u v c hc huu hvv huv hPu hPv hQu hQv hPQ hGP hGQ hRline hSline f

theorem independent_interaction_identity
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P Q : E →ₗ[ℝ] E) (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (hPQ : ∀ z, P (Q z) = 0) (f : E) :
    inner ℝ (f - P f) (f - Q f) = ‖f - P f - Q f‖ ^ 2 := by
  have hfp : inner ℝ f (P f) = inner ℝ (P f) (P f) := by
    simpa only [hPi] using (hPs f (P f)).symm
  have hfq : inner ℝ f (Q f) = inner ℝ (Q f) (Q f) := by
    simpa only [hQi] using (hQs f (Q f)).symm
  have hpf : inner ℝ (P f) f = inner ℝ (P f) (P f) := by rw [real_inner_comm, hfp]
  have hqf : inner ℝ (Q f) f = inner ℝ (Q f) (Q f) := by rw [real_inner_comm, hfq]
  have hpq : inner ℝ (P f) (Q f) = 0 := by rw [hPs, hPQ, inner_zero_right]
  have hqp : inner ℝ (Q f) (P f) = 0 := by rw [real_inner_comm, hpq]
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, hfp, hfq, hpf, hqf, hpq, hqp]
  ring

theorem independent_disjoint_interaction
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P Q G : E →ₗ[ℝ] E)
    (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric) (hGs : G.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (hGi : ∀ z, G (G z) = G z)
    (hPQ : ∀ z, P (Q z) = 0)
    (hGP : ∀ z, G (P z) = 0) (hGQ : ∀ z, G (Q z) = 0)
    (f : E) : ‖G f‖ ^ 2 ≤ inner ℝ (f - P f) (f - Q f) := by
  rw [independent_interaction_identity P Q hPs hQs hPi hQi hPQ f]
  have hG : G (f - P f - Q f) = G f := by
    simp only [map_sub, hGP, hGQ, sub_zero]
  rw [← hG]
  exact projection_norm_sq_le G hGs hGi _

end RankOneInteraction
end Problem315

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/RankOneInteraction.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/ProjectionRangeInteraction.lean -/
section

namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace Problem315.ProjectionRangeInteraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem interaction_of_decomposition
    (P Q G R S : E →ₗ[ℝ] E)
    (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric) (hGs : G.IsSymmetric)
    (hRs : R.IsSymmetric) (hSs : S.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (hGi : ∀ z, G (G z) = G z)
    (hGP : ∀ z, G (P z) = 0) (hGQ : ∀ z, G (Q z) = 0)
    (hR : ∀ z, R (Q z - P (Q z)) = Q z - P (Q z))
    (hS : ∀ z, S (P z - Q (P z)) = P z - Q (P z))
    (f p q j : E) (hf : f = P p + Q q + j)
    (hPj : P j = 0) (hQj : Q j = 0) :
    2 * ‖G f‖ ^ 2 - ‖R f‖ ^ 2 - ‖S f‖ ^ 2 ≤
      2 * ⟪f - P f, f - Q f⟫ := by
  let a := Q q - P (Q q)
  let b := P p - Q (P p)
  have hPa : P a = 0 := by simp only [a, map_sub, hPi, sub_self]
  have hQb : Q b = 0 := by simp only [b, map_sub, hQi, sub_self]
  have hja : ⟪j, a⟫ = 0 := by
    simp only [a, inner_sub_right]
    rw [← hQs, ← hPs, hQj, hPj, inner_zero_left, inner_zero_left, sub_self]
  have hjb : ⟪j, b⟫ = 0 := by
    simp only [b, inner_sub_right]
    rw [← hPs, ← hQs, hPj, hQj, inner_zero_left, inner_zero_left, sub_self]
  have ha : f - P f = j + a := by
    rw [hf]
    simp only [map_add, hPi, hPj]
    dsimp [a]
    module
  have hb : f - Q f = j + b := by
    rw [hf]
    simp only [map_add, hQi, hQj]
    dsimp [b]
    module
  have hfa : ⟪f, a⟫ = ⟪a, a⟫ := by
    have hz : ⟪P f, a⟫ = 0 := by rw [hPs, hPa, inner_zero_right]
    have ht : ⟪f - P f, a⟫ = ⟪a, a⟫ := by
      rw [ha, inner_add_left, hja, zero_add]
    simpa only [inner_sub_left, hz, sub_zero] using ht
  have hfb : ⟪f, b⟫ = ⟪b, b⟫ := by
    have hz : ⟪Q f, b⟫ = 0 := by rw [hQs, hQb, inner_zero_right]
    have ht : ⟪f - Q f, b⟫ = ⟪b, b⟫ := by
      rw [hb, inner_add_left, hjb, zero_add]
    simpa only [inner_sub_left, hz, sub_zero] using ht
  have hRa : R a = a := hR q
  have hSb : S b = b := hS p
  have hra := RankOneInteraction.error_norm_sq_le R hRs f a hRa hfa
  have hsb := RankOneInteraction.error_norm_sq_le S hSs f b hSb hfb
  have hGf : G f = G j := by rw [hf, map_add, map_add, hGP, hGQ, zero_add, zero_add]
  have hg : ‖G f‖ ^ 2 ≤ ‖j‖ ^ 2 := by
    rw [hGf]
    exact RankOneInteraction.projection_norm_sq_le G hGs hGi j
  have hid : ⟪f - P f, f - Q f⟫ = ‖j‖ ^ 2 + ⟪a, b⟫ := by
    rw [ha, hb, inner_add_left, inner_add_right, inner_add_right,
      hjb, show ⟪a, j⟫ = 0 by rw [real_inner_comm, hja],
      real_inner_self_eq_norm_sq]
    ring
  have hlow := RankOneInteraction.interaction_lower_bound a b j (f - P f) (f - Q f) hid
  linarith

theorem exists_range_decomposition [FiniteDimensional ℝ E]
    (P Q : E →ₗ[ℝ] E) (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (f : E) :
    ∃ p q j : E, f = P p + Q q + j ∧ P j = 0 ∧ Q j = 0 := by
  let K : Submodule ℝ E := P.range ⊔ Q.range
  let w := K.starProjection f
  let j := f - w
  have hw : w ∈ K := K.starProjection_apply_mem f
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hw
  obtain ⟨p₀, rfl⟩ := hp
  obtain ⟨q₀, rfl⟩ := hq
  have hj : j ∈ Kᗮ := K.sub_starProjection_mem_orthogonal f
  have hPj : P j = 0 := by
    have hm : P j ∈ K := (show P.range ≤ K from le_sup_left) (show P j ∈ P.range from ⟨j, rfl⟩)
    have hz : ⟪j, P j⟫ = 0 := (K.mem_orthogonal' j).mp hj (P j) hm
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [hPs, hPi, hz]
  have hQj : Q j = 0 := by
    have hm : Q j ∈ K := (show Q.range ≤ K from le_sup_right) (show Q j ∈ Q.range from ⟨j, rfl⟩)
    have hz : ⟪j, Q j⟫ = 0 := (K.mem_orthogonal' j).mp hj (Q j) hm
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [hQs, hQi, hz]
  refine ⟨p₀, q₀, j, ?_, hPj, hQj⟩
  rw [hpq]
  dsimp [j]
  module

theorem exists_correlated_range_decomposition [FiniteDimensional ℝ E]
    (P Q : E →ₗ[ℝ] E) (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (p : E) :
    ∃ x u : E, P p = P (Q x) + u ∧ P u = u ∧ Q u = 0 := by
  let K := (P.comp Q).range
  let w := K.starProjection (P p)
  let u := P p - w
  have hw : w ∈ K := K.starProjection_apply_mem (P p)
  obtain ⟨x, hx⟩ := hw
  change P (Q x) = w at hx
  have hPw : P w = w := by rw [← hx, hPi]
  have hPu : P u = u := by simp only [u, map_sub, hPi, hPw]
  have hu : u ∈ Kᗮ := K.sub_starProjection_mem_orthogonal (P p)
  have hQu : Q u = 0 := by
    have hm : P (Q u) ∈ K := ⟨u, rfl⟩
    have hz : ⟪u, P (Q u)⟫ = 0 := (K.mem_orthogonal' u).mp hu _ hm
    rw [← hPs, hPu] at hz
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [hQs, hQi, hz]
  refine ⟨x, u, ?_, hPu, hQu⟩
  rw [hx]
  dsimp [u]
  module

theorem exists_two_projection_decomposition [FiniteDimensional ℝ E]
    (P Q : E →ₗ[ℝ] E) (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (f : E) :
    ∃ p q j u v : E,
      f = P (Q p) + Q (P q) + j + u + v ∧
      P j = 0 ∧ Q j = 0 ∧ P u = u ∧ Q u = 0 ∧ P v = 0 ∧ Q v = v := by
  obtain ⟨p₀,q₀,j,hf,hPj,hQj⟩ := exists_range_decomposition P Q hPs hQs hPi hQi f
  obtain ⟨p,u,hp,hPu,hQu⟩ := exists_correlated_range_decomposition P Q hPs hQs hPi hQi p₀
  obtain ⟨q,v,hq,hQv,hPv⟩ := exists_correlated_range_decomposition Q P hQs hPs hQi hPi q₀
  refine ⟨p,q,j,u,v,?_,hPj,hQj,hPu,hQu,hPv,hQv⟩
  rw [hf,hp,hq]
  module

theorem interaction_of_correlated_error_ranges [FiniteDimensional ℝ E]
    (P Q G R S : E →ₗ[ℝ] E)
    (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric) (hGs : G.IsSymmetric)
    (hRs : R.IsSymmetric) (hSs : S.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (hGi : ∀ z, G (G z) = G z)
    (hGP : ∀ z, G (P z) = 0) (hGQ : ∀ z, G (Q z) = 0)
    (hR : ∀ z, R (Q (P z) - P (Q (P z))) = Q (P z) - P (Q (P z)))
    (hS : ∀ z, S (P (Q z) - Q (P (Q z))) = P (Q z) - Q (P (Q z)))
    (f : E) :
    2 * ‖G f‖ ^ 2 - ‖R f‖ ^ 2 - ‖S f‖ ^ 2 ≤
      2 * ⟪f - P f, f - Q f⟫ := by
  obtain ⟨p,q,j,u,v,hf,hPj,hQj,hPu,hQu,hPv,hQv⟩ :=
    exists_two_projection_decomposition P Q hPs hQs hPi hQi f
  let a := Q (P q) - P (Q (P q))
  let b := P (Q p) - Q (P (Q p))
  have hPa : P a = 0 := by simp only [a, map_sub, hPi, sub_self]
  have hQb : Q b = 0 := by simp only [b, map_sub, hQi, sub_self]
  have hja : ⟪j, a⟫ = 0 := by
    simp only [a, inner_sub_right]
    rw [← hQs j (P q), hQj, inner_zero_left,
      ← hPs j (Q (P q)), hPj, inner_zero_left, sub_self]
  have hjb : ⟪j, b⟫ = 0 := by
    simp only [b, inner_sub_right]
    rw [← hPs j (Q p), hPj, inner_zero_left,
      ← hQs j (P (Q p)), hQj, inner_zero_left, sub_self]
  have hju : ⟪j, u⟫ = 0 := by rw [← hPu, ← hPs, hPj, inner_zero_left]
  have hjv : ⟪j, v⟫ = 0 := by rw [← hQv, ← hQs, hQj, inner_zero_left]
  have hua : ⟪u, a⟫ = 0 := by rw [← hPu, hPs, hPa, inner_zero_right]
  have hvb : ⟪v, b⟫ = 0 := by rw [← hQv, hQs, hQb, inner_zero_right]
  have huv : ⟪u, v⟫ = 0 := by rw [← hPu, hPs, hPv, inner_zero_right]
  have hva : ⟪v, a⟫ = 0 := by
    simp only [a, inner_sub_right]
    rw [← hQs, hQv, ← hPs, hPv, inner_zero_left,
      ← hPs, hPv, inner_zero_left, sub_self]
  have hub : ⟪u, b⟫ = 0 := by
    simp only [b, inner_sub_right]
    rw [← hPs, hPu, ← hQs, hQu, inner_zero_left,
      ← hQs, hQu, inner_zero_left, sub_self]
  have ha : f - P f = j + a + v := by
    rw [hf]
    simp only [map_add, hPi, hPj, hPu, hPv]
    dsimp [a]
    module
  have hb : f - Q f = j + b + u := by
    rw [hf]
    simp only [map_add, hQi, hQj, hQu, hQv]
    dsimp [b]
    module
  have hfa : ⟪f, a⟫ = ⟪a, a⟫ := by
    have hz : ⟪P f, a⟫ = 0 := by rw [hPs, hPa, inner_zero_right]
    have ht : ⟪f - P f, a⟫ = ⟪a, a⟫ := by
      rw [ha, inner_add_left, inner_add_left, hja, hva, zero_add, add_zero]
    simpa only [inner_sub_left, hz, sub_zero] using ht
  have hfb : ⟪f, b⟫ = ⟪b, b⟫ := by
    have hz : ⟪Q f, b⟫ = 0 := by rw [hQs, hQb, inner_zero_right]
    have ht : ⟪f - Q f, b⟫ = ⟪b, b⟫ := by
      rw [hb, inner_add_left, inner_add_left, hjb, hub, zero_add, add_zero]
    simpa only [inner_sub_left, hz, sub_zero] using ht
  have hra := RankOneInteraction.error_norm_sq_le R hRs f a (hR q) hfa
  have hsb := RankOneInteraction.error_norm_sq_le S hSs f b (hS p) hfb
  have hGu : G u = 0 := by rw [← hPu, hGP]
  have hGv : G v = 0 := by rw [← hQv, hGQ]
  have hGf : G f = G j := by
    rw [hf]
    simp only [map_add, hGP, hGQ, hGu, hGv, zero_add, add_zero]
  have hg : ‖G f‖ ^ 2 ≤ ‖j‖ ^ 2 := by
    rw [hGf]
    exact RankOneInteraction.projection_norm_sq_le G hGs hGi j
  have hid : ⟪f - P f, f - Q f⟫ = ‖j‖ ^ 2 + ⟪a, b⟫ := by
    rw [ha, hb]
    simp only [inner_add_left, inner_add_right, hjb, hju, hvb,
      show ⟪a, j⟫ = 0 by rw [real_inner_comm, hja],
      show ⟪a, u⟫ = 0 by rw [real_inner_comm, hua],
      show ⟪v, j⟫ = 0 by rw [real_inner_comm, hjv],
      show ⟪v, u⟫ = 0 by rw [real_inner_comm, huv],
      real_inner_self_eq_norm_sq, zero_add, add_zero]
  have hlow := RankOneInteraction.interaction_lower_bound a b j (f - P f) (f - Q f) hid
  linarith

end Problem315.ProjectionRangeInteraction

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/ProjectionRangeInteraction.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairRangeInteraction.lean -/
section

namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace Problem315.PairResampling
attribute [local instance] Classical.propDecidable

theorem pair_interaction_of_correlated_ranges
    {n : ℕ} {d : Fin n → ℕ} (a b : Finset (Fin n))
    (G R S : StateSpace n d →L[ℝ] StateSpace n d)
    (hGs : G.toLinearMap.IsSymmetric)
    (hRs : R.toLinearMap.IsSymmetric) (hSs : S.toLinearMap.IsSymmetric)
    (hGi : ∀ f, G (G f) = G f)
    (hGa : ∀ f, G (expectation n d a f) = 0)
    (hGb : ∀ f, G (expectation n d b f) = 0)
    (hR : ∀ f, R (fluctuation n d a (expectation n d b (expectation n d a f))) =
      fluctuation n d a (expectation n d b (expectation n d a f)))
    (hS : ∀ f, S (fluctuation n d b (expectation n d a (expectation n d b f))) =
      fluctuation n d b (expectation n d a (expectation n d b f)))
    (f : StateSpace n d) :
    2 * ‖G f‖ ^ 2 - ‖R f‖ ^ 2 - ‖S f‖ ^ 2 ≤
      2 * ⟪fluctuation n d a f, fluctuation n d b f⟫ := by
  apply ProjectionRangeInteraction.interaction_of_correlated_error_ranges
    (expectation n d a).toLinearMap (expectation n d b).toLinearMap
    G.toLinearMap R.toLinearMap S.toLinearMap
    (expectation_isSymmetric a) (expectation_isSymmetric b) hGs hRs hSs
    (expectation_idempotent a) (expectation_idempotent b) hGi hGa hGb
    (fun z => ?_) (fun z => ?_) f |>.trans_eq
      (by simp only [ContinuousLinearMap.coe_coe, fluctuation_eq_sub])
  · simpa only [fluctuation_eq_sub, ContinuousLinearMap.coe_coe] using hR z
  · simpa only [fluctuation_eq_sub, ContinuousLinearMap.coe_coe] using hS z

end Problem315.PairResampling

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairRangeInteraction.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairAffineInteraction.lean -/
section

namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

def AffineFlagImage (i j k l : Fin n) (f : StateSpace n d) : Prop :=
  ∃ base weight : StateSpace n d,
    base ∈ fiberSpace n d {i,j} ∧ weight ∈ fiberSpace n d {i,j} ∧
    (∀ G : GraphState n d, crossTotal i j k l G ≠ 2 → weight G = 0) ∧
    f = base + multiply weight (observable i k l)

theorem affineFlagImage_of_cellwise {β : Type*}
    (i j k l : Fin n) (key : GraphState n d → β)
    (hkey : ∀ G H : GraphState n d, SameFiber {i,j} G.val H.val → key G = key H)
    (f : StateSpace n d)
    (hcell : ∀ c : β, ∃ A B : ℝ,
      (∀ G : GraphState n d, key G = c → f G = A + B * observable i k l G) ∧
      (∀ G : GraphState n d, key G = c → crossTotal i j k l G ≠ 2 → B = 0)) :
    AffineFlagImage i j k l f := by
  choose A B hformula hsupport using hcell
  let base : StateSpace n d := WithLp.toLp 2 (fun G => A (key G))
  let weight : StateSpace n d := WithLp.toLp 2 (fun G => B (key G))
  refine ⟨base,weight,?_,?_,?_,?_⟩
  · intro G H h
    change A (key G) = A (key H)
    rw [hkey G H h]
  · intro G H h
    change B (key G) = B (key H)
    rw [hkey G H h]
  · intro G hG
    exact hsupport (key G) G rfl hG
  · ext G
    exact hformula (key G) G rfl

theorem fluctuation_mem_of_affineFlagImage
    (i j k l : Fin n) (hij : i ≠ j)
    (hk : Outside i j k) (hl : Outside i j l)
    (f : StateSpace n d) (hf : AffineFlagImage i j k l f) :
    fluctuation n d {i,j} f ∈ equalitySpace i j k l := by
  obtain ⟨base,weight,hbase,hweight,hsupport,rfl⟩ := hf
  rw [map_add, (fluctuation_eq_zero_iff _ _).mpr hbase, zero_add]
  exact fluctuation_weighted_observable_mem i j k l hij hk hl weight hweight hsupport

theorem projection_fixes_fluctuation_of_affineFlagImage
    (i j k l : Fin n) (hij : i ≠ j)
    (hk : Outside i j k) (hl : Outside i j l)
    (f : StateSpace n d) (hf : AffineFlagImage i j k l f) :
    projection i j k l (fluctuation n d {i,j} f) = fluctuation n d {i,j} f :=
  (projection_eq_self_iff _ _ _ _ _).mpr
    (fluctuation_mem_of_affineFlagImage i j k l hij hk hl f hf)

theorem interaction_of_affine_conditional_images
    (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hk : Outside i j k) (hl : Outside i j l)
    (hi : Outside k l i) (hj : Outside k l j)
    (G : StateSpace n d →L[ℝ] StateSpace n d)
    (hGs : G.toLinearMap.IsSymmetric) (hGi : ∀ f, G (G f) = G f)
    (hGa : ∀ f, G (expectation n d {i,j} f) = 0)
    (hGb : ∀ f, G (expectation n d {k,l} f) = 0)
    (hBA : ∀ f, AffineFlagImage i j k l
      (expectation n d {k,l} (expectation n d {i,j} f)))
    (hAB : ∀ f, AffineFlagImage k l i j
      (expectation n d {i,j} (expectation n d {k,l} f)))
    (f : StateSpace n d) :
    2 * ‖G f‖ ^ 2 - ‖projection i j k l f‖ ^ 2 - ‖projection k l i j f‖ ^ 2 ≤
      2 * ⟪fluctuation n d {i,j} f, fluctuation n d {k,l} f⟫ := by
  exact pair_interaction_of_correlated_ranges {i,j} {k,l} G
    (projection i j k l) (projection k l i j) hGs
    (equalitySpace i j k l).starProjection_isSymmetric
    (equalitySpace k l i j).starProjection_isSymmetric
    hGi hGa hGb
    (fun z => projection_fixes_fluctuation_of_affineFlagImage i j k l hij hk hl _ (hBA z))
    (fun z => projection_fixes_fluctuation_of_affineFlagImage k l i j hkl hi hj _ (hAB z)) f

theorem switch_interaction_of_affine_conditional_images
    (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hk : Outside i j k) (hl : Outside i j l)
    (hi : Outside k l i) (hj : Outside k l j)
    (p : SwitchProposal n)
    (hpa : SwitchPairFiber.Crosses p {i,j}) (hpb : SwitchPairFiber.Crosses p {k,l})
    (hBA : ∀ f : StateSpace n d, AffineFlagImage i j k l
      (expectation n d {k,l} (expectation n d {i,j} f)))
    (hAB : ∀ f : StateSpace n d, AffineFlagImage k l i j
      (expectation n d {i,j} (expectation n d {k,l} f)))
    (f : StateSpace n d) :
    2 * ‖SwitchFlip.projection p f‖ ^ 2 -
        ‖projection i j k l f‖ ^ 2 - ‖projection k l i j f‖ ^ 2 ≤
      2 * ⟪fluctuation n d {i,j} f, fluctuation n d {k,l} f⟫ := by
  exact interaction_of_affine_conditional_images i j k l hij hkl hk hl hi hj
    (SwitchFlip.projection p) (SwitchFlip.projection_symmetric p)
    (SwitchFlip.projection_idempotent p)
    (SwitchFlip.projection_expectation p {i,j} hpa)
    (SwitchFlip.projection_expectation p {k,l} hpb) hBA hAB f

end Problem315.PairEquality

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairAffineInteraction.lean -/

/- BEGIN exact official body: lean/OAI/Probability/SwitchChain/PairActualAffine.lean -/
section

namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling DisjointEncoding DisjointMarginal
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem right_left_expectation_affine (e : Fin 4 ↪ Fin n)
    (f : StateSpace n d) :
    AffineFlagImage (e 0) (e 1) (e 2) (e 3)
      (expectation n d {e 2,e 3} (expectation n d {e 0,e 1} f)) := by
  apply affineFlagImage_of_cellwise _ _ _ _ (cellIndex e)
    (fun G H h => (cellIndex_eq_iff e G H).mpr
      (sameCell_of_sameFiber_left e G.val H.val h))
  intro c
  induction c using Quotient.inductionOn with
  | h G =>
    obtain ⟨A,B,hB,hAB⟩ := right_left_expectation_cell_affine e G f
    refine ⟨A,B,?_,?_⟩
    · intro H hH
      have hcell : SameCell e G.val H.val :=
        ((cellIndex_eq_iff e H G).mp hH).symm
      exact hAB ⟨H,hcell⟩
    · intro H hH ht
      have hcell : SameCell e G.val H.val :=
        ((cellIndex_eq_iff e H G).mp hH).symm
      apply hB
      rwa [← equality_crossTotal_on_cell e G ⟨H,hcell⟩]

theorem left_right_expectation_affine (e : Fin 4 ↪ Fin n)
    (f : StateSpace n d) :
    AffineFlagImage (e 2) (e 3) (e 0) (e 1)
      (expectation n d {e 0,e 1} (expectation n d {e 2,e 3} f)) := by
  apply affineFlagImage_of_cellwise _ _ _ _ (cellIndex e)
    (fun G H h => (cellIndex_eq_iff e G H).mpr
      (sameCell_of_sameFiber_right e G.val H.val h))
  intro c
  induction c using Quotient.inductionOn with
  | h G =>
    obtain ⟨A,B,hB,hAB⟩ := left_right_expectation_cell_affine e G f
    refine ⟨A,B,?_,?_⟩
    · intro H hH
      have hcell : SameCell e G.val H.val :=
        ((cellIndex_eq_iff e H G).mp hH).symm
      exact hAB ⟨H,hcell⟩
    · intro H hH ht
      have hcell : SameCell e G.val H.val :=
        ((cellIndex_eq_iff e H G).mp hH).symm
      apply hB
      rwa [← equality_crossTotal_reverse_on_cell e G ⟨H,hcell⟩]

theorem actual_switch_interaction (e : Fin 4 ↪ Fin n)
    (p : SwitchProposal n)
    (hpa : SwitchPairFiber.Crosses p {e 0,e 1})
    (hpb : SwitchPairFiber.Crosses p {e 2,e 3})
    (f : StateSpace n d) :
    2 * ‖SwitchFlip.projection p f‖ ^ 2 -
        ‖projection (e 0) (e 1) (e 2) (e 3) f‖ ^ 2 -
        ‖projection (e 2) (e 3) (e 0) (e 1) f‖ ^ 2 ≤
      2 * ⟪fluctuation n d {e 0,e 1} f,
        fluctuation n d {e 2,e 3} f⟫ := by
  have he (i j : Fin 4) (hij : i ≠ j) : e i ≠ e j :=
    fun h => hij (e.injective h)
  exact switch_interaction_of_affine_conditional_images
    (e 0) (e 1) (e 2) (e 3) (he 0 1 (by decide)) (he 2 3 (by decide))
    ⟨he 2 0 (by decide),he 2 1 (by decide)⟩
    ⟨he 3 0 (by decide),he 3 1 (by decide)⟩
    ⟨he 0 2 (by decide),he 0 3 (by decide)⟩
    ⟨he 1 2 (by decide),he 1 3 (by decide)⟩
    p hpa hpb (right_left_expectation_affine e)
    (left_right_expectation_affine e) f

theorem actual_named_interaction (i j k l : Fin n) (h : FourDistinct i j k l)
    (f : StateSpace n d) :
    2 * ‖SwitchFlip.projection (CrossToggle.crossProposal i j k l h) f‖ ^ 2 -
        ‖projection i j k l f‖ ^ 2 - ‖projection k l i j f‖ ^ 2 ≤
      2 * ⟪fluctuation n d {i,j} f, fluctuation n d {k,l} f⟫ := by
  let e : Fin 4 ↪ Fin n :=
    ⟨![i,j,k,l], by
      rcases h with ⟨hij,hik,hil,hjk,hjl,hkl⟩
      intro x y hxy
      fin_cases x <;> fin_cases y <;>
        simp_all [Ne.symm hij, Ne.symm hik, Ne.symm hil,
          Ne.symm hjk, Ne.symm hjl, Ne.symm hkl]⟩
  exact actual_switch_interaction e (CrossToggle.crossProposal i j k l h)
    (CrossToggle.crossProposal_left i j k l h)
    (CrossToggle.crossProposal_right i j k l h) f

end Problem315.PairEquality

end

end OAI

end
/- END exact official body: lean/OAI/Probability/SwitchChain/PairActualAffine.lean -/
