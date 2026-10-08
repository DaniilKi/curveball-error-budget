import NativeCardinality
import Mathlib.Data.Nat.Choose.Basic

namespace CurveballVerified

/-- Every raw native left-list entry is in the native exclusive list; neither
graph validity nor distinct/bounded endpoint assumptions are required. -/
theorem native_left_subset_exclusive (n : Nat) (es : CurveballNative.Edges)
    (a b : Nat) :
    ∀ v ∈ CurveballNative.left n es a b, v ∈ CurveballNative.exclusive n es a b := by
  intro v hv
  obtain ⟨hvn,houtside,ha,hb⟩ := (CurveballNative.left_mem n es a b v).mp hv
  exact (CurveballNative.exclusive_mem n es a b v).mpr
    ⟨hvn,houtside,Or.inl ⟨ha,hb⟩⟩

theorem native_left_length_le_exclusive (n : Nat) (es : CurveballNative.Edges)
    (a b : Nat) :
    (CurveballNative.left n es a b).length ≤
      (CurveballNative.exclusive n es a b).length := by
  have hs : (CurveballNative.left n es a b).toFinset ⊆
      (CurveballNative.exclusive n es a b).toFinset := by
    intro v hv
    exact List.mem_toFinset.mpr
      (native_left_subset_exclusive n es a b v (List.mem_toFinset.mp hv))
  have hc := Finset.card_le_card hs
  have hl : (CurveballNative.left n es a b).Nodup := List.nodup_range.filter _
  have he : (CurveballNative.exclusive n es a b).Nodup := List.nodup_range.filter _
  simpa only [List.toFinset_card_of_nodup hl,List.toFinset_card_of_nodup he] using hc

/-- A native exclusive list is a duplicate-free subset of the universe with
the two distinct pair endpoints removed. Validity of raw es is unnecessary. -/
theorem native_exclusive_length_le_sub_two (n : Nat) (es : CurveballNative.Edges)
    (i j : Fin n) (hij : i ≠ j) :
    (CurveballNative.exclusive n es i.val j.val).length ≤ n - 2 := by
  have hs : chosenSet n (CurveballNative.exclusive n es i.val j.val) ⊆
      (Finset.univ : Finset (Fin n)) \ {i,j} := by
    intro v hv
    have hm : v.val ∈ CurveballNative.exclusive n es i.val j.val := by
      simpa [chosenSet] using hv
    have ho := ((CurveballNative.exclusive_mem n es i.val j.val v.val).mp hm).2.1
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ v,?_⟩
    simp only [Finset.mem_insert,Finset.mem_singleton]
    rintro (hvi | hvj)
    · exact ho.1 (congrArg Fin.val hvi)
    · exact ho.2 (congrArg Fin.val hvj)
  have hc : ((Finset.univ : Finset (Fin n)) \ {i,j}).card = n - 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ ({i,j} : Finset (Fin n))),
      Finset.card_pair hij]
    simp
  calc
    (CurveballNative.exclusive n es i.val j.val).length =
        (chosenSet n (CurveballNative.exclusive n es i.val j.val)).card := by
      symm
      apply chosenSet_card
      · exact List.nodup_range.filter _
      · intro v hv
        exact List.mem_range.mp (List.mem_filter.mp hv).1
    _ ≤ ((Finset.univ : Finset (Fin n)) \ {i,j}).card := Finset.card_le_card hs
    _ = n - 2 := hc

/-- Direct interface for the actual raw Nat labels checked by the runtime. -/
theorem native_exclusive_length_le_sub_two_raw (n : Nat) (es : CurveballNative.Edges)
    (a b : Nat) (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    (CurveballNative.exclusive n es a b).length ≤ n - 2 := by
  exact native_exclusive_length_le_sub_two n es ⟨a,ha⟩ ⟨b,hb⟩
    (fun he => hab (congrArg Fin.val he))

/-- The existing Mathlib maximum covers every index b, including b > a. -/
theorem binomial_le_global_central (N a b : Nat) (ha : a ≤ N) :
    a.choose b ≤ N.choose (N / 2) := by
  exact (Nat.choose_le_choose b ha).trans (Nat.choose_le_middle b N)

/-- Exact mathematical subset bound consumed through native_choose_eq by the
reservation proof; no distribution, positivity or word-width claim is added. -/
theorem native_subset_choose_le_global (n : Nat) (es : CurveballNative.Edges)
    (i j : Fin n) (hij : i ≠ j) :
    (CurveballNative.exclusive n es i.val j.val).length.choose
        (CurveballNative.left n es i.val j.val).length ≤
      (n - 2).choose ((n - 2) / 2) := by
  exact binomial_le_global_central (n - 2) _ _
    (native_exclusive_length_le_sub_two n es i j hij)

theorem native_subset_choose_le_global_raw (n : Nat) (es : CurveballNative.Edges)
    (a b : Nat) (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    (CurveballNative.exclusive n es a b).length.choose
        (CurveballNative.left n es a b).length ≤
      (n - 2).choose ((n - 2) / 2) := by
  exact binomial_le_global_central (n - 2) _ _
    (native_exclusive_length_le_sub_two_raw n es a b ha hb hab)

#print axioms native_left_subset_exclusive
#print axioms native_left_length_le_exclusive
#print axioms native_exclusive_length_le_sub_two
#print axioms native_exclusive_length_le_sub_two_raw
#print axioms binomial_le_global_central
#print axioms native_subset_choose_le_global
#print axioms native_subset_choose_le_global_raw

end CurveballVerified
