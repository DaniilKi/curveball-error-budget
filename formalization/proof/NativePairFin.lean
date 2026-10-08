import NatFinSubsets
import CurveballTransitionCore

namespace CurveballVerified
noncomputable section
open OAI.Problem315 CurveballSubsetVerified
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem finSet_range (n : Nat) : finSetOfNat n (List.range n).toFinset = Finset.univ := by
  ext v
  simp [finSetOfNat,v.isLt]

def pairFinEquiv (n : Nat) : Fin (n.choose 2) ≃ ↥(PairResampling.pairs n) :=
  (pairAssignmentEquiv n).trans
    ((boundedAssignmentEquiv n (List.range n) 2 (fun _ hv => List.mem_range.mp hv)).trans
      { toFun := fun T => ⟨T.val,by
          apply Finset.mem_powersetCard.mpr
          exact ⟨Finset.subset_univ _,T.property.2⟩⟩
        invFun := fun T => ⟨T.val,by
          have ht := Finset.mem_powersetCard.mp T.property
          exact ⟨by rw [finSet_range]; exact Finset.subset_univ _,ht.2⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })

theorem pairFinEquiv_val (n : Nat) (rank : Fin (n.choose 2)) :
    (pairFinEquiv n rank).val = finSetOfNat n (pairAssignmentEquiv n rank).val := rfl

theorem pairFinEquiv_native {n : Nat} (rank : Fin (n.choose 2)) (i j : Fin n)
    (hp : CurveballNative.unrankPair n rank.val = some (i.val,j.val)) :
    (pairFinEquiv n rank).val = {i,j} := by
  let r : Fin ((List.range n).length.choose 2) := ⟨rank.val,by simpa using rank.isLt⟩
  have hs := unrankSubset_at (List.range n) 2 r
  have hl : (subsetAt (List.range n) 2 r).val = [i.val,j.val] :=
    Option.some.inj (hs.symm.trans (unrankPair_list hp))
  have he : (pairAssignmentEquiv n rank).val = ({i.val,j.val} : Finset Nat) := by
    change ((subsetAt (List.range n) 2 r).val).toFinset = _
    rw [hl]
    simp
  rw [pairFinEquiv_val,he]
  ext v
  simp only [mem_finSetOfNat,Finset.mem_insert,Finset.mem_singleton]
  exact or_congr Fin.ext_iff.symm Fin.ext_iff.symm

theorem nativePairEndpoint_exists (n : Nat) (rank : Fin (n.choose 2)) :
    ∃ p : Fin n × Fin n,
      CurveballNative.unrankPair n rank.val = some (p.1.val,p.2.val) ∧ p.1 < p.2 := by
  obtain ⟨i,j,hp,hij,hjn,_⟩ := unrankPair_complete n rank
  exact ⟨(⟨i,by omega⟩,⟨j,hjn⟩),hp,hij⟩

/-- Proof-side typed observation of the actual native pair, with no ideal
    pair selection substituted for the decoder. -/
def nativePairEndpoint (n : Nat) (rank : Fin (n.choose 2)) : Fin n × Fin n :=
  Classical.choose (nativePairEndpoint_exists n rank)

theorem nativePairEndpoint_spec (n : Nat) (rank : Fin (n.choose 2)) :
    CurveballNative.unrankPair n rank.val =
      some ((nativePairEndpoint n rank).1.val,(nativePairEndpoint n rank).2.val) ∧
      (nativePairEndpoint n rank).1 < (nativePairEndpoint n rank).2 :=
  Classical.choose_spec (nativePairEndpoint_exists n rank)

theorem nativePairEndpoint_finset (n : Nat) (rank : Fin (n.choose 2)) :
    {(nativePairEndpoint n rank).1,(nativePairEndpoint n rank).2} =
      (pairFinEquiv n rank).val :=
  (pairFinEquiv_native rank _ _ (nativePairEndpoint_spec n rank).1).symm

theorem nativePairEndpoint_sum {n : Nat} {d : Fin n → Nat} (G H : GraphState n d) :
    (∑ rank : Fin (n.choose 2),
      pairKernel {(nativePairEndpoint n rank).1,(nativePairEndpoint n rank).2} G H) /
        (n.choose 2 : ℝ) = transition n d G H := by
  simp_rw [nativePairEndpoint_finset]
  have he := (pairFinEquiv n).sum_comp (fun a => pairKernel a.val G H)
  rw [he]
  unfold transition
  congr 1
  exact Finset.sum_coe_sort (PairResampling.pairs n) (fun a => pairKernel a G H)

#print axioms pairFinEquiv
#print axioms nativePairEndpoint_spec
#print axioms nativePairEndpoint_sum
end
end CurveballVerified
