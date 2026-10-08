import NativeDecoderIntegration

namespace CurveballSubsetVerified
noncomputable section
open CurveballVerified

def pairAssignmentEquiv (n : Nat) : Fin (n.choose 2) ≃ Assignment (List.range n) 2 :=
  (show Fin (n.choose 2) ≃ Fin ((List.range n).length.choose 2) from
    { toFun := fun r => ⟨r.val,by simpa using r.isLt⟩
      invFun := fun r => ⟨r.val,by simpa using r.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans
    (subsetAssignmentEquiv List.nodup_range List.pairwise_le_range 2)

instance pairAssignment_nonempty (n : Nat) [NeZero (n.choose 2)] :
    Nonempty (Assignment (List.range n) 2) :=
  ⟨pairAssignmentEquiv n ⟨0,Nat.pos_of_ne_zero (NeZero.ne (n.choose 2))⟩⟩

/-- The proof-side finite wrapper observes the actual native pair return value;
    the membership guard is proved redundant for every valid rank below. -/
def nativePairAssignment (n rank : Nat) : Option (Assignment (List.range n) 2) :=
  (CurveballNative.unrankPair n rank).bind fun out =>
    if h : ({out.1,out.2} : Finset Nat) ∈ (List.range n).toFinset.powersetCard 2
    then some ⟨{out.1,out.2},h⟩ else none

theorem nativePairAssignment_at (n : Nat) (rank : Fin (n.choose 2)) :
    nativePairAssignment n rank.val = some (pairAssignmentEquiv n rank) := by
  obtain ⟨i,j,hpair,hij,hjn,hlist⟩ := unrankPair_complete n rank
  let r : Fin ((List.range n).length.choose 2) := ⟨rank.val,by simpa using rank.isLt⟩
  have hs := unrankSubset_at (List.range n) 2 r
  have hl : (subsetAt (List.range n) 2 r).val = [i,j] := Option.some.inj (hs.symm.trans hlist)
  have he : (pairAssignmentEquiv n rank).val = ({i,j} : Finset Nat) := by
    change ((subsetAt (List.range n) 2 r).val).toFinset = _
    rw [hl]
    simp
  have hp : ({i,j} : Finset Nat) ∈ (List.range n).toFinset.powersetCard 2 :=
    he ▸ (pairAssignmentEquiv n rank).property
  simp only [nativePairAssignment,hpair,Option.bind_some]
  rw [dif_pos hp]
  apply congrArg some
  exact Subtype.ext he.symm

/-- Every two-element subset of the vertex range is reached exactly once by the
    actual unordered-pair decoder. Uniformity is established, not assumed. -/
theorem native_pair_uniform (n : Nat) [NeZero (n.choose 2)] :
    mapLaw (uniformLaw (Fin (n.choose 2)))
      (fun rank => nativePairAssignment n rank.val) =
      mapLaw (uniformLaw (Assignment (List.range n) 2)) Option.some := by
  have hf : (fun rank : Fin (n.choose 2) => nativePairAssignment n rank.val) =
      Option.some ∘ pairAssignmentEquiv n := by
    funext rank
    exact nativePairAssignment_at n rank
  rw [hf,← mapLaw_comp,map_uniform_bijection]

def nativePairFromBits (n width cap : Nat) (tape : List Bool) :
    Option (Assignment (List.range n) 2) :=
  (fixedBitsOutput (n.choose 2) width cap tape).bind fun rank => nativePairAssignment n rank.val

/-- Actual fair finite bits followed by actual native pair unranking. The law
    retains every cap failure, and is expressed on unordered pairs of Nat labels. -/
theorem actual_capped_pair_law (n width cap : Nat) [NeZero (n.choose 2)]
    (hwidth : n.choose 2 ≤ 2 ^ width) :
    mapLaw (batchLaw (fun _ => uniformLaw (Fin width → Bool)) cap)
      (fun bits => nativePairFromBits n width cap (bitTape width cap bits)) =
      mapPartialLaw (cappedWordLaw (n.choose 2) (2 ^ width) cap) (pairAssignmentEquiv n) := by
  have hf : (fun bits => nativePairFromBits n width cap (bitTape width cap bits)) =
      Option.map (pairAssignmentEquiv n) ∘
        (fun bits => fixedBitsOutput (n.choose 2) width cap (bitTape width cap bits)) := by
    funext bits
    cases h : fixedBitsOutput (n.choose 2) width cap (bitTape width cap bits) with
    | none => simp [nativePairFromBits,h]
    | some rank => simp [nativePairFromBits,h,nativePairAssignment_at]
  rw [hf,← mapLaw_comp,actual_capped_bit_law
    (Nat.pos_of_ne_zero (NeZero.ne (n.choose 2))) width cap hwidth]
  rfl

#print axioms nativePairAssignment_at
#print axioms native_pair_uniform
#print axioms actual_capped_pair_law
end
end CurveballSubsetVerified
