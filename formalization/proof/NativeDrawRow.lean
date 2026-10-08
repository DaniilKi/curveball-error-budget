import NativeSubsetRow
import NativePairFin
import PartialTapeBind
import NativeReservedObservation
import NativeSamplingProtocol

namespace CurveballVerified
noncomputable section
open OAI.Problem315 CurveballSubsetVerified CurveballNativeSampling
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Finite observation of the exact builder draw followed by the exact native
    trade. This does not implement an alternative draw or alter its failures. -/
def samplingStep (r : Request) (d : Fin r.n → Nat) (es : CurveballNative.Edges)
    (bits : List Bool) : Option (GraphState r.n d) :=
  (draw r es bits).bind fun out =>
    nativeTradeState r.n d es out.1.first out.1.second out.1.chosen

def nativeSubsetBound (r : Request) (es : CurveballNative.Edges)
    (rank : Fin (r.n.choose 2)) : Nat :=
  let p := nativePairEndpoint r.n rank
  (CurveballNative.exclusive r.n es p.1.val p.2.val).length.choose
    (CurveballNative.left r.n es p.1.val p.2.val).length

theorem samplingStep_split (r : Request) (d : Fin r.n → Nat)
    (es : CurveballNative.Edges)
    (pairBits : Tape (pairReserve r)) (subsetBits : Tape (subsetReserve r))
    (hp : wordWidth (r.n.choose 2) * r.cap ≤ pairReserve r)
    (hs : ∀ rank : Fin (r.n.choose 2),
      wordWidth (nativeSubsetBound r es rank) * r.cap ≤ subsetReserve r) :
    samplingStep r d es (pairBits.val ++ subsetBits.val) =
      (reservedBitsOutput (r.n.choose 2) (wordWidth (r.n.choose 2)) r.cap
        (pairReserve r) pairBits.val).bind fun rank =>
      let p := nativePairEndpoint r.n rank
      nativeSubsetReserved r.n d es p.1.val p.2.val
        (wordWidth (nativeSubsetBound r es rank)) r.cap (subsetReserve r) subsetBits.val := by
  have hpair := reserved_observation (r.n.choose 2) (wordWidth (r.n.choose 2))
    r.cap (pairReserve r) pairBits.val subsetBits.val pairBits.property hp
  unfold samplingStep draw
  simp only [native_choose_eq]
  rw [hpair]
  cases hr : reservedBitsOutput (r.n.choose 2) (wordWidth (r.n.choose 2)) r.cap
      (pairReserve r) pairBits.val with
  | none => simp [hr]
  | some rank =>
    have he := (nativePairEndpoint_spec r.n rank).1
    have hsubset := reserved_observation (nativeSubsetBound r es rank)
      (wordWidth (nativeSubsetBound r es rank)) r.cap (subsetReserve r)
        subsetBits.val [] subsetBits.property (hs rank)
    simp only [List.append_nil] at hsubset
    simp only [hr,Option.map_some]
    dsimp only [Bind.bind,Pure.pure]
    simp only [Option.bind_some,he]
    dsimp only [nativeSubsetBound] at hsubset ⊢
    rw [hsubset]
    unfold nativeSubsetReserved nativeRankOutput
    cases hsub : reservedBitsOutput
        ((CurveballNative.exclusive r.n es (nativePairEndpoint r.n rank).1.val
          (nativePairEndpoint r.n rank).2.val).length.choose
            (CurveballNative.left r.n es (nativePairEndpoint r.n rank).1.val
              (nativePairEndpoint r.n rank).2.val).length)
        (wordWidth ((CurveballNative.exclusive r.n es (nativePairEndpoint r.n rank).1.val
          (nativePairEndpoint r.n rank).2.val).length.choose
            (CurveballNative.left r.n es (nativePairEndpoint r.n rank).1.val
              (nativePairEndpoint r.n rank).2.val).length)) r.cap (subsetReserve r) subsetBits.val with
    | none => simp [hsub]
    | some subrank =>
      simp only [hsub,Option.map_some,Option.bind_some]
      cases hu : CurveballNative.unrankSubset
        (CurveballNative.exclusive r.n es (nativePairEndpoint r.n rank).1.val
          (nativePairEndpoint r.n rank).2.val)
        (CurveballNative.left r.n es (nativePairEndpoint r.n rank).1.val
          (nativePairEndpoint r.n rank).2.val).length subrank.val <;> simp [hu]

/-- The complete actual builder one-step graph row is at most the existing
    credited transition row. Numeric width/reservation obligations are explicit;
    no uniform output, Markov property, or sampler row law is assumed. -/
theorem sampling_draw_row_dominated (r : Request) (d : Fin r.n → Nat)
    (es : CurveballNative.Edges) (C : CanonicalGraph r.n) (href : EdgeRefines es C)
    (hg : CurveballNative.graphValid r.n es = true) (G H : GraphState r.n d)
    (hG : C.toSimpleGraph = G.val) [NeZero (r.n.choose 2)]
    (hpw : r.n.choose 2 ≤ 2 ^ wordWidth (r.n.choose 2))
    (hpr : wordWidth (r.n.choose 2) * r.cap ≤ pairReserve r)
    (hspos : ∀ rank : Fin (r.n.choose 2), 0 < nativeSubsetBound r es rank)
    (hsw : ∀ rank : Fin (r.n.choose 2),
      nativeSubsetBound r es rank ≤ 2 ^ wordWidth (nativeSubsetBound r es rank))
    (hsr : ∀ rank : Fin (r.n.choose 2),
      wordWidth (nativeSubsetBound r es rank) * r.cap ≤ subsetReserve r) :
    (mapLaw (uniformLaw (Tape (pairReserve r + subsetReserve r)))
      (fun t => samplingStep r d es t.val)).mass (some H) ≤ transition r.n d G H := by
  let p := uniformLaw (Tape (pairReserve r))
  let q := uniformLaw (Tape (subsetReserve r))
  let f := fun t : Tape (pairReserve r) =>
    reservedBitsOutput (r.n.choose 2) (wordWidth (r.n.choose 2)) r.cap (pairReserve r) t.val
  let g := fun (rank : Fin (r.n.choose 2)) (t : Tape (subsetReserve r)) =>
    let ij := nativePairEndpoint r.n rank
    nativeSubsetReserved r.n d es ij.1.val ij.2.val
      (wordWidth (nativeSubsetBound r es rank)) r.cap (subsetReserve r) t.val
  have he := map_uniform_bijection (appendTapeEquiv (pairReserve r) (subsetReserve r))
  have hf : (fun t => samplingStep r d es
      (appendTapeEquiv (pairReserve r) (subsetReserve r) t).val) =
      (fun t => (f t.1).bind (fun rank => g rank t.2)) := by
    funext t
    exact samplingStep_split r d es t.1 t.2 hpr hsr
  rw [← he,mapLaw_comp,uniformLaw_product]
  simp only [Function.comp_def]
  rw [hf,bindTapeLaw_pushforward]
  have hpLaw : mapLaw p f = cappedWordLaw (r.n.choose 2)
      (2 ^ wordWidth (r.n.choose 2)) r.cap :=
    uniform_reserved_tape_law (Nat.pos_of_ne_zero (NeZero.ne (r.n.choose 2))) _ _ _ hpw hpr
  change (bindTapeLaw (mapLaw p f) q g).mass (some H) ≤ _
  rw [hpLaw]
  letI : NeZero (2 ^ wordWidth (r.n.choose 2)) := ⟨ne_of_gt (by positivity)⟩
  have hrow (rank : Fin (r.n.choose 2)) (Z : GraphState r.n d) :
      (mapLaw q (g rank)).mass (some Z) ≤
        pairKernel {(nativePairEndpoint r.n rank).1,(nativePairEndpoint r.n rank).2} G Z := by
    letI : NeZero ((CurveballNative.exclusive r.n es (nativePairEndpoint r.n rank).1.val
        (nativePairEndpoint r.n rank).2.val).length.choose
          (CurveballNative.left r.n es (nativePairEndpoint r.n rank).1.val
            (nativePairEndpoint r.n rank).2.val).length) :=
      ⟨ne_of_gt (by simpa only [nativeSubsetBound] using hspos rank)⟩
    have hij := ne_of_lt (nativePairEndpoint_spec r.n rank).2
    exact native_reserved_subset_dominated href hg G Z hG _ _ hij
      (wordWidth (nativeSubsetBound r es rank)) r.cap (subsetReserve r) (hsw rank) (hsr rank)
  have hnonneg (rank : Fin (r.n.choose 2)) (Z : GraphState r.n d) :
      0 ≤ pairKernel {(nativePairEndpoint r.n rank).1,(nativePairEndpoint r.n rank).2} G Z := by
    unfold pairKernel
    split_ifs <;> positivity
  have hb := bindTapeLaw_dominated
    (cappedWordLaw (r.n.choose 2) (2 ^ wordWidth (r.n.choose 2)) r.cap) q g
    (uniformLaw (Fin (r.n.choose 2)))
    (fun rank Z => pairKernel {(nativePairEndpoint r.n rank).1,(nativePairEndpoint r.n rank).2} G Z)
    (capped_success_dominated hpw r.cap) hrow hnonneg H
  have hsum : (∑ rank : Fin (r.n.choose 2),
      (uniformLaw (Fin (r.n.choose 2))).mass rank *
        pairKernel {(nativePairEndpoint r.n rank).1,(nativePairEndpoint r.n rank).2} G H) =
      transition r.n d G H := by
    simp only [uniformLaw,Fintype.card_fin,div_eq_mul_inv,one_mul]
    rw [← Finset.mul_sum]
    simpa only [div_eq_mul_inv,mul_comm] using nativePairEndpoint_sum G H
  exact hb.trans_eq hsum

#print axioms samplingStep_split
#print axioms sampling_draw_row_dominated
end
end CurveballVerified
