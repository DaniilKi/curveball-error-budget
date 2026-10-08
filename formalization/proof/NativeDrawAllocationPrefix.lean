import NativeConcreteExecution

namespace CurveballVerified
noncomputable section
open CurveballNativeSampling CurveballSubsetVerified

/-- DRAFT: exact success AND failure framing for the actual builder draw.
    It allocates both complete reservations, including padding, before exposing
    the next untouched suffix. No native sampler definition is substituted. -/
theorem draw_split_prefix (r : Request) (es : CurveballNative.Edges)
    (pairBits : Tape (pairReserve r)) (subsetBits : Tape (subsetReserve r))
    (suffix : List Bool)
    (hp : wordWidth (r.n.choose 2) * r.cap ≤ pairReserve r)
    (hs : ∀ rank : Fin (r.n.choose 2),
      wordWidth (nativeSubsetBound r es rank) * r.cap ≤ subsetReserve r) :
    draw r es ((pairBits.val ++ subsetBits.val) ++ suffix) =
      (draw r es (pairBits.val ++ subsetBits.val)).map (fun out => (out.1,suffix)) := by
  have hp0 := reserved_observation (r.n.choose 2) (wordWidth (r.n.choose 2))
    r.cap (pairReserve r) pairBits.val subsetBits.val pairBits.property hp
  have hps := reserved_observation (r.n.choose 2) (wordWidth (r.n.choose 2))
    r.cap (pairReserve r) pairBits.val (subsetBits.val ++ suffix) pairBits.property hp
  unfold draw
  simp only [native_choose_eq]
  rw [List.append_assoc,hps,hp0]
  cases hr : reservedBitsOutput (r.n.choose 2) (wordWidth (r.n.choose 2)) r.cap
      (pairReserve r) pairBits.val with
  | none => simp [hr]
  | some rank =>
    have he := (nativePairEndpoint_spec r.n rank).1
    have hs0 := reserved_observation (nativeSubsetBound r es rank)
      (wordWidth (nativeSubsetBound r es rank)) r.cap (subsetReserve r)
        subsetBits.val [] subsetBits.property (hs rank)
    have hss := reserved_observation (nativeSubsetBound r es rank)
      (wordWidth (nativeSubsetBound r es rank)) r.cap (subsetReserve r)
        subsetBits.val suffix subsetBits.property (hs rank)
    simp only [List.append_nil] at hs0
    simp only [hr,Option.map_some]
    dsimp only [Bind.bind,Pure.pure]
    simp only [Option.bind_some,he]
    dsimp only [nativeSubsetBound] at hs0 hss ⊢
    rw [hs0,hss]
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

theorem draw_allocated_prefix (r : Request) (es : CurveballNative.Edges)
    (allocated : Tape (pairReserve r + subsetReserve r)) (suffix : List Bool)
    (hp : wordWidth (r.n.choose 2) * r.cap ≤ pairReserve r)
    (hs : ∀ rank : Fin (r.n.choose 2),
      wordWidth (nativeSubsetBound r es rank) * r.cap ≤ subsetReserve r) :
    draw r es (allocated.val ++ suffix) =
      (draw r es allocated.val).map (fun out => (out.1,suffix)) := by
  let x := (appendTapeEquiv (pairReserve r) (subsetReserve r)).symm allocated
  have hval : allocated.val = x.1.val ++ x.2.val :=
    (congrArg Subtype.val ((appendTapeEquiv (pairReserve r) (subsetReserve r)).apply_symm_apply allocated)).symm
  rw [hval]
  exact draw_split_prefix r es x.1 x.2 suffix hp hs

theorem draw_allocated_success_suffix (r : Request) (es : CurveballNative.Edges)
    (allocated : Tape (pairReserve r + subsetReserve r))
    (hp : wordWidth (r.n.choose 2) * r.cap ≤ pairReserve r)
    (hs : ∀ rank : Fin (r.n.choose 2),
      wordWidth (nativeSubsetBound r es rank) * r.cap ≤ subsetReserve r)
    (drawn : CurveballNative.Draw) (rest : List Bool)
    (hd : draw r es allocated.val = some (drawn,rest)) : rest = [] := by
  have h := draw_allocated_prefix r es allocated [] hp hs
  simp only [List.append_nil,hd,Option.map_some,Option.some.injEq] at h
  exact congrArg Prod.snd h

#print axioms draw_allocated_prefix
#print axioms draw_allocated_success_suffix
end
end CurveballVerified
