import NativeGeneratedTraceLaw

namespace CurveballVerified
noncomputable section
open CurveballNativeSampling

/-- DRAFT: complete actual generation preserves an arbitrary untouched suffix,
    with exactly the same success/failure and raw draw/edge outputs. -/
theorem generate_chunks_prefix (r : Request) (hc : SamplingCapacities r)
    (t : Nat) (es : CurveballNative.Edges) (hv : CurveballNative.graphValid r.n es = true)
    (bits : BatchSpace (Tape (pairReserve r + subsetReserve r)) t) (suffix : List Bool) :
    generateTrace r t es
      ((chunksTapeEquiv (pairReserve r + subsetReserve r) t bits).val ++ suffix) =
      (generateTrace r t es (chunksTapeEquiv (pairReserve r + subsetReserve r) t bits).val).map
        (fun out => (out.1,out.2.1,suffix)) := by
  induction t generalizing es suffix with
  | zero =>
    have hn : (chunksTapeEquiv (pairReserve r + subsetReserve r) 0 bits).val = [] := rfl
    simp [generateTrace,hn]
  | succ t ih =>
    rw [chunksTapeEquiv_val_succ,List.append_assoc]
    have hp0 := draw_allocated_prefix r es bits.1
      (chunksTapeEquiv (pairReserve r + subsetReserve r) t bits.2).val
      hc.pairReserve (hc.subsetReserve es hv)
    have hps := draw_allocated_prefix r es bits.1
      ((chunksTapeEquiv (pairReserve r + subsetReserve r) t bits.2).val ++ suffix)
      hc.pairReserve (hc.subsetReserve es hv)
    simp only [generateTrace]
    rw [hp0,hps]
    cases hd : draw r es bits.1.val with
    | none => simp [hd]
    | some out =>
      obtain ⟨drawn,rest⟩ := out
      simp only [hd,Option.map_some]
      dsimp only [Bind.bind,Pure.pure]
      simp only [Option.bind_some]
      cases ht : CurveballNative.trade r.n es drawn.first drawn.second drawn.chosen with
      | none => simp [ht]
      | some next =>
        have hnext := CurveballNative.trade_success_valid ht
        simp only [ht,Option.bind_some]
        rw [ih next hnext bits.2 suffix]
        cases hg : generateTrace r t next
            (chunksTapeEquiv (pairReserve r + subsetReserve r) t bits.2).val <;> simp [hg]

theorem generate_allocated_prefix (r : Request) (hc : SamplingCapacities r)
    (t : Nat) (es : CurveballNative.Edges) (hv : CurveballNative.graphValid r.n es = true)
    (allocated : Tape ((pairReserve r + subsetReserve r)*t)) (suffix : List Bool) :
    generateTrace r t es (allocated.val ++ suffix) =
      (generateTrace r t es allocated.val).map (fun out => (out.1,out.2.1,suffix)) := by
  let bits := (chunksTapeEquiv (pairReserve r + subsetReserve r) t).symm allocated
  have he : chunksTapeEquiv (pairReserve r + subsetReserve r) t bits = allocated :=
    (chunksTapeEquiv (pairReserve r + subsetReserve r) t).apply_symm_apply allocated
  have heval := congrArg Subtype.val he
  simpa only [heval] using generate_chunks_prefix r hc t es hv bits suffix

/-- Exact oneChain framing: replay and endpoint/count decisions inspect the same
    actual raw trace and graph, irrespective of the future replicate's suffix. -/
theorem one_chain_allocated_prefix (r : Request) (hc : SamplingCapacities r)
    (hv : CurveballNative.graphValid r.n r.edges = true)
    (allocated : Tape ((pairReserve r + subsetReserve r)*r.trades)) (suffix : List Bool) :
    oneChain r (allocated.val ++ suffix) =
      (oneChain r allocated.val).map (fun out => (out.1,out.2.1,suffix)) := by
  have hf := generate_allocated_prefix r hc r.trades r.edges hv allocated suffix
  unfold oneChain
  rw [hf]
  cases hg : generateTrace r r.trades r.edges allocated.val with
  | none => simp [hg]
  | some out =>
    obtain ⟨draws,generated,rest⟩ := out
    simp only [hg,Option.map_some]
    dsimp only [Bind.bind,Pure.pure]
    simp only [Option.bind_some]
    cases hr : CurveballNative.replay r.n r.edges draws with
    | none => simp [hr]
    | some replayed =>
      obtain ⟨last,count⟩ := replayed
      simp only [hr,Option.bind_some]
      by_cases h : last = generated ∧ count = r.trades <;> simp [h]

#print axioms generate_allocated_prefix
#print axioms one_chain_allocated_prefix
end
end CurveballVerified
