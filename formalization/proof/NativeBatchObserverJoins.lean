import NativeCanonicalCounting
import NativeReplayProof
import NativeBatchLaw

namespace CurveballVerified
noncomputable section
open OAI.Problem315 CurveballNativeSampling
attribute [local instance] Classical.propDecidable

/-- The actual generated draw list replays to its actual generated endpoint,
with all attempted trades counted. This is a deterministic runtime identity. -/
theorem generateTrace_success_replay (r : Request) {t : Nat}
    {es out : CurveballNative.Edges} {bits rest : List Bool}
    {draws : List CurveballNative.Draw}
    (hgen : generateTrace r t es bits = some (draws,out,rest)) :
    CurveballNative.replay r.n es draws = some (out,t) ∧ draws.length = t := by
  induction t generalizing es out bits rest draws with
  | zero =>
    simp only [generateTrace] at hgen
    cases hgen
    exact ⟨rfl,rfl⟩
  | succ t ih =>
    cases hd : draw r es bits with
    | none => simp [generateTrace,hd] at hgen
    | some drawn =>
      obtain ⟨dr,unused⟩ := drawn
      cases ht : CurveballNative.trade r.n es dr.first dr.second dr.chosen with
      | none => simp [generateTrace,hd,ht] at hgen
      | some next =>
        cases hg : generateTrace r t next unused with
        | none => simp [generateTrace,hd,ht,hg] at hgen
        | some generated =>
          obtain ⟨ds,last,suffix⟩ := generated
          simp [generateTrace,hd,ht,hg] at hgen
          obtain ⟨rfl,rfl,rfl⟩ := hgen
          obtain ⟨hreplay,hlen⟩ := ih hg
          exact ⟨by simp [CurveballNative.replay,ht,hreplay],by simp [hlen]⟩

/-- Arbitrary successful native replay from a valid model passes its observer.
This reuses accepted degree/validity refinement; no new upstream fold is used. -/
theorem native_replay_success_observer {n : Nat} {d : Fin n → Nat}
    (s : NativeModel n d) {draws : List CurveballNative.Draw}
    {out : CurveballNative.Edges} {count : Nat}
    (hrun : CurveballNative.replay n s.edges draws = some (out,count)) :
    ∃ next : NativeModel n d,
      next.edges = out ∧ observeNativeModel n d out = some next := by
  let C := canonicalOfNative n s.edges s.valid
  obtain ⟨_,H,hrep,hv,hdeg⟩ := native_replay_refines
    (canonicalOfNative_refines n s.edges s.valid) s.valid hrun
  have heq : (canonicalOfNative n out hv).toSimpleGraph = H.toSimpleGraph :=
    native_canonical_eq_of_refines (canonicalOfNative_refines n out hv) hrep
  have hd : Realizes n d (canonicalOfNative n out hv).toSimpleGraph := by
    intro v
    rw [heq,← degree_refines H,hdeg,degree_refines C]
    exact s.realizes v
  exact ⟨⟨out,hv,hd⟩,rfl,by simp [observeNativeModel,hv,hd]⟩

theorem generateTrace_success_observer (r : Request) (d : Fin r.n → Nat)
    (s : NativeModel r.n d) {t : Nat} {out : CurveballNative.Edges}
    {bits rest : List Bool} {draws : List CurveballNative.Draw}
    (hgen : generateTrace r t s.edges bits = some (draws,out,rest)) :
    ∃ next : NativeModel r.n d,
      next.edges = out ∧ observeNativeModel r.n d out = some next :=
  native_replay_success_observer s (generateTrace_success_replay r hgen).1

theorem oneChain_success_observer (r : Request) (d : Fin r.n → Nat)
    (s : NativeModel r.n d) (hs : s.edges = r.edges)
    {bits rest : List Bool} {out : CurveballNative.Edges} {count : Nat}
    (hchain : oneChain r bits = some (out,count,rest)) :
    ∃ next : NativeModel r.n d,
      next.edges = out ∧ observeNativeModel r.n d out = some next := by
  unfold oneChain at hchain
  cases hg : generateTrace r r.trades r.edges bits with
  | none => simp [hg] at hchain
  | some generated =>
    obtain ⟨draws,last,unused⟩ := generated
    simp only [hg] at hchain
    dsimp only [Bind.bind,Pure.pure] at hchain
    simp only [Option.bind_some] at hchain
    cases hr : CurveballNative.replay r.n r.edges draws with
    | none => simp [hr] at hchain
    | some replayed =>
      obtain ⟨actual,c⟩ := replayed
      simp only [hr,Option.bind_some] at hchain
      split_ifs at hchain with hgate
      · simp only [Option.some.injEq,Prod.mk.injEq] at hchain
        obtain ⟨rfl,rfl,rfl⟩ := hchain
        exact native_replay_success_observer s (by simpa only [hs] using hr)

/-- Every successful actual raw batch has a complete finite graph projection.
The runtime restarts every chain at r.edges; the same initial model is used in
the induction. No successfully rendered graph vector is silently discarded. -/
theorem batch_success_observer (r : Request) (d : Fin r.n → Nat)
    (s : NativeModel r.n d) (hs : s.edges = r.edges)
    {b : Nat} {bits rest : List Bool} {outs : List CurveballNative.Edges} {count : Nat}
    (hbatch : batch r b bits = some (outs,count,rest)) :
    ∃ ys : BatchSpace (GraphState r.n d) b, rawGraphBatch r.n d b outs = some ys := by
  induction b generalizing bits rest outs count with
  | zero =>
    simp only [batch] at hbatch
    cases hbatch
    exact ⟨(),rfl⟩
  | succ b ih =>
    cases hh : oneChain r bits with
    | none => simp [batch,hh] at hbatch
    | some head =>
      obtain ⟨first,c,unused⟩ := head
      cases ht : batch r b unused with
      | none => simp [batch,hh,ht] at hbatch
      | some tail =>
        obtain ⟨others,total,suffix⟩ := tail
        simp [batch,hh,ht] at hbatch
        obtain ⟨rfl,rfl,rfl⟩ := hbatch
        obtain ⟨next,_,hobs⟩ := oneChain_success_observer r d s hs hh
        obtain ⟨ys,hys⟩ := ih ht
        exact ⟨(next.project,ys),by simp [rawGraphBatch,hobs,hys,Option.map]⟩

#print axioms generateTrace_success_replay
#print axioms native_replay_success_observer
#print axioms generateTrace_success_observer
#print axioms oneChain_success_observer
#print axioms batch_success_observer
end
end CurveballVerified
