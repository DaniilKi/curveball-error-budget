import NativeReplay
import NativeTradeRefinement

namespace CurveballVerified

/-- Arbitrary successful replay retains its fixed graph universe, preserves
all labeled degrees, and counts every supplied attempted trade. -/
theorem native_replay_refines {n : Nat} {es out : CurveballNative.Edges}
    {G : CanonicalGraph n} (href : EdgeRefines es G)
    (hg : CurveballNative.graphValid n es = true)
    {draws : List CurveballNative.Draw} {count : Nat}
    (hrun : CurveballNative.replay n es draws = some (out,count)) :
    count = draws.length ∧ ∃ H : CanonicalGraph n,
      EdgeRefines out H ∧ CurveballNative.graphValid n out = true ∧
      ∀ v : Fin n, H.degree v = G.degree v := by
  induction draws generalizing es out G count with
  | nil =>
    simp only [CurveballNative.replay] at hrun
    cases hrun
    exact ⟨rfl,G,href,hg,fun _ => rfl⟩
  | cons d ds ih =>
    cases hs : CurveballNative.trade n es d.first d.second d.chosen with
    | none => simp [CurveballNative.replay,hs] at hrun
    | some next =>
      obtain ⟨J,hnext,hvalid,hdegree⟩ := native_step_success_refines href hs
      cases ht : CurveballNative.replay n next ds with
      | none => simp [CurveballNative.replay,hs,ht] at hrun
      | some result =>
        obtain ⟨last,c⟩ := result
        simp [CurveballNative.replay,hs,ht] at hrun
        obtain ⟨rfl,rfl⟩ := hrun
        obtain ⟨hcount,H,hout,hfinal,hdegrees⟩ := ih hnext hvalid ht
        refine ⟨by simp [hcount],H,hout,hfinal,?_⟩
        intro v
        exact (hdegrees v).trans (hdegree v)

#print axioms native_replay_refines

/-- Degree preservation stated directly for the executable input/output lists. -/
theorem native_replay_degrees {n : Nat} {es out : CurveballNative.Edges}
    (hg : CurveballNative.graphValid n es = true)
    {draws : List CurveballNative.Draw} {count : Nat}
    (hrun : CurveballNative.replay n es draws = some (out,count)) (v : Fin n) :
    CurveballNative.degree n out v.val = CurveballNative.degree n es v.val := by
  obtain ⟨_,H,hout,_,hdegree⟩ :=
    native_replay_refines (canonicalOfNative_refines n es hg) hg hrun
  rw [native_degree_refines hout,
    native_degree_refines (canonicalOfNative_refines n es hg)]
  exact hdegree v

#print axioms native_replay_degrees
end CurveballVerified
