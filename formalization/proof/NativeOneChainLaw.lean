import NativeGeneratedTraceLaw

namespace CurveballVerified
noncomputable section
open OAI.Problem315 CurveballNativeSampling
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- DRAFT: suppressing actual successful outputs cannot increase any successful
    event mass. This keeps none; it does not normalize successful executions. -/
theorem partial_success_mass_mono {Ω α : Type} [Fintype Ω] [Fintype α]
    [DecidableEq α] (law : FiniteLaw Ω) (actual candidate : Ω → Option α)
    (h : ∀ bits y, actual bits = some y → candidate bits = some y) (y : α) :
    (mapLaw law actual).mass (some y) ≤ (mapLaw law candidate).mass (some y) := by
  unfold mapLaw
  apply Finset.sum_le_sum
  intro bits hb
  by_cases ha : actual bits = some y
  · simp only [ha,h bits y ha,ite_true]
    exact le_rfl
  · by_cases hc : candidate bits = some y
    · simp only [ha,hc,ite_false,ite_true]
      exact law.nonnegative bits
    · simp [ha,hc]

def oneChainProjection (r : Request) (d : Fin r.n → Nat) (bits : List Bool) :
    Option (GraphState r.n d) :=
  (oneChain r bits).bind fun out =>
    (observeNativeModel r.n d out.1).map NativeModel.project

/-- The actual replay/count/endpoint guards only suppress generation outputs.
    Successful graph projection is the exact generateTrace endpoint, without a
    second graph fold proof or any assumption about its law. -/
theorem one_chain_projection_implies_generated (r : Request) (d : Fin r.n → Nat)
    (bits : List Bool) (H : GraphState r.n d)
    (h : oneChainProjection r d bits = some H) :
    generatedProjection r d r.trades r.edges bits = some H := by
  unfold oneChainProjection oneChain at h
  cases hg : generateTrace r r.trades r.edges bits with
  | none => simp [hg] at h
  | some generated =>
    obtain ⟨draws,last,rest⟩ := generated
    simp only [hg] at h
    dsimp only [Bind.bind,Pure.pure] at h
    simp only [Option.bind_some] at h
    cases hr : CurveballNative.replay r.n r.edges draws with
    | none => simp [hr] at h
    | some replayed =>
      obtain ⟨out,count⟩ := replayed
      simp only [hr,Option.bind_some] at h
      split_ifs at h with hgate
      · simp only [Option.bind_some] at h
        have he : out = last := hgate.1
        subst out
        simpa only [generatedProjection,hg,Option.bind_some] using h
      · simp at h

/-- Complete uniform entropy through the ACTUAL oneChain, including its actual
    replay checks, is dominated by the existing transition power. -/
theorem actual_one_chain_dominated (r : Request) (d : Fin r.n → Nat)
    (hc : SamplingCapacities r) (s : NativeModel r.n d) (hs : s.edges = r.edges)
    (H : GraphState r.n d) :
    (mapLaw (uniformLaw (Tape ((pairReserve r + subsetReserve r)*r.trades)))
      (fun tape => oneChainProjection r d tape.val)).mass (some H) ≤
        (transition r.n d ^ r.trades) s.project H := by
  have hm := partial_success_mass_mono
    (uniformLaw (Tape ((pairReserve r + subsetReserve r)*r.trades)))
    (fun tape => oneChainProjection r d tape.val)
    (fun tape => generatedProjection r d r.trades s.edges tape.val)
    (fun tape H h => by
      simpa only [hs] using one_chain_projection_implies_generated r d tape.val H h) H
  exact hm.trans (actual_generated_trace_dominated r d hc s r.trades H)

#print axioms partial_success_mass_mono
#print axioms one_chain_projection_implies_generated
#print axioms actual_one_chain_dominated
end
end CurveballVerified
