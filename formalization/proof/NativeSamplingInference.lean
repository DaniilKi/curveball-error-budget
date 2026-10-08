import NativeInference
import NativeJointDomination
import NativeBatchStatistics
import NativePlanJoins
import NativeGuardCapacity

/- SOURCE-ONLY DRAFT. Complete proof body supplied, no claimed acceptance.
   Pending analytical dependency replay and deterministic guard/model joins.
   No TV, exchangeability or desired inference bound is a hypothesis. -/
namespace CurveballVerified
noncomputable section
open OAI.Problem315 CurveballNativeSampling
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem curveball_row_eq_finite {n : Nat} {d : Fin n → Nat} (hn : 2 ≤ n) :
    curveballRow (d := d) hn = finiteCurveballRow hn := by
  funext G
  apply FiniteLaw.ext_mass
  rfl

theorem ideal_graph_experiment_eq_curveball (r : Request) (d : Fin r.n → Nat)
    [Nonempty (GraphState r.n d)] (hc : SamplingCapacities r) (b : Nat) :
    idealGraphExperiment r d hc b = curveballExperiment hc.nTwo r.trades b := by
  unfold idealGraphExperiment curveballExperiment
  simp only [curveball_row_eq_finite] <;> rfl

def nativeGraphReject (r : Request) (d : Fin r.n → Nat) :
    GraphState r.n d × Option (BatchSpace (GraphState r.n d) r.b) → Prop :=
  fun x => match x.2 with
    | none => False
    | some ys => CurveballNative.rankCheck r.b (exceedCount r.b graphTriangles (x.1,ys))
        r.etaNum r.etaDen r.alphaNum r.alphaDen = true

/-- The actual native fair-bit experiment's completed rejection probability is
    bounded by the requested alpha. Actual capped draws, trace, replay, fresh
    ordered batches and runtime statistic identities have separate accepted
    concrete proofs; the ordinary analytical bound is derived from its integer
    certificate and true IID rank argument, rather than assumed here.
    Uniform observation is the explicit null model of nativeGraphExperiment.
    Numeric capacities and deterministic representation/count identities remain
    intermediate joins until discharged from the executable's guards. -/
theorem actual_native_rank_bound (r : Request) (d : Fin r.n → Nat)
    [Nonempty (GraphState r.n d)]
    (models : GraphState r.n d → NativeModel r.n d)
    (hmodels : ∀ G, (models G).project = G)
    (hlimits : withinLimits r = true) (hplan : arithmeticPlan r = true)
    (hedges : r.edges.length = (∑ v,d v)/2) :
    eventMass (nativeGraphExperiment r d models r.b) (nativeGraphReject r d) ≤
      (r.alphaNum : ℝ)/r.alphaDen := by
  let hc := native_limits_sampling_capacities r hlimits
  obtain ⟨hn,_⟩ := native_limits_dimensions r hlimits
  obtain ⟨he,ha,_,_,hcut,_⟩ := native_plan_scalars r hplan
  let E : BatchSpace (GraphState r.n d) (r.b+1) → Prop := fun x =>
    CurveballNative.rankCheck r.b (exceedCount r.b graphTriangles x)
      r.etaNum r.etaDen r.alphaNum r.alphaDen = true
  have hdom := actual_joint_event_dominated r d hc models hmodels r.b E
  have hideal := native_curveball_inference_bound hn
    (native_plan_degree_budget r d hplan hedges) r.b r.etaNum r.etaDen
    r.alphaNum r.alphaDen he ha (Nat.le_of_lt hcut)
    (native_plan_joint_error r hplan) graphTriangles
  rw [ideal_graph_experiment_eq_curveball] at hdom
  have hideal' : @eventMass _ _ (curveballExperiment (d := d) hc.nTwo r.trades r.b) E
      (fun x => Classical.propDecidable (E x)) ≤
      (r.alphaNum : ℝ)/r.alphaDen := by
    convert hideal using 1 <;>
      exact congrArg (fun dec : DecidablePred E =>
        @eventMass _ _ (curveballExperiment (d := d) hc.nTwo r.trades r.b) E dec)
        (Subsingleton.elim _ _)
  convert hdom.trans hideal' using 1
  unfold eventMass
  apply Finset.sum_congr rfl
  intro x hx
  cases h : x.2 <;> simp [nativeGraphReject, E, h]

/-- A concrete completed raw output uses exactly the same rank decision, with
    the native observed statistic and all computed replicate scores. -/
theorem native_completed_rank_identity (r : Request) (d : Fin r.n → Nat)
    (s : NativeModel r.n d) (hs : s.edges = r.edges)
    (outs : List CurveballNative.Edges) (ys : BatchSpace (GraphState r.n d) r.b)
    (h : rawGraphBatch r.n d r.b outs = some ys) :
    CurveballNative.rankCheck r.b
      (((outs.map (CurveballNative.triangles r.n)).filter
        (fun t => decide (CurveballNative.triangles r.n r.edges ≤ t))).length)
      r.etaNum r.etaDen r.alphaNum r.alphaDen =
    CurveballNative.rankCheck r.b (exceedCount r.b graphTriangles (s.project,ys))
      r.etaNum r.etaDen r.alphaNum r.alphaDen := by
  have he := raw_graph_batch_exceed s r.b outs ys h
  rw [hs] at he
  rw [he]

#print axioms actual_native_rank_bound
#print axioms native_completed_rank_identity
end
end CurveballVerified
