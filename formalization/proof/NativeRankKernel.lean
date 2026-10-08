import NatFinSubsets
import PairFiberFiniteBridge
import CurveballTransitionCore
import FiniteTapeLaw

namespace CurveballVerified
noncomputable section
open scoped BigOperators
open OAI.Problem315 OAI.Problem315.PairFiber CurveballSubsetVerified
attribute [local instance] Classical.propDecidable

def nativeSubsetEquiv {n : Nat} {es : CurveballNative.Edges}
    {C : CanonicalGraph n} (href : EdgeRefines es C)
    {d : Fin n → Nat} (G : GraphState n d)
    (hG : C.toSimpleGraph = G.val) (i j : Fin n) :
    Fin ((CurveballNative.exclusive n es i.val j.val).length.choose
      (CurveballNative.left n es i.val j.val).length) ≃ OAI.Problem315.PairFiber.Assignment G.val i j :=
  (subsetAssignmentEquiv (List.nodup_range.filter _)
    (List.pairwise_le_range.filter _) (CurveballNative.left n es i.val j.val).length).trans
      (nativeAssignmentEquiv href G hG i j)

theorem nativeSubsetEquiv_val {n : Nat} {es : CurveballNative.Edges}
    {C : CanonicalGraph n} (href : EdgeRefines es C)
    {d : Fin n → Nat} (G : GraphState n d)
    (hG : C.toSimpleGraph = G.val) (i j : Fin n)
    (rank : Fin ((CurveballNative.exclusive n es i.val j.val).length.choose
      (CurveballNative.left n es i.val j.val).length)) :
    (nativeSubsetEquiv href G hG i j rank).val =
      chosenSet n (subsetAt (CurveballNative.exclusive n es i.val j.val)
        (CurveballNative.left n es i.val j.val).length rank).val := by
  change finSetOfNat n (_ : List Nat).toFinset = _
  exact finSetOfNat_list n _

def nativeRankFiberEquiv {n : Nat} {es : CurveballNative.Edges}
    {C : CanonicalGraph n} (href : EdgeRefines es C)
    {d : Fin n → Nat} (G : GraphState n d)
    (hG : C.toSimpleGraph = G.val) (i j : Fin n) (hij : i ≠ j) :
    Fin ((CurveballNative.exclusive n es i.val j.val).length.choose
      (CurveballNative.left n es i.val j.val).length) ≃
      ↥(PairResampling.fiberStates {i,j} G) :=
  (nativeSubsetEquiv href G hG i j).trans (resamplingFiberEquiv G i j hij).symm

/-- A finite observer of the actual native trade return value. Both validation
    guards below are proved redundant for every decoded rank on a valid graph. -/
def nativeTradeState (n : Nat) (d : Fin n → Nat) (es : CurveballNative.Edges)
    (i j : Nat) (chosen : List Nat) : Option (GraphState n d) :=
  (CurveballNative.trade n es i j chosen).bind fun out =>
    if hv : CurveballNative.graphValid n out = true then
      let H := canonicalOfNative n out hv
      if hd : Realizes n d H.toSimpleGraph then some ⟨H.toSimpleGraph,hd⟩ else none
    else none

def nativeRankOutput (n : Nat) (d : Fin n → Nat) (es : CurveballNative.Edges)
    (i j rank : Nat) : Option (GraphState n d) :=
  (CurveballNative.unrankSubset (CurveballNative.exclusive n es i j)
    (CurveballNative.left n es i j).length rank).bind
      (nativeTradeState n d es i j)

theorem nativeRankOutput_at {n : Nat} {es : CurveballNative.Edges}
    {C : CanonicalGraph n} (href : EdgeRefines es C)
    (hg : CurveballNative.graphValid n es = true)
    {d : Fin n → Nat} (G : GraphState n d)
    (hG : C.toSimpleGraph = G.val) (i j : Fin n) (hij : i ≠ j)
    (rank : Fin ((CurveballNative.exclusive n es i.val j.val).length.choose
      (CurveballNative.left n es i.val j.val).length)) :
    nativeRankOutput n d es i.val j.val rank.val =
      some (nativeRankFiberEquiv href G hG i j hij rank).val := by
  let chosen := (subsetAt (CurveballNative.exclusive n es i.val j.val)
    (CurveballNative.left n es i.val j.val).length rank).val
  have hu := unrankSubset_at (CurveballNative.exclusive n es i.val j.val)
    (CurveballNative.left n es i.val j.val).length rank
  obtain ⟨chosen',out,hu',ht,H,href',hT,hgraph,hdeg⟩ :=
    decoded_trade_refines href hg i j hij rank
  have hchosen : chosen' = chosen := Option.some.inj (hu'.symm.trans hu)
  subst chosen'
  have hv := CurveballNative.trade_success_valid ht
  have hcanon : (canonicalOfNative n out hv).toSimpleGraph = H.toSimpleGraph := by
    ext u v
    exact (native_adjacent_refines (canonicalOfNative_refines n out hv) u v).symm.trans
      (native_adjacent_refines href' u v)
  have hd : Realizes n d (canonicalOfNative n out hv).toSimpleGraph := by
    intro v
    rw [hcanon,← degree_refines H,hdeg,degree_refines C,hG]
    exact G.property v
  have hf : (nativeRankFiberEquiv href G hG i j hij rank).val.val =
      trade G.val i j hij (nativeSubsetEquiv href G hG i j rank).val
        (nativeSubsetEquiv href G hG i j rank).property.1 := by
    change ((resamplingFiberEquiv G i j hij).symm
      (nativeSubsetEquiv href G hG i j rank)).val.val = _
    rw [resamplingFiberEquiv_symm_val,stateFiberEquiv_symm_apply]
  simp only [nativeSubsetEquiv_val] at hf
  simp only [hG] at hgraph
  have he : (canonicalOfNative n out hv).toSimpleGraph =
      (nativeRankFiberEquiv href G hG i j hij rank).val.val :=
    hcanon.trans (hgraph.trans hf.symm)
  have hts : nativeTradeState n d es i.val j.val chosen =
      some (nativeRankFiberEquiv href G hG i j hij rank).val := by
    unfold nativeTradeState
    rw [ht]
    simp only [Option.bind_some]
    rw [dif_pos hv,dif_pos hd]
    apply congrArg some
    exact Subtype.ext he
  unfold nativeRankOutput
  rw [hu']
  exact hts

def fiberLaw {n : Nat} {d : Fin n → Nat} (a : Finset (Fin n))
    (G : GraphState n d) : FiniteLaw (GraphState n d) := by
  classical
  letI : Nonempty ↥(PairResampling.fiberStates a G) :=
    ⟨⟨G,PairResampling.self_mem_fiberStates a G⟩⟩
  exact mapLaw (uniformLaw ↥(PairResampling.fiberStates a G)) Subtype.val

theorem fiberLaw_mass {n : Nat} {d : Fin n → Nat} (a : Finset (Fin n))
    (G H : GraphState n d) : (fiberLaw a G).mass H = pairKernel a G H := by
  classical
  by_cases hh : H ∈ PairResampling.fiberStates a G
  · have hf : Finset.univ.filter
        (fun x : ↥(PairResampling.fiberStates a G) => x.val = H) = {⟨H,hh⟩} := by
      ext x
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
      constructor
      · intro h; exact Subtype.ext h
      · intro h; exact congrArg Subtype.val h
    change (∑ x : ↥(PairResampling.fiberStates a G),
      if x.val = H then 1 / (Fintype.card ↥(PairResampling.fiberStates a G) : ℝ) else 0) = _
    rw [← Finset.sum_filter,hf]
    simp only [Finset.sum_singleton,Fintype.card_coe,pairKernel,
      (PairResampling.mem_fiberStates a G H).mp hh,ite_true]
  · have hz (x : ↥(PairResampling.fiberStates a G)) : x.val ≠ H := by
      intro he
      exact hh (he ▸ x.property)
    simp [fiberLaw,mapLaw,uniformLaw,hz,pairKernel,
      (PairResampling.mem_fiberStates a G H).not.mp hh]

theorem native_rank_uniform_fiber {n : Nat} {es : CurveballNative.Edges}
    {C : CanonicalGraph n} (href : EdgeRefines es C)
    {d : Fin n → Nat} (G : GraphState n d)
    (hG : C.toSimpleGraph = G.val) (i j : Fin n) (hij : i ≠ j)
    [NeZero ((CurveballNative.exclusive n es i.val j.val).length.choose
      (CurveballNative.left n es i.val j.val).length)] :
    mapLaw (uniformLaw (Fin ((CurveballNative.exclusive n es i.val j.val).length.choose
      (CurveballNative.left n es i.val j.val).length)))
      (fun rank => (nativeRankFiberEquiv href G hG i j hij rank).val) =
      fiberLaw {i,j} G := by
  letI : Nonempty ↥(PairResampling.fiberStates {i,j} G) :=
    ⟨⟨G,PairResampling.self_mem_fiberStates {i,j} G⟩⟩
  change mapLaw _ (Subtype.val ∘ nativeRankFiberEquiv href G hG i j hij) = _
  rw [← mapLaw_comp,map_uniform_bijection]
  rfl

#print axioms nativeRankOutput_at
#print axioms fiberLaw_mass
#print axioms native_rank_uniform_fiber
end
end CurveballVerified
