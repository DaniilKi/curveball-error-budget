import NativeByteTapeLaw

/- SOURCE-ONLY DRAFT. No compilation/acceptance claimed. -/
namespace CurveballVerified
noncomputable section
open OAI.Problem315 CurveballNativeSampling
attribute [local instance] Classical.propDecidable

theorem native_entropy_bits_length (r : Request) :
    8 * entropyBytes r = ((pairReserve r + subsetReserve r)*r.trades)*r.b := by
  have hallocation : 8*((pairReserve r + subsetReserve r)/8) =
      pairReserve r + subsetReserve r := by
    unfold pairReserve subsetReserve
    omega
  unfold entropyBytes
  calc
    8 * (r.b*r.trades*((pairReserve r+subsetReserve r)/8)) =
      r.b*r.trades*(8*((pairReserve r+subsetReserve r)/8)) := by ring
    _ = ((pairReserve r+subsetReserve r)*r.trades)*r.b := by rw [hallocation]; ring

/-- The exact runtime byte converter feeds exactly its complete reserved batch
    tape; every byte is used in little-endian order. Uniform independent bytes
    are an explicit entropy model, not a conclusion about an operating system. -/
theorem native_byte_batch_law (r : Request) (d : Fin r.n → Nat) :
    mapLaw (batchLaw (fun _ => uniformLaw (Fin 256)) (entropyBytes r))
      (fun xs => batchProjection r d r.b (bytesBits (bytesFromBlocks (entropyBytes r) xs))) =
    mapLaw (uniformLaw (Tape (((pairReserve r+subsetReserve r)*r.trades)*r.b)))
      (fun tape => batchProjection r d r.b tape.val) := by
  rw [native_bytesBits_pushforward]
  have he := map_uniform_bijection (tapeCongr (native_entropy_bits_length r))
  rw [← he,mapLaw_comp]
  rfl

theorem actual_byte_batch_dominated (r : Request) (d : Fin r.n → Nat)
    (hc : SamplingCapacities r) (s : NativeModel r.n d) (hs : s.edges = r.edges)
    (ys : BatchSpace (GraphState r.n d) r.b) :
    (mapLaw (batchLaw (fun _ => uniformLaw (Fin 256)) (entropyBytes r))
      (fun xs => batchProjection r d r.b (bytesBits (bytesFromBlocks (entropyBytes r) xs)))).mass (some ys) ≤
    (batchLaw (fun _ => iterateKernel (finiteCurveballRow hc.nTwo) s.project r.trades) r.b).mass ys := by
  rw [native_byte_batch_law]
  exact actual_batch_dominated r d hc s hs r.b ys

#print axioms native_entropy_bits_length
#print axioms native_byte_batch_law
#print axioms actual_byte_batch_dominated
end
end CurveballVerified
