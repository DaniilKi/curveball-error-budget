import ProbabilityProofBundle

namespace CurveballVerified
noncomputable section

/-- Padding and all unused rejected words are discarded at the agreed boundary. -/
theorem reserved_bits_refines {n : Nat} (hn : 0 < n) (width cap reserve : Nat)
    (hwidth : n ≤ 2 ^ width) (hreserve : width * cap ≤ reserve)
    (bits : BatchSpace (Fin width → Bool) cap) (padding suffix : List Bool)
    (hpadding : padding.length = reserve - width * cap) :
    CurveballNative.drawBelowReserved n width cap reserve
      ((bitTape width cap bits ++ padding) ++ suffix) =
      (cappedWords n (2 ^ width) cap (batchMap (@decodeBits width) cap bits)).map
        (fun out => (out.val,suffix)) := by
  have hlen : (bitTape width cap bits ++ padding).length = reserve := by
    rw [List.length_append,bitTape_length,hpadding]
    omega
  rw [CurveballNative.drawBelowReserved_prefix _ _ _ _ _ _ hlen hreserve]
  have ht : (bitTape width cap bits ++ padding).take (width * cap) = bitTape width cap bits := by
    rw [← bitTape_length width cap bits]
    exact List.take_append_length
  rw [ht,CurveballNative.drawBelow_eq]
  have hbad : ¬ (n = 0 ∨ 2 ^ width < n) := by omega
  simp only [drawBelow,hbad,ite_false]
  have h := congrArg (Option.map (fun value => (value,suffix)))
    (bitTape_cappedWords n width cap bits)
  simpa only [Option.map_map,Function.comp_def] using h

def reservedBitsOutput (n width cap reserve : Nat) (bits : List Bool) : Option (Fin n) :=
  (CurveballNative.drawBelowReserved n width cap reserve bits).bind fun out =>
    if h : out.1 < n then some ⟨out.1,h⟩ else none

theorem reservedBitsOutput_refines {n : Nat} (hn : 0 < n) (width cap reserve : Nat)
    (hwidth : n ≤ 2 ^ width) (hreserve : width * cap ≤ reserve)
    (bits : BatchSpace (Fin width → Bool) cap) (padding : List Bool)
    (hpadding : padding.length = reserve - width * cap) :
    reservedBitsOutput n width cap reserve (bitTape width cap bits ++ padding) =
      cappedWords n (2 ^ width) cap (batchMap (@decodeBits width) cap bits) := by
  have h := reserved_bits_refines hn width cap reserve hwidth hreserve bits padding [] hpadding
  simp only [List.append_nil] at h
  cases hw : cappedWords n (2 ^ width) cap (batchMap (@decodeBits width) cap bits) with
  | none =>
    simp only [hw,Option.map_none] at h
    simp [reservedBitsOutput,h]
  | some value =>
    simp only [hw,Option.map_some] at h
    simp [reservedBitsOutput,h,value.isLt]

/-- Exact executed reserved-draw law. Padding is arbitrary and never interpreted. -/
theorem actual_reserved_bit_law {n : Nat} (hn : 0 < n) (width cap reserve : Nat)
    (hwidth : n ≤ 2 ^ width) (hreserve : width * cap ≤ reserve)
    (padding : List Bool) (hpadding : padding.length = reserve - width * cap) :
    mapLaw (batchLaw (fun _ => uniformLaw (Fin width → Bool)) cap)
      (fun bits => reservedBitsOutput n width cap reserve (bitTape width cap bits ++ padding)) =
      cappedWordLaw n (2 ^ width) cap := by
  have hf : (fun bits => reservedBitsOutput n width cap reserve
      (bitTape width cap bits ++ padding)) =
      (fun bits => fixedBitsOutput n width cap (bitTape width cap bits)) := by
    funext bits
    rw [reservedBitsOutput_refines hn width cap reserve hwidth hreserve bits padding hpadding,
      fixedBitsOutput_refines hn width cap hwidth bits]
  rw [hf]
  exact actual_capped_bit_law hn width cap hwidth

/-- The entropy premise is an explicit product law; this supplies the next draw's
    untouched suffix even when the prefix draw aborts. -/
theorem reserved_suffix_independent {n : Nat} (hn : 0 < n) (width cap reserve : Nat)
    (hwidth : n ≤ 2 ^ width) (hreserve : width * cap ≤ reserve)
    (padding : List Bool) (hpadding : padding.length = reserve - width * cap)
    {S : Type} [Fintype S] [DecidableEq S] (suffixLaw : FiniteLaw S) :
    mapLaw (productLaw (batchLaw (fun _ => uniformLaw (Fin width → Bool)) cap) suffixLaw)
      (fun x => (reservedBitsOutput n width cap reserve
        (bitTape width cap x.1 ++ padding),x.2)) =
      productLaw (cappedWordLaw n (2 ^ width) cap) suffixLaw := by
  have h := independent_suffix
    (batchLaw (fun _ => uniformLaw (Fin width → Bool)) cap) suffixLaw
    (fun bits => reservedBitsOutput n width cap reserve (bitTape width cap bits ++ padding))
  rw [actual_reserved_bit_law hn width cap reserve hwidth hreserve padding hpadding] at h
  exact h

#print axioms reserved_bits_refines
#print axioms actual_reserved_bit_law
#print axioms reserved_suffix_independent
end
end CurveballVerified
