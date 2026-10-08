import FiniteTapeLaw

namespace CurveballVerified
noncomputable section

/-- The finite range guard observes the exact raw draw and discards no valid
    successful output. The suffix is exactly the fixed reservation boundary. -/
theorem reserved_observation (n width cap reserve : Nat)
    (allocated suffix : List Bool) (hlen : allocated.length = reserve)
    (hr : width * cap ≤ reserve) :
    CurveballNative.drawBelowReserved n width cap reserve (allocated ++ suffix) =
      (reservedBitsOutput n width cap reserve allocated).map
        (fun rank => (rank.val,suffix)) := by
  have ha := CurveballNative.drawBelowReserved_prefix n width cap reserve
    allocated [] hlen hr
  simp only [List.append_nil] at ha
  rw [CurveballNative.drawBelowReserved_prefix n width cap reserve allocated suffix hlen hr]
  cases hs : CurveballNative.drawBelow n width cap (allocated.take (width*cap)) with
  | none => simp [reservedBitsOutput,ha,hs]
  | some out =>
    have hb : out.1 < n :=
      CurveballVerified.drawBelow_range ((CurveballNative.drawBelow_eq _ _ _ _) ▸ hs)
    simp [reservedBitsOutput,ha,hs,hb]

#print axioms reserved_observation
end
end CurveballVerified
