import NativeEntropy
import RandomBits

namespace CurveballNative

theorem bitsValue_eq (bits : List Bool) :
    bitsValue bits = CurveballVerified.bitsValue bits := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp only [bitsValue, CurveballVerified.bitsValue, ih]

theorem drawBelowAux_eq (n width cap : Nat) (bits : List Bool) :
    drawBelowAux n width cap bits = CurveballVerified.drawBelowAux n width cap bits := by
  induction cap generalizing bits with
  | zero => rfl
  | succ cap ih =>
    simp only [drawBelowAux, CurveballVerified.drawBelowAux, bitsValue_eq, ih]

theorem drawBelow_eq (n width cap : Nat) (bits : List Bool) :
    drawBelow n width cap bits = CurveballVerified.drawBelow n width cap bits := by
  simp only [drawBelow, CurveballVerified.drawBelow, drawBelowAux_eq]

theorem drawBelowFixed_range {n width cap value : Nat} {bits rest : List Bool}
    (h : drawBelowFixed n width cap bits = some (value,rest)) : value < n := by
  unfold drawBelowFixed at h
  split_ifs at h with hlen
  cases hd : drawBelow n width cap (bits.take (width * cap)) with
  | none => simp [hd] at h
  | some out =>
    obtain ⟨x,left⟩ := out
    simp [hd] at h
    obtain ⟨rfl,rfl⟩ := h
    exact CurveballVerified.drawBelow_range ((drawBelow_eq _ _ _ _) ▸ hd)

theorem drawBelowFixed_suffix {n width cap value : Nat} {bits rest : List Bool}
    (h : drawBelowFixed n width cap bits = some (value,rest)) :
    rest = bits.drop (width * cap) := by
  unfold drawBelowFixed at h
  split_ifs at h with hlen
  cases hd : drawBelow n width cap (bits.take (width * cap)) with
  | none => simp [hd] at h
  | some out =>
    obtain ⟨x,left⟩ := out
    simpa [hd] using (congrArg (Option.map Prod.snd) h).symm

theorem drawBelowFixed_prefix (n width cap : Nat) (allocated suffix : List Bool)
    (hlen : allocated.length = width * cap) :
    drawBelowFixed n width cap (allocated ++ suffix) =
      (drawBelow n width cap allocated).map (fun out => (out.1,suffix)) := by
  have hshort : ¬ (allocated ++ suffix).length < width * cap := by
    simp only [List.length_append]
    omega
  have ht : (allocated ++ suffix).take (width * cap) = allocated := by
    rw [← hlen]
    exact List.take_append_length
  have hd : (allocated ++ suffix).drop (width * cap) = suffix := by
    rw [← hlen]
    exact List.drop_append_length
  simp only [drawBelowFixed,hshort,if_false,ht,hd]
  cases drawBelow n width cap allocated <;> rfl

theorem drawBelowReserved_range {n width cap reserve value : Nat} {bits rest : List Bool}
    (h : drawBelowReserved n width cap reserve bits = some (value,rest)) : value < n := by
  unfold drawBelowReserved at h
  split_ifs at h with hbad
  cases hd : drawBelow n width cap (bits.take (width * cap)) with
  | none => simp [hd] at h
  | some out =>
    obtain ⟨x,left⟩ := out
    simp [hd] at h
    obtain ⟨rfl,rfl⟩ := h
    exact CurveballVerified.drawBelow_range ((drawBelow_eq _ _ _ _) ▸ hd)

theorem drawBelowReserved_prefix (n width cap reserve : Nat) (allocated suffix : List Bool)
    (hlen : allocated.length = reserve) (hreserve : width * cap ≤ reserve) :
    drawBelowReserved n width cap reserve (allocated ++ suffix) =
      (drawBelow n width cap (allocated.take (width * cap))).map (fun out => (out.1,suffix)) := by
  have hbad : ¬ (reserve < width * cap ∨ (allocated ++ suffix).length < reserve) := by
    simp only [List.length_append]
    omega
  have ht : (allocated ++ suffix).take (width * cap) = allocated.take (width * cap) :=
    List.take_append_of_le_length (by omega)
  have hd : (allocated ++ suffix).drop reserve = suffix := by
    rw [← hlen]
    exact List.drop_append_length
  simp only [drawBelowReserved,hbad,if_false,ht,hd]
  cases drawBelow n width cap (allocated.take (width * cap)) <;> rfl

#print axioms bitsValue_eq
#print axioms drawBelowAux_eq
#print axioms drawBelow_eq
#print axioms drawBelowFixed_range
#print axioms drawBelowFixed_suffix
#print axioms drawBelowFixed_prefix
#print axioms drawBelowReserved_range
#print axioms drawBelowReserved_prefix
end CurveballNative
