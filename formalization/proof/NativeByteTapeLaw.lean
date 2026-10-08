import NativeBatchStatistics
import Init.Data.ByteArray.Lemmas
import Init.Data.UInt.Lemmas

/- SOURCE-ONLY DRAFT. Compiler slot belongs to builder. No acceptance claimed.
   All finite checks below use kernel `decide`, never native_decide or testing. -/
namespace CurveballVerified
noncomputable section
open CurveballNativeSampling

/-- The runtime loop visits bytes in increasing index order. -/
theorem byteArray_toList_loop (bytes : ByteArray) (i : Nat) (acc : List UInt8) :
    ByteArray.toList.loop bytes i acc = acc.reverse ++ bytes.data.toList.drop i := by
  rw [ByteArray.toList.loop]
  by_cases hi : i < bytes.size
  · simp only [hi,ite_true]
    rw [byteArray_toList_loop bytes (i+1) (bytes.get! i :: acc)]
    rw [List.reverse_cons,List.append_assoc,List.singleton_append]
    have hlen : i < bytes.data.toList.length := by
      simpa only [Array.length_toList,ByteArray.size_data] using hi
    have hget : bytes.get! i = bytes.data.toList[i]'hlen := by
      cases bytes with
      | mk data =>
        change data[i]! = data[i]'hi
        exact getElem!_pos data i hi
    rw [List.drop_eq_getElem_cons hlen,hget]
  · have hle : bytes.data.toList.length ≤ i := by
      simpa only [Array.length_toList,ByteArray.size_data] using Nat.le_of_not_gt hi
    simp only [hi,ite_false,List.drop_eq_nil_of_le hle,List.append_nil]
termination_by bytes.size - i
decreasing_by omega

theorem byteArray_toList_eq_data (bytes : ByteArray) :
    bytes.toList = bytes.data.toList := by
  simpa only [ByteArray.toList,List.reverse_nil,List.nil_append,List.drop_zero] using
    byteArray_toList_loop bytes 0 []

def byteVectorBits (x : Fin 256) : Fin 8 → Bool :=
  fun i => decide ((x.val / 2^i.val) % 2 = 1)

/-- Exhaustive finite equality checked by the kernel, for all 256 byte values. -/
theorem decode_byte_vector (x : Fin 256) :
    (decodeBits (byteVectorBits x)).val = x.val := by
  revert x
  decide

theorem byteVectorBits_bijective : Function.Bijective byteVectorBits := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro x y h
    apply Fin.ext
    rw [← decode_byte_vector x,← decode_byte_vector y,h]
  · simp

def byteBitsEquiv : Fin 256 ≃ (Fin 8 → Bool) :=
  Equiv.ofBijective byteVectorBits byteVectorBits_bijective

def bytesFromBlocks (b : Nat) (xs : BatchSpace (Fin 256) b) : ByteArray :=
  ((batchToList b xs).map fun x => UInt8.ofNatLT x.val x.isLt).toByteArray

theorem bytesFromBlocks_size (b : Nat) (xs : BatchSpace (Fin 256) b) :
    (bytesFromBlocks b xs).size = b := by
  induction b with
  | zero => simp [bytesFromBlocks,batchToList]
  | succ b ih =>
    simpa only [bytesFromBlocks,List.size_toByteArray,List.length_map,batchToList,
      List.length_cons] using congrArg (fun k => k+1) (ih xs.2)

theorem byte_vector_list (x : Fin 256) :
    (List.range 8).map (fun bit => decide ((x.val / 2^bit) % 2 = 1)) =
    List.ofFn (byteVectorBits x) := by
  rw [List.ofFn_eq_map,range_eq_finRange_values,List.map_map]
  rfl

theorem bytesBits_bytesFromBlocks (b : Nat) (xs : BatchSpace (Fin 256) b) :
    bytesBits (bytesFromBlocks b xs) = bitTape 8 b (batchMap byteVectorBits b xs) := by
  unfold bytesBits bytesFromBlocks
  rw [byteArray_toList_eq_data,List.toList_data_toByteArray]
  induction b with
  | zero => rfl
  | succ b ih =>
    simp only [batchToList,List.map_cons,List.flatMap_cons,UInt8.toNat_ofNatLT,
      byte_vector_list,batchMap,bitTape]
    rw [ih xs.2]

def byteTapeEquiv (b : Nat) : BatchSpace (Fin 256) b ≃ Tape (8*b) :=
  (batchEquiv byteBitsEquiv b).trans (blockTapeEquiv 8 b)

theorem byteTapeEquiv_val (b : Nat) (xs : BatchSpace (Fin 256) b) :
    (byteTapeEquiv b xs).val = bytesBits (bytesFromBlocks b xs) := by
  change (blockTapeEquiv 8 b (batchEquiv byteBitsEquiv b xs)).val = _
  rw [batchEquiv_apply]
  change (blockTapeEquiv 8 b (batchMap byteVectorBits b xs)).val = _
  rw [blockTapeEquiv_val,bytesBits_bytesFromBlocks]

/-- Uniform independent complete byte vectors induce exactly the complete fair
    bit tape used by the accepted actual native generation/batch laws. This
    proves byte conversion; it does not assume or prove OS entropy quality. -/
theorem uniform_native_byte_tape_law (b : Nat) :
    mapLaw (batchLaw (fun _ => uniformLaw (Fin 256)) b) (byteTapeEquiv b) =
      uniformLaw (Tape (8*b)) := by
  rw [batchLaw_uniform]
  exact map_uniform_bijection (byteTapeEquiv b)

theorem native_bytesBits_pushforward (b : Nat) {α : Type} [Fintype α] [DecidableEq α]
    (f : List Bool → α) :
    mapLaw (batchLaw (fun _ => uniformLaw (Fin 256)) b)
      (fun xs => f (bytesBits (bytesFromBlocks b xs))) =
    mapLaw (uniformLaw (Tape (8*b))) (fun tape => f tape.val) := by
  rw [← uniform_native_byte_tape_law,mapLaw_comp]
  apply congrArg (mapLaw (batchLaw (fun _ => uniformLaw (Fin 256)) b))
  funext xs
  simp only [Function.comp_def,byteTapeEquiv_val]

#print axioms byteArray_toList_eq_data
#print axioms decode_byte_vector
#print axioms byteVectorBits_bijective
#print axioms bytesBits_bytesFromBlocks
#print axioms uniform_native_byte_tape_law
#print axioms native_bytesBits_pushforward
end
end CurveballVerified
