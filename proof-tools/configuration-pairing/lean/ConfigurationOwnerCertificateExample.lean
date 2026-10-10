import ConfigurationOwnerCertificate
namespace ConfigurationPairing.OwnerCertificateExamples
open ConfigurationPairing

namespace retained_edge
def fixedEdges : List (Fin 4 × Fin 4) := [(0,1)]
def outputEdges : List (Fin 4 × Fin 4) := [(0,1),(0,2),(1,3)]
def F := edgeListGraph fixedEdges
def G := edgeListGraph outputEdges
instance fixedAdjDecidable : DecidableRel F.Adj := edgeListGraphDecidable fixedEdges
instance outputAdjDecidable : DecidableRel G.Adj := edgeListGraphDecidable outputEdges
def d : Fin 4 → Nat := fun v => match v.val with
  | 0 => 2
  | 1 => 2
  | 2 => 1
  | _ => 1
def s : Fin 4 → Nat := fun v => match v.val with
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | _ => 1
def owners : Fin 2 × Bool → Fin 4 := fun z => match (pairIndex 2 z).val with
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | _ => 3
def lift : Fin 2 × Bool → Stub s := fun z => match (pairIndex 2 z).val with
  | 0 => ⟨0,⟨0,by decide⟩⟩
  | 1 => ⟨2,⟨0,by decide⟩⟩
  | 2 => ⟨1,⟨0,by decide⟩⟩
  | _ => ⟨3,⟨0,by decide⟩⟩
theorem raw_edge_encoding_checked : CanonicalEdgeEncoding fixedEdges ∧ CanonicalEdgeEncoding outputEdges := by decide
theorem certificate_checked : ownerCertificateCheck F G d s owners lift = true := by decide
theorem captured_output_decodes :
    ∃ (g : TargetGraph F d) (slots : Fin 2 × Bool ≃ Stub (residualDegree F d)),
      g.val = G ∧ (∀ z, (slots z).1 = owners z) ∧
      graphDecoder F d (adjacentPairing (residualDegree F d) 2 slots) = some g :=
  ownerCertificateCheck_sound F G d s owners lift certificate_checked
set_option pp.all true in
#check @captured_output_decodes
#print axioms raw_edge_encoding_checked
#print axioms certificate_checked
#print axioms captured_output_decodes
end retained_edge

namespace triangle_repeated_owners
def fixedEdges : List (Fin 3 × Fin 3) := []
def outputEdges : List (Fin 3 × Fin 3) := [(0,1),(0,2),(1,2)]
def F := edgeListGraph fixedEdges
def G := edgeListGraph outputEdges
instance fixedAdjDecidable : DecidableRel F.Adj := edgeListGraphDecidable fixedEdges
instance outputAdjDecidable : DecidableRel G.Adj := edgeListGraphDecidable outputEdges
def d : Fin 3 → Nat := fun v => match v.val with
  | 0 => 2
  | 1 => 2
  | _ => 2
def s : Fin 3 → Nat := fun v => match v.val with
  | 0 => 2
  | 1 => 2
  | _ => 2
def owners : Fin 3 × Bool → Fin 3 := fun z => match (pairIndex 3 z).val with
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 2
  | 4 => 1
  | _ => 2
def lift : Fin 3 × Bool → Stub s := fun z => match (pairIndex 3 z).val with
  | 0 => ⟨0,⟨0,by decide⟩⟩
  | 1 => ⟨1,⟨0,by decide⟩⟩
  | 2 => ⟨0,⟨1,by decide⟩⟩
  | 3 => ⟨2,⟨0,by decide⟩⟩
  | 4 => ⟨1,⟨1,by decide⟩⟩
  | _ => ⟨2,⟨1,by decide⟩⟩
theorem raw_edge_encoding_checked : CanonicalEdgeEncoding fixedEdges ∧ CanonicalEdgeEncoding outputEdges := by decide
theorem certificate_checked : ownerCertificateCheck F G d s owners lift = true := by decide
theorem captured_output_decodes :
    ∃ (g : TargetGraph F d) (slots : Fin 3 × Bool ≃ Stub (residualDegree F d)),
      g.val = G ∧ (∀ z, (slots z).1 = owners z) ∧
      graphDecoder F d (adjacentPairing (residualDegree F d) 3 slots) = some g :=
  ownerCertificateCheck_sound F G d s owners lift certificate_checked
set_option pp.all true in
#check @captured_output_decodes
#print axioms raw_edge_encoding_checked
#print axioms certificate_checked
#print axioms captured_output_decodes
end triangle_repeated_owners

namespace fixed_only_zero_residual
def fixedEdges : List (Fin 3 × Fin 3) := [(0,1)]
def outputEdges : List (Fin 3 × Fin 3) := [(0,1)]
def F := edgeListGraph fixedEdges
def G := edgeListGraph outputEdges
instance fixedAdjDecidable : DecidableRel F.Adj := edgeListGraphDecidable fixedEdges
instance outputAdjDecidable : DecidableRel G.Adj := edgeListGraphDecidable outputEdges
def d : Fin 3 → Nat := fun v => match v.val with
  | 0 => 1
  | 1 => 1
  | _ => 0
def s : Fin 3 → Nat := fun v => match v.val with
  | 0 => 0
  | 1 => 0
  | _ => 0
def owners : Fin 0 × Bool → Fin 3 := fun z => Fin.elim0 z.1
def lift : Fin 0 × Bool → Stub s := fun z => Fin.elim0 z.1
theorem raw_edge_encoding_checked : CanonicalEdgeEncoding fixedEdges ∧ CanonicalEdgeEncoding outputEdges := by decide
theorem certificate_checked : ownerCertificateCheck F G d s owners lift = true := by decide
theorem captured_output_decodes :
    ∃ (g : TargetGraph F d) (slots : Fin 0 × Bool ≃ Stub (residualDegree F d)),
      g.val = G ∧ (∀ z, (slots z).1 = owners z) ∧
      graphDecoder F d (adjacentPairing (residualDegree F d) 0 slots) = some g :=
  ownerCertificateCheck_sound F G d s owners lift certificate_checked
set_option pp.all true in
#check @captured_output_decodes
#print axioms raw_edge_encoding_checked
#print axioms certificate_checked
#print axioms captured_output_decodes
end fixed_only_zero_residual

end ConfigurationPairing.OwnerCertificateExamples
