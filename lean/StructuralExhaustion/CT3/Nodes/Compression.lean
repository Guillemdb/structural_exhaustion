import StructuralExhaustion.CT3.Graph

namespace StructuralExhaustion.CT3.Nodes.Compression

def nodeId : Graph.NodeId := .compressionSearch

def automationContract : Core.NodeAutomationContract where
  nodeId := Graph.NodeId.code nodeId
  executionClass := .finiteSearch
  authorInputs := [
    ⟨"Capability.candidates", .userFiniteEnumeration⟩,
    ⟨"Spec.candidatePiece", .userOperator⟩,
    ⟨"Spec.response", .userOperator⟩,
    ⟨"Spec.Admissible", .userDefinition⟩,
    ⟨"Spec.Smaller", .userDefinition⟩,
    ⟨"Capability.contexts", .userFiniteEnumeration⟩,
    ⟨"Capability.admissibleDecidable", .instanceBridge⟩,
    ⟨"Capability.smallerDecidable", .instanceBridge⟩
  ]
  derivedInputs := [
    ⟨"ExactVectorState", .derivedFromPredecessor⟩,
    ⟨"SameResponse", .derivedByGenericSearch⟩
  ]
  frameworkTheorems := [
    "FiniteSearch.first_total",
    "ResponseComparison.compare_total"
  ]
  generatedOutputs := [
    ⟨"CT3.CompressionDecision", .derivedByGenericSearch⟩,
    ⟨"CT3.CompressionCertificate", .derivedByGenericSearch⟩,
    ⟨"CT3.UncompressibleExternalType", .derivedByGenericTheorem⟩
  ]
  manualObligations := []

abbrev Contract {P : Core.Problem} (S : Spec P) (C : Capability S)
    (input : Input S) (vector : ExactVectorState S input) :=
  CompressionDecision S C input vector

def run {P : Core.Problem} (S : Spec P) (C : Capability S)
    (input : Input S) (vector : ExactVectorState S input) :
    Contract S C input vector :=
  findCompression S C input vector

end StructuralExhaustion.CT3.Nodes.Compression
