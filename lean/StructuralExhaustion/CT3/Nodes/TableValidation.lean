import StructuralExhaustion.CT3.Graph

namespace StructuralExhaustion.CT3.Nodes.TableValidation

def nodeId : Graph.NodeId := .tableValidation

def automationContract : Core.NodeAutomationContract where
  nodeId := Graph.NodeId.code nodeId
  executionClass := .finiteSearch
  authorInputs := [
    ⟨"Capability.rows", .userFiniteEnumeration⟩,
    ⟨"Capability.contexts", .userFiniteEnumeration⟩,
    ⟨"Spec.rowPiece", .userOperator⟩,
    ⟨"Spec.rowResponse", .userOperator⟩,
    ⟨"Spec.response", .userOperator⟩
  ]
  derivedInputs := [
    ⟨"UncompressibleExternalType", .derivedFromPredecessor⟩
  ]
  frameworkTheorems := ["FiniteSearch.dependentSearch_sound"]
  generatedOutputs := [
    ⟨"CT3.TableValidationDecision", .derivedByGenericSearch⟩,
    ⟨"CT3.DistinguishingContextResidual", .derivedByGenericSearch⟩,
    ⟨"CT3.ExactTableState", .derivedByGenericTheorem⟩
  ]
  manualObligations := []

abbrev Contract {P : Core.Problem} (S : Spec P) (C : Capability S)
    (input : Input S) :=
  TableValidationDecision S C input

def run {P : Core.Problem} (S : Spec P) (C : Capability S)
    {input : Input S} {vector : ExactVectorState S input}
    (_state : UncompressibleExternalType S C input vector) : Contract S C input :=
  validateTable S C input

end StructuralExhaustion.CT3.Nodes.TableValidation
