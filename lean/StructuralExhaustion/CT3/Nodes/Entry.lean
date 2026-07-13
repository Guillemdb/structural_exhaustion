import StructuralExhaustion.CT3.Graph

namespace StructuralExhaustion.CT3.Nodes.Entry

def nodeId : Graph.NodeId := .entry

def automationContract : Core.NodeAutomationContract where
  nodeId := Graph.NodeId.code nodeId
  executionClass := .definitional
  authorInputs := []
  derivedInputs := [
    ⟨"Input.context", .derivedFromPredecessor⟩,
    ⟨"Input.piece", .derivedFromPredecessor⟩
  ]
  frameworkTheorems := []
  generatedOutputs := [⟨"CT3.Input", .derivedFromPredecessor⟩]
  manualObligations := []

abbrev Contract {P : Core.Problem} (S : Spec P) := Input S

def run {P : Core.Problem} {S : Spec P} (input : Input S) : Contract S :=
  input

end StructuralExhaustion.CT3.Nodes.Entry
