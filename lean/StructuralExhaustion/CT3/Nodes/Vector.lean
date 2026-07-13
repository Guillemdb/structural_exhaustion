import StructuralExhaustion.CT3.Graph

namespace StructuralExhaustion.CT3.Nodes.Vector

def nodeId : Graph.NodeId := .vectorComputation

def automationContract : Core.NodeAutomationContract where
  nodeId := Graph.NodeId.code nodeId
  executionClass := .definitional
  authorInputs := [⟨"Spec.response", .userOperator⟩]
  derivedInputs := [⟨"Input.piece", .derivedFromPredecessor⟩]
  frameworkTheorems := ["ExactVectorState.exact"]
  generatedOutputs := [⟨"CT3.ExactVectorState", .derivedByComputation⟩]
  manualObligations := []

abbrev Contract {P : Core.Problem} (S : Spec P) (input : Input S) :=
  ExactVectorState S input

def run {P : Core.Problem} (S : Spec P) (input : Input S) :
    Contract S input :=
  computeExactVector S input

end StructuralExhaustion.CT3.Nodes.Vector
