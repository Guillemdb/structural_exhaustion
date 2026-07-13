import StructuralExhaustion.CT3.Graph

namespace StructuralExhaustion.CT3.Nodes.Lookup

def nodeId : Graph.NodeId := .rowLookup

def automationContract : Core.NodeAutomationContract where
  nodeId := Graph.NodeId.code nodeId
  executionClass := .finiteSearch
  authorInputs := [
    ⟨"Capability.rows", .userFiniteEnumeration⟩,
    ⟨"Capability.contexts", .userFiniteEnumeration⟩,
    ⟨"Spec.response", .userOperator⟩,
    ⟨"Spec.rowResponse", .userOperator⟩
  ]
  derivedInputs := [
    ⟨"ExactTableState", .derivedFromPredecessor⟩,
    ⟨"RowMatches", .derivedByGenericSearch⟩
  ]
  frameworkTheorems := [
    "FiniteSearch.first_total",
    "ResponseComparison.compare_total"
  ]
  generatedOutputs := [
    ⟨"CT3.RowLookupDecision", .derivedByGenericSearch⟩,
    ⟨"CT3.KnownRowCertificate", .derivedByGenericSearch⟩,
    ⟨"CT3.NovelExternalTypeResidual", .derivedByGenericTheorem⟩
  ]
  manualObligations := []

abbrev Contract {P : Core.Problem} (S : Spec P) (C : Capability S)
    (input : Input S) (table : ExactTableState S C) :=
  RowLookupDecision S C input table

def run {P : Core.Problem} (S : Spec P) (C : Capability S)
    (input : Input S) (table : ExactTableState S C) :
    Contract S C input table :=
  lookupRow S C input table

end StructuralExhaustion.CT3.Nodes.Lookup
