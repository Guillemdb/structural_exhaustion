import StructuralExhaustion.CT7.Theorems

namespace StructuralExhaustion.CT7

def residualKindContracts : List Core.ResidualKindContract := [
  {
    residualKindId := "CT7.residual.distinguishingContext"
    leanType := "StructuralExhaustion.CT7.DistinguishingResidual S capability ctx input"
    semanticFields := [
      ⟨"unrealized", "CT7.UnrealizedState S capability ctx input",
        .derivedFromPredecessor⟩,
      ⟨"context", "S.Context", .derivedByGenericSearch⟩,
      ⟨"differs",
        "S.response ctx input.left context ≠ S.response ctx input.right context",
        .derivedByGenericSearch⟩
    ]
    inheritedContext := .branch
  }
]

def residualKindIds : List String :=
  residualKindContracts.map fun contract => contract.residualKindId

def capabilityContract : Core.CapabilityContract where
  capabilityId := "StructuralExhaustion.CT7.reference"
  tacticId := "CT7"
  requiredDefinitions := [
    ⟨"Spec.Object", .userDefinition⟩,
    ⟨"Spec.Context", .userDefinition⟩,
    ⟨"Spec.Realizes", .userDefinition⟩,
    ⟨"Spec.response", .userOperator⟩,
    ⟨"Capability.contexts", .userFiniteEnumeration⟩,
    ⟨"Capability.realizesDecidable", .instanceBridge⟩]
  requiredInstances := ["Capability.realizesDecidable"]
  derivedOperations := ["CT7.analyzeRealization", "CT7.analyzeDistinction",
    "CT7.runReference",
    "CT7.residual.distinguishingContext"]

def nodeAutomationContracts : List Core.NodeAutomationContract := [
  { nodeId := "CT7.entry", executionClass := .definitional,
    authorInputs := [], derivedInputs := [⟨"input", .derivedFromPredecessor⟩],
    frameworkTheorems := [],
    generatedOutputs := [⟨"CT7.Input", .derivedDefinitionally⟩],
    manualObligations := [] },
  { nodeId := "CT7.search.realization", executionClass := .finiteSearch,
    authorInputs := [⟨"Spec.Realizes", .userDefinition⟩,
      ⟨"Capability.contexts", .userFiniteEnumeration⟩,
      ⟨"Capability.realizesDecidable", .instanceBridge⟩],
    derivedInputs := [⟨"input", .derivedFromPredecessor⟩],
    frameworkTheorems := ["Core.FiniteSearch.search_none_iff"],
    generatedOutputs := [
      ⟨"CT7.RealizationDecision", .derivedByGenericSearch⟩,
      ⟨"CT7.RealizationCertificate", .derivedByGenericSearch⟩,
      ⟨"CT7.UnrealizedState", .derivedByGenericTheorem⟩],
    manualObligations := [] },
  { nodeId := "CT7.search.distinction", executionClass := .finiteSearch,
    authorInputs := [⟨"Spec.response", .userOperator⟩,
      ⟨"Capability.contexts", .userFiniteEnumeration⟩],
    derivedInputs := [⟨"CT7.UnrealizedState", .derivedFromPredecessor⟩],
    frameworkTheorems := ["Core.FiniteSearch.search_none_iff"],
    generatedOutputs := [
      ⟨"CT7.DistinctionDecision", .derivedByGenericSearch⟩,
      ⟨"CT7.DistinguishingResidual", .derivedByGenericSearch⟩,
      ⟨"CT7.NeutralityCertificate", .derivedByGenericTheorem⟩],
    manualObligations := [] }
]

syntax "ct7_execute " term " using " term " at " term " on " term : term
macro_rules
  | `(ct7_execute $S using $cap at $ctx on $input) =>
      `(StructuralExhaustion.CT7.run $S $cap $ctx $input)
syntax "ct7 " term " using " term " at " term " on " term : tactic
macro_rules
  | `(tactic| ct7 $S using $cap at $ctx on $input) =>
      `(tactic| exact StructuralExhaustion.CT7.run_verified $S $cap $ctx $input)
syntax "ct7_total " term " using " term " at " term " on " term : tactic
macro_rules
  | `(tactic| ct7_total $S using $cap at $ctx on $input) =>
      `(tactic| exact StructuralExhaustion.CT7.run_total $S $cap $ctx $input)

end StructuralExhaustion.CT7
