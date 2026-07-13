import StructuralExhaustion.CT16.Theorems

namespace StructuralExhaustion.CT16

def residualKindContracts : List Core.ResidualKindContract := [
  ⟨"CT16.residual.properSupport", "StructuralExhaustion.CT16.ProperSupportResidual",
    [⟨"missing", "Capability.Coordinate", .derivedByGenericSearch⟩,
     ⟨"absent", "¬ InSupport context.G missing", .derivedByGenericTheorem⟩], .branch⟩,
  ⟨"CT16.residual.closedTypeMismatch", "StructuralExhaustion.CT16.ClosedTypeMismatchResidual",
    [⟨"state", "ClosedCodeState", .derivedFromPredecessor⟩,
     ⟨"notEqual", "closedCode context.G ≠ targetCode", .derivedByComputation⟩], .branch⟩]
def residualKindIds := residualKindContracts.map (·.residualKindId)
def capabilityContract : Core.CapabilityContract := ⟨"CT16.reference", "CT16",
  [⟨"Capability.Coordinate", .userDefinition⟩,
   ⟨"Capability.ClosedCode", .userDefinition⟩,
   ⟨"Capability.coordinates", .userFiniteEnumeration⟩,
   ⟨"Capability.InSupport", .userDefinition⟩,
   ⟨"Capability.inSupportDecidable", .instanceBridge⟩,
   ⟨"Capability.closedCode", .userOperator⟩,
   ⟨"Capability.targetCode", .userDefinition⟩,
   ⟨"Capability.codeDecidableEq", .instanceBridge⟩],
  ["Capability.inSupportDecidable", "Capability.codeDecidableEq"],
  ["exhaustive support scan", "literal closed-code comparison"]⟩
def nodeAutomationContracts : List Core.NodeAutomationContract := [
  {
    nodeId := "CT16.entry"
    executionClass := .definitional
    authorInputs := []
    derivedInputs := [⟨"Input", .derivedFromPredecessor⟩]
    frameworkTheorems := []
    generatedOutputs := [⟨"CT16.Input", .derivedDefinitionally⟩]
    manualObligations := []
  },
  {
    nodeId := "CT16.search.support"
    executionClass := .finiteSearch
    authorInputs := [⟨"Capability.coordinates", .userFiniteEnumeration⟩,
      ⟨"Capability.InSupport", .userDefinition⟩,
      ⟨"Capability.inSupportDecidable", .instanceBridge⟩]
    derivedInputs := [⟨"context", .derivedFromPredecessor⟩]
    frameworkTheorems := ["Core.FiniteSearch.search"]
    generatedOutputs := [
      ⟨"CT16.SupportDecision", .derivedByGenericSearch⟩,
      ⟨"CT16.ProperSupportResidual", .derivedByGenericSearch⟩,
      ⟨"CT16.WholeSupportState", .derivedByGenericTheorem⟩]
    manualObligations := []
  },
  {
    nodeId := "CT16.compute.closed-code"
    executionClass := .verifiedComputation
    authorInputs := [⟨"Capability.closedCode", .userOperator⟩]
    derivedInputs := [⟨"WholeSupportState", .derivedFromPredecessor⟩]
    frameworkTheorems := []
    generatedOutputs := [⟨"CT16.ClosedCodeState", .derivedByComputation⟩]
    manualObligations := []
  },
  {
    nodeId := "CT16.decide.closed-code"
    executionClass := .verifiedComputation
    authorInputs := [⟨"Capability.targetCode", .userDefinition⟩,
      ⟨"Capability.codeDecidableEq", .instanceBridge⟩]
    derivedInputs := [⟨"ClosedCodeState", .derivedFromPredecessor⟩]
    frameworkTheorems := []
    generatedOutputs := [
      ⟨"CT16.CodeDecision", .derivedByComputation⟩,
      ⟨"CT16.ExactCodeCertificate", .derivedByGenericTheorem⟩,
      ⟨"CT16.ClosedTypeMismatchResidual", .derivedByGenericTheorem⟩]
    manualObligations := []
  }]

syntax "ct16_execute " term " at " term " on " term : term
macro_rules | `(ct16_execute $c at $ctx on $i) => `(CT16.run $c $ctx $i)
syntax "ct16 " term " at " term " on " term : tactic
macro_rules
  | `(tactic| ct16 $c at $ctx on $i) =>
      `(tactic| exact CT16.run_verified $c $ctx $i)
syntax "ct16_total " term " at " term " on " term : tactic
macro_rules
  | `(tactic| ct16_total $c at $ctx on $i) =>
      `(tactic| exact CT16.run_total $c $ctx $i)

end StructuralExhaustion.CT16
