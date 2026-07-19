import StructuralExhaustion.CT4.Cardinality
import StructuralExhaustion.Core.CTTransition

namespace StructuralExhaustion.CT4

namespace Capability

/-- Canonical executable CT4 entry.  CT4 consumes the inherited branch
context directly; its capability owns every finite universe and the unique
route trigger cannot replace predecessor state. -/
def executableInterface {P : Core.Problem} {S : Spec P}
    (capability : Capability S) :
    Core.Routing.ExecutableInterface .ct4 where
  Context := Core.BranchContext P
  Trigger := fun _context => Unit
  Result := fun input _trigger => ExecutionResult S capability input
  execute := fun input _trigger => run S capability input

end Capability

def residualKindContracts : List Core.ResidualKindContract := [
  {
    residualKindId := "CT4.residual.missingPayer"
    leanType := "StructuralExhaustion.CT4.MissingPayerResidual S input"
    semanticFields := [
      ⟨"demand", "S.Demand", .derivedByGenericSearch⟩,
      ⟨"noEligible", "CT4.MissingAt S input demand", .derivedByGenericTheorem⟩
    ]
    inheritedContext := .branch
  },
  {
    residualKindId := "CT4.residual.overloadedFibre"
    leanType := "StructuralExhaustion.CT4.OverloadedFibreResidual S capability input"
    semanticFields := [
      ⟨"total", "CT4.TotalAssignmentState S capability input",
        .derivedFromPredecessor⟩,
      ⟨"payer", "S.Payer", .derivedByGenericSearch⟩,
      ⟨"overloaded",
        "CT4.Overloaded S capability input total.assignment payer",
        .derivedByComputation⟩
    ]
    inheritedContext := .branch
  },
  {
    residualKindId := "CT4.residual.capacity"
    leanType := "StructuralExhaustion.CT4.CapacityResidual S capability input"
    semanticFields := [
      ⟨"bounded", "CT4.BoundedFibreState S capability input",
        .derivedFromPredecessor⟩,
      ⟨"required_le_capacity",
        "capability.required input ≤ CT4.totalCapacity S capability input",
        .derivedByComputation⟩
    ]
    inheritedContext := .branch
  }
]

def residualKindIds : List String :=
  residualKindContracts.map fun contract => contract.residualKindId
def capabilityContract : Core.CapabilityContract where
  capabilityId := "StructuralExhaustion.CT4.reference"
  tacticId := "CT4"
  requiredDefinitions := [
    ⟨"Spec.Demand", .userDefinition⟩,
    ⟨"Spec.Payer", .userDefinition⟩,
    ⟨"Spec.Eligible", .userDefinition⟩,
    ⟨"Spec.demandWeight", .userOperator⟩,
    ⟨"Spec.capacity", .userOperator⟩,
    ⟨"Capability.demands", .userFiniteEnumeration⟩,
    ⟨"Capability.payers", .userFiniteEnumeration⟩,
    ⟨"Capability.eligibleDecidable", .instanceBridge⟩,
    ⟨"Capability.required", .userOperator⟩]
  requiredInstances := ["Capability.eligibleDecidable"]
  derivedOperations := ["CT4.assignedPayer", "CT4.analyzeAvailability",
    "CT4.analyzeFibres", "CT4.compareCapacity", "CT4.runReference",
    "CT4.Capability.executableInterface",
    "CT4.residual.missingPayer", "CT4.residual.overloadedFibre",
    "CT4.residual.capacity"]

/-- Minimal author contract for the functional strict-cardinality profile. -/
def functionalCardinalityCapabilityProfile : Core.CapabilityProfile where
  capabilityId := "StructuralExhaustion.CT4.profile.functionalCardinality"
  tacticId := "CT4"
  requiredDefinitions := [
    ⟨"StructuralExhaustion.CT4.FunctionalCardinalityProfile.Demand",
      .userDefinition⟩,
    ⟨"StructuralExhaustion.CT4.FunctionalCardinalityProfile.Payer",
      .userDefinition⟩,
    ⟨"StructuralExhaustion.CT4.FunctionalCardinalityProfile.Eligible",
      .userDefinition⟩,
    ⟨"StructuralExhaustion.CT4.FunctionalCardinalityProfile.demands",
      .userFiniteEnumeration⟩,
    ⟨"StructuralExhaustion.CT4.FunctionalCardinalityProfile.payers",
      .userFiniteEnumeration⟩,
    ⟨"StructuralExhaustion.CT4.FunctionalCardinalityProfile.eligibleDecidable",
      .instanceBridge⟩,
    ⟨"StructuralExhaustion.CT4.FunctionalCardinalityProfile.functional",
      .userOperator⟩]
  requiredInstances := [
    "StructuralExhaustion.CT4.FunctionalCardinalityProfile.eligibleDecidable"]
  derivedOperations := [
    "StructuralExhaustion.CT4.FunctionalCardinalityProfile.spec",
    "StructuralExhaustion.CT4.FunctionalCardinalityProfile.capability",
    "StructuralExhaustion.CT4.FunctionalCardinalityProfile.run",
    "StructuralExhaustion.CT4.FunctionalCardinalityProfile.run_terminal_eq_missing",
    "StructuralExhaustion.CT4.FunctionalCardinalityProfile.missingResidual"]
def nodeAutomationContracts : List Core.NodeAutomationContract := [
  { nodeId := "CT4.entry", executionClass := .definitional,
    authorInputs := [], derivedInputs := [], frameworkTheorems := [],
    generatedOutputs := [⟨"CT4.Input", .derivedDefinitionally⟩],
    manualObligations := [] },
  { nodeId := "CT4.compute.assignment", executionClass := .finiteSearch,
    authorInputs := [⟨"Spec.Eligible", .userDefinition⟩,
      ⟨"Capability.payers", .userFiniteEnumeration⟩,
      ⟨"Capability.eligibleDecidable", .instanceBridge⟩],
    derivedInputs := [⟨"input", .derivedFromPredecessor⟩],
    frameworkTheorems := ["Core.FiniteSearch.search_sound",
      "CT4.assignedPayer_sound"],
    generatedOutputs := [⟨"CT4.AssignmentState", .derivedByGenericSearch⟩],
    manualObligations := [] },
  { nodeId := "CT4.search.availability", executionClass := .finiteSearch,
    authorInputs := [⟨"Capability.demands", .userFiniteEnumeration⟩],
    derivedInputs := [⟨"CT4.AssignmentState", .derivedFromPredecessor⟩],
    frameworkTheorems := ["Core.FiniteSearch.search_none_iff"],
    generatedOutputs := [
      ⟨"CT4.AvailabilityDecision", .derivedByGenericSearch⟩,
      ⟨"CT4.MissingPayerResidual", .derivedByGenericSearch⟩,
      ⟨"CT4.TotalAssignmentState", .derivedByGenericTheorem⟩],
    manualObligations := [] },
  { nodeId := "CT4.compute.fibres", executionClass := .verifiedComputation,
    authorInputs := [⟨"Spec.demandWeight", .userOperator⟩,
      ⟨"Spec.capacity", .userOperator⟩,
      ⟨"Capability.demands", .userFiniteEnumeration⟩,
      ⟨"Capability.payers", .userFiniteEnumeration⟩],
    derivedInputs := [⟨"CT4.TotalAssignmentState", .derivedFromPredecessor⟩,
      ⟨"fibre", .derivedByComputation⟩],
    frameworkTheorems := [],
    generatedOutputs := [
      ⟨"CT4.FibreDecision", .derivedByGenericSearch⟩,
      ⟨"CT4.OverloadedFibreResidual", .derivedByGenericSearch⟩,
      ⟨"CT4.BoundedFibreState", .derivedByGenericTheorem⟩],
    manualObligations := [] },
  { nodeId := "CT4.decide.capacity", executionClass := .verifiedComputation,
    authorInputs := [⟨"Capability.required", .userOperator⟩,
      ⟨"Capability.payers", .userFiniteEnumeration⟩,
      ⟨"Spec.capacity", .userOperator⟩],
    derivedInputs := [⟨"CT4.BoundedFibreState", .derivedFromPredecessor⟩,
      ⟨"totalCapacity", .derivedByComputation⟩],
    frameworkTheorems := [],
    generatedOutputs := [
      ⟨"CT4.CapacityDecision", .derivedByComputation⟩,
      ⟨"CT4.C4Certificate", .derivedByGenericTheorem⟩,
      ⟨"CT4.CapacityResidual", .derivedByGenericTheorem⟩],
    manualObligations := [] }
]

syntax "ct4_execute " term " using " term " at " term : term
macro_rules
  | `(ct4_execute $S using $cap at $input) =>
      `(StructuralExhaustion.CT4.run $S $cap $input)
syntax "ct4 " term " using " term " at " term : tactic
macro_rules
  | `(tactic| ct4 $S using $cap at $input) =>
      `(tactic| exact StructuralExhaustion.CT4.run_verified $S $cap $input)
syntax "ct4_total " term " using " term " at " term : tactic
macro_rules
  | `(tactic| ct4_total $S using $cap at $input) =>
      `(tactic| exact StructuralExhaustion.CT4.run_total $S $cap $input)

end StructuralExhaustion.CT4
