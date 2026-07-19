import StructuralExhaustion.CT17.Theorems
import StructuralExhaustion.Core.CTTransition

namespace StructuralExhaustion.CT17

universe uAmbient uBranch uTarget uOffset uPosition uValue

namespace Capability

/-- Canonical executable CT17 entry.  Its typed trigger carries the requested
scale at the inherited branch context; the framework invokes the public CT17
runner without reconstructing any survivor or orbit data. -/
def executableInterface
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : Spec.{uAmbient, uBranch, uTarget, uOffset, uPosition, uValue} P}
    (capability : Capability S) :
    Core.Routing.ExecutableInterface .ct17 where
  Context := Core.BranchContext P
  Trigger := Input S capability
  Result := fun ctx input => ExecutionResult S capability ctx input
  execute := fun ctx input => run S capability ctx input

end Capability

def incompatibilityResidualKindId := "CT17.residual.incompatibility"
def survivorResidualKindId := "CT17.residual.survivors"
def orbitResidualKindId := "CT17.residual.orbit"

def residualKindContracts : List Core.ResidualKindContract := [
  {
    residualKindId := incompatibilityResidualKindId
    leanType := "StructuralExhaustion.CT17.IncompatibilityResidual"
    semanticFields := [
      ⟨"target", "Spec.Target", .derivedByGenericSearch⟩,
      ⟨"offset", "Spec.Offset", .derivedByGenericSearch⟩,
      ⟨"incompatible", "¬ Spec.Compatible context target offset",
        .derivedByGenericTheorem⟩]
    inheritedContext := .branch
  },
  {
    residualKindId := survivorResidualKindId
    leanType := "StructuralExhaustion.CT17.SurvivorResidual"
    semanticFields := [
      ⟨"first", "Spec.Position input.scale", .derivedByGenericSearch⟩,
      ⟨"remaining", "List (Spec.Position input.scale)",
        .derivedByComputation⟩,
      ⟨"exact", "enumeration.survivors = first :: remaining",
        .derivedByGenericTheorem⟩]
    inheritedContext := .branch
  },
  {
    residualKindId := orbitResidualKindId
    leanType := "StructuralExhaustion.CT17.OrbitResidual"
    semanticFields := [
      ⟨"values", "List Spec.Value", .derivedByComputation⟩,
      ⟨"avoids", "OrbitAvoids", .derivedByGenericTheorem⟩]
    inheritedContext := .branch
  }]

def residualKindIds := residualKindContracts.map (·.residualKindId)

def capabilityContract : Core.CapabilityContract where
  capabilityId := "StructuralExhaustion.CT17.reference"
  tacticId := "CT17"
  requiredDefinitions := [
    ⟨"Spec.Target", .userDefinition⟩,
    ⟨"Spec.Offset", .userDefinition⟩,
    ⟨"Spec.Position", .userDefinition⟩,
    ⟨"Spec.Value", .userDefinition⟩,
    ⟨"Spec.targetValue", .userOperator⟩,
    ⟨"Spec.blockValue", .userOperator⟩,
    ⟨"Spec.orbitValue", .userOperator⟩,
    ⟨"Spec.Compatible", .userDefinition⟩,
    ⟨"Capability.targets", .userFiniteEnumeration⟩,
    ⟨"Capability.offsets", .userFiniteEnumeration⟩,
    ⟨"Capability.positions", .userFiniteEnumeration⟩,
    ⟨"Capability.compatibleDecidable", .instanceBridge⟩,
    ⟨"Capability.valueDecidableEq", .instanceBridge⟩,
    ⟨"Capability.finiteScaleLimit", .userDefinition⟩]
  requiredInstances := [
    "Capability.compatibleDecidable",
    "Capability.valueDecidableEq"]
  derivedOperations := [
    "CT17.analyzeCompatibility",
    "CT17.analyzeScale",
    "CT17.enumerateSurvivors",
    "CT17.analyzeArithmetic",
    "CT17.runReference",
    "StructuralExhaustion.CT17.Capability.executableInterface",
    incompatibilityResidualKindId,
    survivorResidualKindId,
    orbitResidualKindId]

def nodeAutomationContracts : List Core.NodeAutomationContract := [
  {
    nodeId := "CT17.entry"
    executionClass := .definitional
    authorInputs := []
    derivedInputs := [⟨"Input", .derivedFromPredecessor⟩]
    frameworkTheorems := []
    generatedOutputs := [⟨"CT17.Graph.Edge.begin", .generatedAudit⟩]
    manualObligations := []
  },
  {
    nodeId := "CT17.search.compatibility"
    executionClass := .finiteSearch
    authorInputs := [
      ⟨"Capability.targets", .userFiniteEnumeration⟩,
      ⟨"Capability.offsets", .userFiniteEnumeration⟩,
      ⟨"Spec.Compatible", .userDefinition⟩,
      ⟨"Capability.compatibleDecidable", .instanceBridge⟩]
    derivedInputs := [⟨"context", .derivedFromPredecessor⟩]
    frameworkTheorems := ["Core.FiniteSearch.dependentSearch",
      "CT17.analyzeCompatibility_sound"]
    generatedOutputs := [
      ⟨"CT17.CompatibilityDecision", .derivedByGenericSearch⟩,
      ⟨"CT17.IncompatibilityResidual", .derivedByGenericSearch⟩,
      ⟨"CT17.CompatibleState", .derivedByGenericTheorem⟩]
    manualObligations := []
  },
  {
    nodeId := "CT17.decide.scale"
    executionClass := .verifiedComputation
    authorInputs := [⟨"Capability.finiteScaleLimit", .userDefinition⟩]
    derivedInputs := [
      ⟨"CompatibleState", .derivedFromPredecessor⟩,
      ⟨"Input.scale", .derivedFromPredecessor⟩]
    frameworkTheorems := ["CT17.analyzeScale_sound"]
    generatedOutputs := [
      ⟨"CT17.ScaleDecision", .derivedByComputation⟩,
      ⟨"CT17.FiniteScaleState", .derivedByComputation⟩,
      ⟨"CT17.OrbitScaleState", .derivedByComputation⟩]
    manualObligations := []
  },
  {
    nodeId := "CT17.enumerate.survivors"
    executionClass := .finiteSearch
    authorInputs := [
      ⟨"Capability.positions", .userFiniteEnumeration⟩,
      ⟨"Capability.targets", .userFiniteEnumeration⟩,
      ⟨"Capability.offsets", .userFiniteEnumeration⟩,
      ⟨"Spec.blockValue", .userOperator⟩,
      ⟨"Spec.targetValue", .userOperator⟩,
      ⟨"Capability.valueDecidableEq", .instanceBridge⟩]
    derivedInputs := [⟨"FiniteScaleState", .derivedFromPredecessor⟩]
    frameworkTheorems := ["Core.FiniteSearch.dependentSearch",
      "CT17.analyzeSurvivors_sound"]
    generatedOutputs := [
      ⟨"CT17.SurvivorDecision", .derivedByGenericSearch⟩,
      ⟨"CT17.ExhaustedCertificate", .derivedByGenericTheorem⟩,
      ⟨"CT17.SurvivorResidual", .derivedByGenericSearch⟩]
    manualObligations := []
  },
  {
    nodeId := "CT17.decide.arithmetic"
    executionClass := .finiteSearch
    authorInputs := [
      ⟨"Capability.targets", .userFiniteEnumeration⟩,
      ⟨"Capability.offsets", .userFiniteEnumeration⟩,
      ⟨"Spec.orbitValue", .userOperator⟩,
      ⟨"Spec.targetValue", .userOperator⟩,
      ⟨"Capability.valueDecidableEq", .instanceBridge⟩]
    derivedInputs := [⟨"OrbitScaleState", .derivedFromPredecessor⟩]
    frameworkTheorems := ["Core.FiniteSearch.dependentSearch",
      "CT17.analyzeArithmetic_sound"]
    generatedOutputs := [
      ⟨"CT17.ArithmeticDecision", .derivedByGenericSearch⟩,
      ⟨"CT17.TargetHitCertificate", .derivedByGenericSearch⟩,
      ⟨"CT17.OrbitResidual", .derivedByGenericTheorem⟩]
    manualObligations := []
  }]

syntax "ct17_execute " term " with " term " at " term " on " term : term
macro_rules
  | `(ct17_execute $spec:term with $capability:term at $ctx:term on $input:term) =>
      `(CT17.run $spec $capability $ctx $input)

syntax "ct17 " term " with " term " at " term " on " term : tactic
macro_rules
  | `(tactic| ct17 $spec:term with $capability:term at $ctx:term on $input:term) =>
      `(tactic| exact CT17.run_verified $spec $capability $ctx $input)

syntax "ct17_total " term " with " term " at " term " on " term : tactic
macro_rules
  | `(tactic| ct17_total $spec:term with $capability:term at $ctx:term
      on $input:term) =>
      `(tactic| exact CT17.run_total $spec $capability $ctx $input)

end StructuralExhaustion.CT17
