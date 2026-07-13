import StructuralExhaustion.CT11.NegativeBudget

namespace StructuralExhaustion.CT11

def admissibilityGapResidualKindId := "CT11.residual.admissibilityGap"
def localizedDeficitResidualKindId := "CT11.residual.localizedDeficit"

def residualKindContracts : List Core.ResidualKindContract := [
  {
    residualKindId := admissibilityGapResidualKindId
    leanType := "StructuralExhaustion.CT11.AdmissibilityGapResidual"
    semanticFields := [
      ⟨"cell", "Capability.Cell", .derivedByGenericSearch⟩,
      ⟨"inadmissible", "¬ Capability.Admissible context cell", .derivedByGenericTheorem⟩]
    inheritedContext := .branch
  },
  {
    residualKindId := localizedDeficitResidualKindId
    leanType := "StructuralExhaustion.CT11.LocalizedDeficitResidual"
    semanticFields := [
      ⟨"cell", "Capability.Cell", .derivedByGenericSearch⟩,
      ⟨"negative", "localBudget context cell < 0", .derivedByGenericTheorem⟩]
    inheritedContext := .branch
  }]

def capabilityContract : Core.CapabilityContract where
  capabilityId := "StructuralExhaustion.CT11.reference"
  tacticId := "CT11"
  requiredDefinitions := [
    ⟨"Capability.Cell", .userDefinition⟩,
    ⟨"Capability.Admissible", .userDefinition⟩,
    ⟨"Capability.admissibleDecidable", .instanceBridge⟩,
    ⟨"Capability.localBudget", .userOperator⟩]
  requiredInstances := ["Capability.admissibleDecidable"]
  derivedOperations := ["CT11.analyzeAdmissibility", "CT11.localize",
    "CT11.runReference", admissibilityGapResidualKindId, localizedDeficitResidualKindId]

/-- Minimal author contract for everywhere-admissible negative-budget
localization. -/
def negativeBudgetCapabilityProfile : Core.CapabilityProfile where
  capabilityId := "StructuralExhaustion.CT11.profile.negativeBudget"
  tacticId := "CT11"
  requiredDefinitions := [
    ⟨"StructuralExhaustion.CT11.NegativeBudgetProfile.Cell", .userDefinition⟩,
    ⟨"StructuralExhaustion.CT11.NegativeBudgetProfile.localBudget",
      .userOperator⟩]
  requiredInstances := []
  derivedOperations := [
    "StructuralExhaustion.CT11.NegativeBudgetProfile.capability",
    "StructuralExhaustion.CT11.NegativeBudgetProfile.input",
    "StructuralExhaustion.CT11.NegativeBudgetProfile.run",
    "StructuralExhaustion.CT11.NegativeBudgetProfile.run_terminal_localized",
    "StructuralExhaustion.CT11.NegativeBudgetProfile.residual"]

def nodeAutomationContracts : List Core.NodeAutomationContract := [
  ⟨"CT11.entry", .definitional, [],
    [⟨"Input.context", .derivedFromPredecessor⟩,
      ⟨"Input.cells", .derivedFromPredecessor⟩,
      ⟨"Input.deficit", .derivedFromPredecessor⟩], [],
    [⟨"CT11.Input", .derivedFromPredecessor⟩], []⟩,
  ⟨"CT11.compute.decomposition", .definitional, [],
    [], [],
    [⟨"CT11.Graph.Edge.decomposed", .generatedAudit⟩], []⟩,
  ⟨"CT11.search.admissibilityGap", .finiteSearch,
    [⟨"Capability.Admissible", .userDefinition⟩,
      ⟨"Capability.admissibleDecidable", .instanceBridge⟩],
    [⟨"Input.context", .derivedFromPredecessor⟩,
      ⟨"Input.cells", .derivedFromPredecessor⟩],
    ["Core.FiniteSearch.onList"],
    [⟨"CT11.AdmissibilityDecision", .derivedByGenericSearch⟩,
      ⟨"CT11.AdmissibilityGapResidual", .derivedByGenericSearch⟩,
      ⟨"CT11.AdmissibleDecomposition", .derivedByGenericTheorem⟩], []⟩,
  ⟨"CT11.search.localNegativeBudget", .finiteSearch,
    [⟨"Capability.localBudget", .userOperator⟩],
    [⟨"CT11.AdmissibleDecomposition", .derivedFromPredecessor⟩,
      ⟨"Input.context", .derivedFromPredecessor⟩,
      ⟨"Input.cells", .derivedFromPredecessor⟩,
      ⟨"Input.deficit", .derivedFromPredecessor⟩],
    ["CT11.sum_nonnegative"],
    [⟨"CT11.LocalizedDeficitResidual", .derivedByGenericSearch⟩], []⟩]

syntax "ct11_execute " term " on " term : term
macro_rules
  | `(ct11_execute $cap:term on $input:term) => `(CT11.run $cap $input)
syntax "ct11 " term " on " term : tactic
macro_rules
  | `(tactic| ct11 $cap:term on $input:term) =>
      `(tactic| exact CT11.run_verified $cap $input)
syntax "ct11_total " term " on " term : tactic
macro_rules
  | `(tactic| ct11_total $cap:term on $input:term) =>
      `(tactic| exact CT11.run_total $cap $input)

end StructuralExhaustion.CT11
