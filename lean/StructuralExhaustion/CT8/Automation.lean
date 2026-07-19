import StructuralExhaustion.CT8.Theorems
import StructuralExhaustion.Core.CTTransition

namespace StructuralExhaustion.CT8

namespace Capability

/-- Canonical executable CT8 entry.  The dependent trigger is the exact
input already indexed by the inherited branch context, and execution invokes
only CT8's public reference runner. -/
def executableInterface
    {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability.{uAmbient, uBranch, uState, uType, uResponseContext} P) :
    Core.Routing.ExecutableInterface .ct8 where
  Context := Core.BranchContext P
  Trigger := Input capability
  Result := fun context input => ExecutionResult capability context input
  execute := fun context input => run capability context input

end Capability

def responseSeparationResidualKindId := "CT8.residual.responseSeparation"
def removalResidualKindId := "CT8.residual.removal"

def residualKindContracts : List Core.ResidualKindContract := [
  {
    residualKindId := removalResidualKindId
    leanType := "StructuralExhaustion.CT8.RemovalResidual"
    semanticFields := [
      ⟨"pair", "OrderedRepeatedPair", .derivedByGenericSearch⟩,
      ⟨"responsesEqual", "ResponsesEqual", .derivedByGenericTheorem⟩,
      ⟨"smaller", "Core.SmallerObject", .derivedByComputation⟩]
    inheritedContext := .branch
  },
  {
    residualKindId := responseSeparationResidualKindId
    leanType := "StructuralExhaustion.CT8.SeparationResidual"
    semanticFields := [
      ⟨"pair", "OrderedRepeatedPair", .derivedByGenericSearch⟩,
      ⟨"separator", "ResponseSeparator", .derivedByGenericSearch⟩]
    inheritedContext := .branch
  }]
def capabilityContract : Core.CapabilityContract where
  capabilityId := "StructuralExhaustion.CT8.reference"
  tacticId := "CT8"
  requiredDefinitions := [
    ⟨"Capability.State", .userDefinition⟩,
    ⟨"Capability.ExactType", .userDefinition⟩,
    ⟨"Capability.ResponseContext", .userDefinition⟩,
    ⟨"Capability.exactTypes", .userFiniteEnumeration⟩,
    ⟨"Capability.responseContexts", .userFiniteEnumeration⟩,
    ⟨"Capability.exactType", .userOperator⟩,
    ⟨"Capability.response", .userOperator⟩,
    ⟨"Input.remove", .userOperator⟩]
  requiredInstances := []
  derivedOperations := ["CT8.findRepeated", "CT8.analyzeResponses",
    "CT8.runReference", "CT8.Capability.executableInterface",
    responseSeparationResidualKindId, removalResidualKindId]
def nodeAutomationContracts : List Core.NodeAutomationContract := [
  ⟨"CT8.entry", .definitional, [],
    [⟨"context", .derivedFromPredecessor⟩,
      ⟨"Input.sequence", .derivedFromPredecessor⟩], [],
    [⟨"CT8.Input", .derivedFromPredecessor⟩], []⟩,
  ⟨"CT8.search.orderedRepeatedType", .finiteSearch,
    [⟨"Capability.exactTypes", .userFiniteEnumeration⟩,
      ⟨"Capability.exactType", .userOperator⟩],
    [⟨"Input.sequence", .derivedFromPredecessor⟩],
    ["Core.FiniteSearch.onList"],
    [⟨"CT8.RepetitionDecision", .derivedByGenericSearch⟩,
      ⟨"CT8.OrderedRepeatedPair", .derivedByGenericSearch⟩,
      ⟨"CT8.NoRepetitionCertificate", .derivedByGenericTheorem⟩], []⟩,
  ⟨"CT8.compare.responses", .finiteSearch,
    [⟨"Capability.responseContexts", .userFiniteEnumeration⟩,
      ⟨"Capability.response", .userOperator⟩,
      ⟨"Input.remove", .userOperator⟩],
    [⟨"CT8.OrderedRepeatedPair", .derivedFromPredecessor⟩],
    ["Core.FiniteSearch.search"],
    [⟨"CT8.ResponseDecision", .derivedByGenericSearch⟩,
      ⟨"CT8.RemovalResidual", .derivedByGenericTheorem⟩,
      ⟨"CT8.SeparationResidual", .derivedByGenericSearch⟩], []⟩]
syntax "ct8_execute " term " at " term " on " term : term
macro_rules
  | `(ct8_execute $cap:term at $ctx:term on $input:term) =>
      `(CT8.run $cap $ctx $input)
syntax "ct8 " term " at " term " on " term : tactic
macro_rules
  | `(tactic| ct8 $cap:term at $ctx:term on $input:term) =>
      `(tactic| exact CT8.run_verified $cap $ctx $input)
syntax "ct8_total " term " at " term " on " term : tactic
macro_rules
  | `(tactic| ct8_total $cap:term at $ctx:term on $input:term) =>
      `(tactic| exact CT8.run_total $cap $ctx $input)
end StructuralExhaustion.CT8
