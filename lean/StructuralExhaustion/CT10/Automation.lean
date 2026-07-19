import StructuralExhaustion.CT10.Theorems
import StructuralExhaustion.Core.CTTransition

namespace StructuralExhaustion.CT10

namespace Capability

/-- Canonical executable CT10 entry.  The route contributes only the exact
local datum collection, while `Input.ofTrigger` preserves the predecessor's
branch context by construction. -/
def executableInterface {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability.{uAmbient, uBranch, uDatum, uClass, uPromotion} P) :
    Core.Routing.ExecutableInterface .ct10 where
  Context := Core.BranchContext P
  Trigger := Trigger capability
  Result := fun context trigger =>
    ExecutionResult capability (Input.ofTrigger context trigger)
  execute := fun context trigger =>
    run capability (Input.ofTrigger context trigger)

end Capability

def directResidualKindId := "CT10.residual.direct"
def promotedResidualKindId := "CT10.residual.promoted"

def residualKindContracts : List Core.ResidualKindContract := [
  {
    residualKindId := directResidualKindId
    leanType := "StructuralExhaustion.CT10.DirectResidual"
    semanticFields := [
      ⟨"cls", "Capability.Class", .derivedByGenericSearch⟩,
      ⟨"direct", "Capability.Direct cls", .derivedByGenericTheorem⟩]
    inheritedContext := .branch
  },
  {
    residualKindId := promotedResidualKindId
    leanType := "StructuralExhaustion.CT10.PromotedResidual"
    semanticFields := [
      ⟨"missing", "MissingDatum", .derivedByGenericSearch⟩,
      ⟨"promotion", "Capability.Promotion", .derivedByComputation⟩]
    inheritedContext := .branch
  }]

def capabilityContract : Core.CapabilityContract where
  capabilityId := "StructuralExhaustion.CT10.reference"
  tacticId := "CT10"
  requiredDefinitions := [
    ⟨"Capability.Datum", .userDefinition⟩,
    ⟨"Capability.Class", .userDefinition⟩,
    ⟨"Capability.Promotion", .userDefinition⟩,
    ⟨"Capability.classes", .userFiniteEnumeration⟩,
    ⟨"Capability.classOf", .userOperator⟩,
    ⟨"Capability.Direct", .userDefinition⟩,
    ⟨"Capability.directDecidable", .instanceBridge⟩,
    ⟨"Capability.promote", .userOperator⟩]
  requiredInstances := ["Capability.directDecidable"]
  derivedOperations := ["CT10.row", "CT10.analyzeDirect", "CT10.analyzeMissing",
    "CT10.runReference", "CT10.Capability.executableInterface",
    directResidualKindId, promotedResidualKindId]

def nodeAutomationContracts : List Core.NodeAutomationContract := [
  ⟨"CT10.entry", .definitional, [],
    [⟨"Input.context", .derivedFromPredecessor⟩,
      ⟨"Input.data", .derivedFromPredecessor⟩], [],
    [⟨"CT10.Input", .derivedFromPredecessor⟩], []⟩,
  ⟨"CT10.compute.classTable", .definitional, [], [], [],
    [⟨"CT10.Graph.Edge.tableBuilt", .generatedAudit⟩], []⟩,
  ⟨"CT10.search.direct", .finiteSearch,
    [⟨"Capability.classes", .userFiniteEnumeration⟩,
      ⟨"Capability.Direct", .userDefinition⟩,
      ⟨"Capability.directDecidable", .instanceBridge⟩],
    [], ["Core.FiniteSearch.search"],
    [⟨"CT10.DirectDecision", .derivedByGenericSearch⟩,
      ⟨"CT10.DirectResidual", .derivedByGenericSearch⟩,
      ⟨"CT10.DirectAbsent", .derivedByGenericTheorem⟩], []⟩,
  ⟨"CT10.search.firstMissing", .finiteSearch,
    [⟨"Capability.classes", .userFiniteEnumeration⟩,
      ⟨"Capability.classOf", .userOperator⟩,
      ⟨"Capability.promote", .userOperator⟩],
    [⟨"CT10.DirectAbsent", .derivedFromPredecessor⟩,
      ⟨"Input.data", .derivedFromPredecessor⟩,
      ⟨"CT10.row", .derivedByComputation⟩],
    ["CT10.datum_mem_own_row", "Core.FiniteSearch.search"],
    [⟨"CT10.MissingDecision", .derivedByGenericSearch⟩,
      ⟨"CT10.PromotedResidual", .derivedByGenericSearch⟩,
      ⟨"CT10.ExhaustiveCertificate", .derivedByGenericTheorem⟩], []⟩,
  ⟨"CT10.compute.promotion", .definitional, [],
    [⟨"CT10.PromotedResidual", .derivedFromPredecessor⟩], [],
    [⟨"CT10.Graph.Edge.promoted", .generatedAudit⟩], []⟩]

syntax "ct10_execute " term " on " term : term
macro_rules
  | `(ct10_execute $cap:term on $input:term) => `(CT10.run $cap $input)
syntax "ct10 " term " on " term : tactic
macro_rules
  | `(tactic| ct10 $cap:term on $input:term) =>
      `(tactic| exact CT10.run_verified $cap $input)
syntax "ct10_total " term " on " term : tactic
macro_rules
  | `(tactic| ct10_total $cap:term on $input:term) =>
      `(tactic| exact CT10.run_total $cap $input)

end StructuralExhaustion.CT10
