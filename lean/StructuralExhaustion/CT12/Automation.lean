import StructuralExhaustion.CT12.DisjointPacking

namespace StructuralExhaustion.CT12

def demandResidualKindId := "CT12.residual.demand"
def tierResidualKindId := "CT12.residual.tier"

def residualKindContracts : List Core.ResidualKindContract := [
  {
    residualKindId := demandResidualKindId
    leanType := "Capability.DemandResidual"
    semanticFields := [
      ⟨"residual", "Capability.DemandResidual", .derivedByComputation⟩]
    inheritedContext := .loopState
  },
  {
    residualKindId := tierResidualKindId
    leanType := "Capability.TierResidual"
    semanticFields := [
      ⟨"residual", "Capability.TierResidual", .derivedByComputation⟩]
    inheritedContext := .loopState
  }]

def capabilityContract : Core.CapabilityContract where
  capabilityId := "StructuralExhaustion.CT12.reference"
  tacticId := "CT12"
  requiredDefinitions := [
    ⟨"Capability.State", .userDefinition⟩,
    ⟨"Capability.DemandResidual", .userDefinition⟩,
    ⟨"Capability.TierResidual", .userDefinition⟩,
    ⟨"Capability.Peeled", .userDefinition⟩,
    ⟨"Capability.peel", .userOperator⟩,
    ⟨"Capability.restorations", .userOperator⟩]
  requiredInstances := []
  derivedOperations := ["CT12.runLoop", "CT12.runReference",
    "CT12.run_iterations_bounded", "CT12.run_trace_bounded",
    demandResidualKindId, tierResidualKindId]

/-- Minimal author contract for canonical head/tail list peeling. -/
def listPeelingCapabilityProfile : Core.CapabilityProfile where
  capabilityId := "StructuralExhaustion.CT12.profile.listPeeling"
  tacticId := "CT12"
  requiredDefinitions := [
    ⟨"StructuralExhaustion.CT12.ListPeeling.Profile.Value", .userDefinition⟩]
  requiredInstances := []
  derivedOperations := [
    "StructuralExhaustion.CT12.ListPeeling.State",
    "StructuralExhaustion.CT12.ListPeeling.Peeled",
    "StructuralExhaustion.CT12.ListPeeling.capability",
    "StructuralExhaustion.CT12.ListPeeling.initialState",
    "StructuralExhaustion.CT12.ListPeeling.run",
    "StructuralExhaustion.CT12.ListPeeling.run_terminal_exhausted",
    "StructuralExhaustion.CT12.ListPeeling.run_iterations_eq_length"]

/-- Maximum finite disjoint packing followed by a vertex-linearly bounded
list-peeling execution. -/
def disjointPackingCapabilityProfile : Core.CapabilityProfile where
  capabilityId := "StructuralExhaustion.CT12.profile.disjointPacking"
  tacticId := "CT12"
  requiredDefinitions := [
    ⟨"StructuralExhaustion.Core.FiniteDisjointPacking.Profile.vertices",
      .userDefinition⟩,
    ⟨"StructuralExhaustion.Core.FiniteDisjointPacking.Profile.finiteItems",
      .userDefinition⟩,
    ⟨"StructuralExhaustion.Core.FiniteDisjointPacking.Profile.support",
      .userOperator⟩,
    ⟨"StructuralExhaustion.Core.FiniteDisjointPacking.Profile.representative",
      .userOperator⟩,
    ⟨"StructuralExhaustion.Core.FiniteDisjointPacking.Profile.representative_mem",
      .userDefinition⟩]
  requiredInstances := []
  derivedOperations := [
    "StructuralExhaustion.Core.FiniteDisjointPacking.Profile.maximum",
    "StructuralExhaustion.Core.FiniteDisjointPacking.Profile.maximum_spec",
    "StructuralExhaustion.Core.FiniteDisjointPacking.Profile.maximum_saturated",
    "StructuralExhaustion.Core.FiniteDisjointPacking.Profile.values_length_le_vertices",
    "StructuralExhaustion.CT12.DisjointPacking.Profile.run",
    "StructuralExhaustion.CT12.DisjointPacking.Profile.run_iterations_eq_values",
    "StructuralExhaustion.CT12.DisjointPacking.Profile.verifiedStage",
    "StructuralExhaustion.CT12.DisjointPacking.Profile.run_total"]

def nodeAutomationContracts : List Core.NodeAutomationContract := [
  ⟨"CT12.entry", .definitional, [],
    [⟨"Input.state", .derivedFromPredecessor⟩,
      ⟨"Input.load", .derivedFromPredecessor⟩], [],
    [⟨"CT12.Input", .derivedFromPredecessor⟩], []⟩,
  ⟨"CT12.decide.saturation", .verifiedComputation, [],
    [⟨"current.state", .derivedFromPredecessor⟩,
      ⟨"current.load", .derivedFromPredecessor⟩], [],
    [⟨"Capability.State 0", .derivedFromPredecessor⟩,
      ⟨"Capability.State (n + 1)", .derivedFromPredecessor⟩], []⟩,
  ⟨"CT12.compute.peel", .verifiedComputation,
    [⟨"Capability.peel", .userOperator⟩],
    [⟨"Capability.State (n + 1)", .derivedFromPredecessor⟩], [],
    [⟨"Capability.Peeled state", .derivedByComputation⟩], []⟩,
  ⟨"CT12.compute.restoration", .verifiedComputation,
    [⟨"Capability.restorations", .userOperator⟩],
    [⟨"Capability.Peeled state", .derivedFromPredecessor⟩],
    ["CT12.RestorationOptions.first_mem"],
    [⟨"CT12.RestorationOptions", .derivedByComputation⟩,
      ⟨"CT12.Restoration", .policySelected⟩], []⟩,
  ⟨"CT12.verify.decrease", .genericTheorem, [],
    [⟨"Capability.Peeled state", .derivedFromPredecessor⟩,
      ⟨"CT12.Restoration.continue.next", .derivedFromPredecessor⟩,
      ⟨"CT12.Restoration.continue.state", .derivedFromPredecessor⟩,
      ⟨"CT12.Restoration.continue.decreases", .derivedFromPredecessor⟩],
    [],
    [⟨"CT12.Graph.Edge.loopBack", .generatedAudit⟩,
      ⟨"CT12.Graph.Edge.loopBack_decreases", .derivedByGenericTheorem⟩], []⟩]

syntax "ct12_execute " term " on " term : term
macro_rules
  | `(ct12_execute $cap:term on $input:term) => `(CT12.run $cap $input)
syntax "ct12 " term " on " term : tactic
macro_rules
  | `(tactic| ct12 $cap:term on $input:term) =>
      `(tactic| exact CT12.run_verified $cap $input)
syntax "ct12_total " term " on " term : tactic
macro_rules
  | `(tactic| ct12_total $cap:term on $input:term) =>
      `(tactic| exact CT12.run_total $cap $input)

end StructuralExhaustion.CT12
