import StructuralExhaustion.CT9.ParityCapacityOne

namespace StructuralExhaustion.CT9

def overloadResidualKindId := "CT9.residual.overload"

def residualKindContracts : List Core.ResidualKindContract := [{
  residualKindId := overloadResidualKindId
  leanType := "StructuralExhaustion.CT9.OverloadResidual"
  semanticFields := [
    ⟨"label", "Capability.Label", .derivedByGenericSearch⟩,
    ⟨"overloaded", "capacity label < fibreCount label", .derivedByGenericTheorem⟩]
  inheritedContext := .branch
}]

def capabilityContract : Core.CapabilityContract where
  capabilityId := "StructuralExhaustion.CT9.reference"
  tacticId := "CT9"
  requiredDefinitions := [
    ⟨"Capability.Item", .userDefinition⟩,
    ⟨"Capability.Label", .userDefinition⟩,
    ⟨"Capability.labels", .userFiniteEnumeration⟩,
    ⟨"Capability.label", .userOperator⟩,
    ⟨"Capability.capacity", .userOperator⟩]
  requiredInstances := []
  derivedOperations := ["CT9.fibre", "CT9.fibre_nodup", "CT9.totalCapacity",
    "CT9.analyze", "CT9.overloadOfTotalCapacityLtCardinality",
    "CT9.SameLabelPair",
    "CT9.OverloadResidual.sameLabelPairOfCapacityOne",
    "CT9.BoundedCertificate.cardinality_le_totalCapacity",
    "CT9.BoundedCertificate.false_of_totalCapacity_lt_cardinality",
    "CT9.run_terminal_overloaded_of_totalCapacity_lt_cardinality",
    "CT9.run_trace_overloaded_of_totalCapacity_lt_cardinality",
    "CT9.runOverloadResidualOfTotalCapacityLtCardinality",
    "CT9.runSameLabelPairOfTotalCapacityLtCardinality",
    "CT9.OverloadedRun", "CT9.OverloadedRun.residual",
    "CT9.runOverloadedOfTotalCapacityLtCardinality",
    "CT9.parityCapacityOne", "CT9.SameParityPair",
    "CT9.ParityCapacityOneRun",
    "CT9.runParityCapacityOneOfThreeLeCardinality",
    "CT9.runReference", overloadResidualKindId]

/-- Minimal capability profile for the two-parity, capacity-one specialization.
The item collection and its three-element lower bound are invocation data. -/
def parityCapacityOneCapabilityProfile : Core.CapabilityProfile where
  capabilityId := "StructuralExhaustion.CT9.profile.parityCapacityOne"
  tacticId := "CT9"
  requiredDefinitions := [
    ⟨"StructuralExhaustion.CT9.ParityCapacityOneSpec.Item", .userDefinition⟩,
    ⟨"StructuralExhaustion.CT9.ParityCapacityOneSpec.rank", .userOperator⟩
  ]
  requiredInstances := []
  derivedOperations := [
    "StructuralExhaustion.CT9.ParityCapacityOneSpec.capability",
    "StructuralExhaustion.CT9.parityCapacityOne",
    "StructuralExhaustion.CT9.totalCapacity_parityCapacityOne",
    "StructuralExhaustion.CT9.runParityCapacityOneOfThreeLeCardinality",
    "StructuralExhaustion.CT9.ParityCapacityOneRun.pair"
  ]

def nodeAutomationContracts : List Core.NodeAutomationContract := [
  ⟨"CT9.entry", .definitional, [],
    [⟨"Input.context", .derivedFromPredecessor⟩,
      ⟨"Input.items", .derivedFromPredecessor⟩], [],
    [⟨"CT9.Input", .derivedFromPredecessor⟩], []⟩,
  ⟨"CT9.compute.partition", .definitional, [], [], [],
    [⟨"CT9.Graph.Edge.partitioned", .generatedAudit⟩], []⟩,
  ⟨"CT9.search.firstOverload", .finiteSearch,
    [⟨"Capability.capacity", .userOperator⟩,
      ⟨"Capability.labels", .userFiniteEnumeration⟩,
      ⟨"Capability.label", .userOperator⟩],
    [⟨"Input.items", .derivedFromPredecessor⟩,
      ⟨"CT9.fibre", .derivedByComputation⟩],
    ["CT9.mem_own_fibre", "Core.FiniteSearch.search"],
    [⟨"CT9.Decision", .derivedByGenericSearch⟩,
      ⟨"CT9.OverloadResidual", .derivedByGenericSearch⟩,
      ⟨"CT9.BoundedCertificate", .derivedByGenericTheorem⟩], []⟩]

syntax "ct9_execute " term " on " term : term
macro_rules
  | `(ct9_execute $cap:term on $input:term) => `(CT9.run $cap $input)
syntax "ct9 " term " on " term : tactic
macro_rules
  | `(tactic| ct9 $cap:term on $input:term) =>
      `(tactic| exact CT9.run_verified $cap $input)
syntax "ct9_total " term " on " term : tactic
macro_rules
  | `(tactic| ct9_total $cap:term on $input:term) =>
      `(tactic| exact CT9.run_total $cap $input)

end StructuralExhaustion.CT9
