import StructuralExhaustion.CT1.TargetEncoding
import StructuralExhaustion.Core.Provision

namespace StructuralExhaustion.CT1

/-- Proof-author surface and framework-derived CT1 operations. -/
def capabilityContract : Core.CapabilityContract where
  capabilityId := "StructuralExhaustion.CT1.reference"
  tacticId := "CT1"
  requiredDefinitions := [
    ⟨"StructuralExhaustion.CT1.Spec.TestIndex", .userDefinition⟩,
    ⟨"StructuralExhaustion.CT1.Spec.Witness", .userDefinition⟩,
    ⟨"StructuralExhaustion.CT1.Spec.Realizes", .userDefinition⟩,
    ⟨"StructuralExhaustion.CT1.Capability.tests", .userFiniteEnumeration⟩,
    ⟨"StructuralExhaustion.CT1.Capability.witnesses", .userFiniteEnumeration⟩,
    ⟨"StructuralExhaustion.CT1.Capability.realizesDecidable", .instanceBridge⟩,
    ⟨"StructuralExhaustion.CT1.Capability.inputSize", .userOperator⟩,
    ⟨"StructuralExhaustion.CT1.Capability.workCoefficient", .userDefinition⟩,
    ⟨"StructuralExhaustion.CT1.Capability.workDegree", .userDefinition⟩,
    ⟨"StructuralExhaustion.CT1.Capability.workBound", .userDefinition⟩
  ]
  requiredInstances := [
    "StructuralExhaustion.CT1.Capability.realizesDecidable"
  ]
  derivedOperations := [
    "StructuralExhaustion.CT1.certifyEquivalence",
    "StructuralExhaustion.CT1.findRealization",
    "StructuralExhaustion.CT1.AvoidingState.ofNoRealization",
    "StructuralExhaustion.CT1.TargetBridge.target_of_publicTarget",
    "StructuralExhaustion.CT1.TargetBridge.publicTarget_of_target",
    "StructuralExhaustion.CT1.TargetBridge.publicTarget_of_c1",
    "StructuralExhaustion.CT1.TargetBridge.not_publicTarget_of_not_target",
    "StructuralExhaustion.CT1.TargetBridge.not_publicTarget_of_avoiding",
    "StructuralExhaustion.CT1.TargetBridge.target_mono_of_publicTarget_mono",
    "StructuralExhaustion.CT1.TargetBridge.publicTargetDecidable",
    "StructuralExhaustion.CT1.TargetEncoding.spec",
    "StructuralExhaustion.CT1.TargetEncoding.capability",
    "StructuralExhaustion.CT1.TargetEncoding.bridge",
    "StructuralExhaustion.CT1.Capability.polynomialBudget",
    "StructuralExhaustion.CT1.runC1OfRealization",
    "StructuralExhaustion.CT1.run",
    "StructuralExhaustion.CT1.run_verified",
    "StructuralExhaustion.CT1.run_terminal_c1_of_target",
    "StructuralExhaustion.CT1.run_terminal_c1_of_publicTarget",
    "StructuralExhaustion.CT1.run_trace_c1_of_target",
    "StructuralExhaustion.CT1.run_trace_c1_of_publicTarget",
    "StructuralExhaustion.CT1.runC1OfTarget",
    "StructuralExhaustion.CT1.runC1OfPublicTarget",
    "StructuralExhaustion.CT1.run_total"
  ]

/-- Minimal author contract for the common one-code public-target profile. -/
def targetEncodingCapabilityProfile : Core.CapabilityProfile where
  capabilityId := "StructuralExhaustion.CT1.profile.targetEncoding"
  tacticId := "CT1"
  requiredDefinitions := [
    ⟨"StructuralExhaustion.CT1.TargetEncoding.Code", .userDefinition⟩,
    ⟨"StructuralExhaustion.CT1.TargetEncoding.codes", .userFiniteEnumeration⟩,
    ⟨"StructuralExhaustion.CT1.TargetEncoding.Accepts", .userDefinition⟩,
    ⟨"StructuralExhaustion.CT1.TargetEncoding.acceptsDecidable",
      .instanceBridge⟩,
    ⟨"StructuralExhaustion.CT1.TargetEncoding.inputSize", .userOperator⟩,
    ⟨"StructuralExhaustion.CT1.TargetEncoding.workCoefficient", .userDefinition⟩,
    ⟨"StructuralExhaustion.CT1.TargetEncoding.workDegree", .userDefinition⟩,
    ⟨"StructuralExhaustion.CT1.TargetEncoding.workBound", .userDefinition⟩,
    ⟨"StructuralExhaustion.CT1.TargetEncoding.encode", .userOperator⟩,
    ⟨"StructuralExhaustion.CT1.TargetEncoding.decode", .userOperator⟩
  ]
  requiredInstances := [
    "StructuralExhaustion.CT1.TargetEncoding.acceptsDecidable"
  ]
  derivedOperations := [
    "StructuralExhaustion.CT1.TargetEncoding.spec",
    "StructuralExhaustion.CT1.TargetEncoding.capability",
    "StructuralExhaustion.CT1.TargetEncoding.bridge",
    "StructuralExhaustion.CT1.runC1OfPublicTarget"
  ]

/-- Minimal author contract for proof-carrying positive and negative target
execution without enumerating a code universe. -/
def targetCertificateCapabilityProfile : Core.CapabilityProfile where
  capabilityId := "StructuralExhaustion.CT1.profile.targetCertificate"
  tacticId := "CT1"
  requiredDefinitions := [
    ⟨"StructuralExhaustion.CT1.TargetCertificateEncoding.Code",
      .userDefinition⟩,
    ⟨"StructuralExhaustion.CT1.TargetCertificateEncoding.Accepts",
      .userDefinition⟩,
    ⟨"StructuralExhaustion.CT1.TargetCertificateEncoding.encode",
      .userOperator⟩,
    ⟨"StructuralExhaustion.CT1.TargetCertificateEncoding.decode",
      .userOperator⟩
  ]
  requiredInstances := []
  derivedOperations := [
    "StructuralExhaustion.CT1.TargetCertificateEncoding.spec",
    "StructuralExhaustion.CT1.TargetCertificateEncoding.bridge",
    "StructuralExhaustion.CT1.TargetCertificateEncoding.run",
    "StructuralExhaustion.CT1.TargetCertificateEncoding.runAvoiding",
    "StructuralExhaustion.CT1.executionOfRealization",
    "StructuralExhaustion.CT1.executionOfNoRealization",
    "StructuralExhaustion.CT1.certifiedC1Budget",
    "StructuralExhaustion.CT1.certifiedAvoidingBudget"
  ]

/-- CT1 exports its two semantic terminal payloads; downstream triggers remain
route-owned. -/
def residualKindContracts : List Core.ResidualKindContract := [
  {
    residualKindId := "CT1.terminal.c1"
    leanType := "StructuralExhaustion.CT1.Target"
    semanticFields := [
      ⟨"target", "∃ index witness, Realizes G index witness",
        .derivedByGenericTheorem⟩
    ]
    inheritedContext := .branch
  },
  {
    residualKindId := "CT1.residual.avoiding"
    leanType := "StructuralExhaustion.CT1.AvoidingState"
    semanticFields := [
      ⟨"noRealization", "∀ index witness, ¬ Realizes G index witness",
        .derivedByGenericTheorem⟩
    ]
    inheritedContext := .avoidingBranch
  }
]

def residualKindIds : List String :=
  residualKindContracts.map (·.residualKindId)

/-- Exact automation class and author/framework boundary for every CT1 node. -/
def nodeAutomationContracts : List Core.NodeAutomationContract := [
  {
    nodeId := "CT1.entry"
    executionClass := .definitional
    authorInputs := []
    derivedInputs := [⟨"input.context", .derivedFromPredecessor⟩]
    frameworkTheorems := []
    generatedOutputs := [⟨"StructuralExhaustion.CT1.Input", .derivedFromPredecessor⟩]
    manualObligations := []
  },
  {
    nodeId := "CT1.certify.equivalence"
    executionClass := .definitional
    authorInputs := [
      ⟨"StructuralExhaustion.CT1.Spec.TestIndex", .userDefinition⟩,
      ⟨"StructuralExhaustion.CT1.Spec.Witness", .userDefinition⟩,
      ⟨"StructuralExhaustion.CT1.Spec.Realizes", .userDefinition⟩
    ]
    derivedInputs := []
    frameworkTheorems := ["StructuralExhaustion.CT1.target_iff_realization"]
    generatedOutputs := [
      ⟨"StructuralExhaustion.CT1.EquivalenceState", .derivedDefinitionally⟩
    ]
    manualObligations := []
  },
  {
    nodeId := "CT1.decide.realization"
    executionClass := .finiteSearch
    authorInputs := [
      ⟨"StructuralExhaustion.CT1.Spec.TestIndex", .userDefinition⟩,
      ⟨"StructuralExhaustion.CT1.Spec.Witness", .userDefinition⟩,
      ⟨"StructuralExhaustion.CT1.Spec.Realizes", .userDefinition⟩,
      ⟨"StructuralExhaustion.CT1.Capability.tests", .userFiniteEnumeration⟩,
      ⟨"StructuralExhaustion.CT1.Capability.witnesses", .userFiniteEnumeration⟩,
      ⟨"StructuralExhaustion.CT1.Capability.realizesDecidable", .instanceBridge⟩,
      ⟨"StructuralExhaustion.CT1.Capability.inputSize", .userOperator⟩,
      ⟨"StructuralExhaustion.CT1.Capability.workCoefficient", .userDefinition⟩,
      ⟨"StructuralExhaustion.CT1.Capability.workDegree", .userDefinition⟩,
      ⟨"StructuralExhaustion.CT1.Capability.workBound", .userDefinition⟩
    ]
    derivedInputs := [
      ⟨"StructuralExhaustion.CT1.EquivalenceState",
        .derivedFromPredecessor⟩,
      ⟨"StructuralExhaustion.Core.FiniteSearch.dependentSearch",
        .derivedByGenericSearch⟩,
      ⟨"StructuralExhaustion.CT1.AvoidingState.ofNoRealization",
        .derivedByGenericTheorem⟩
    ]
    frameworkTheorems := [
      "StructuralExhaustion.Core.FiniteSearch.dependentSearch_sound",
      "StructuralExhaustion.Core.FiniteSearch.dependentSearch_complete"
    ]
    generatedOutputs := [
      ⟨"StructuralExhaustion.CT1.RealizationDecision",
        .derivedByGenericSearch⟩,
      ⟨"StructuralExhaustion.CT1.C1Certificate", .derivedByGenericSearch⟩,
      ⟨"StructuralExhaustion.CT1.AvoidingState", .derivedByGenericTheorem⟩
    ]
    manualObligations := []
  }
]

/-- Execute CT1 from its root input and reusable finite operations. -/
syntax (name := ct1Execute) "ct1_execute " term " using " term : term

macro_rules
  | `(ct1_execute $input:term using $ops:term) =>
      `(StructuralExhaustion.CT1.run _ $ops $input)

/-- Close the semantic soundness claim of a concrete CT1 execution. -/
syntax (name := ct1Tactic) "ct1 " term " using " term : tactic

macro_rules
  | `(tactic| ct1 $input:term using $ops:term) =>
      `(tactic| exact StructuralExhaustion.CT1.run_verified _ $ops $input)

/-- Close totality and trace validity for a concrete CT1 execution. -/
syntax (name := ct1TotalTactic) "ct1_total " term " using " term : tactic

macro_rules
  | `(tactic| ct1_total $input:term using $ops:term) =>
      `(tactic| exact StructuralExhaustion.CT1.run_total _ $ops $input)

end StructuralExhaustion.CT1
