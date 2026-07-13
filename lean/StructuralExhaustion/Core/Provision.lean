import Std

namespace StructuralExhaustion.Core

/-! Audit metadata for separating proof-instance inputs from derived data. -/

/-- How a declaration, field, or proof enters the automation-first machine. -/
inductive Provision where
  | frameworkConstant
  | userDefinition
  | userOperator
  | userFiniteEnumeration
  | typeclassInferred
  | derivedDefinitionally
  | derivedFromPredecessor
  | derivedByGenericSearch
  | derivedByGenericTheorem
  | derivedByComputation
  | instanceBridge
  | optimizedImplementation
  | policySelected
  | generatedRoute
  | generatedAudit
  deriving Repr, DecidableEq

namespace Provision

def all : List Provision := [
  .frameworkConstant,
  .userDefinition,
  .userOperator,
  .userFiniteEnumeration,
  .typeclassInferred,
  .derivedDefinitionally,
  .derivedFromPredecessor,
  .derivedByGenericSearch,
  .derivedByGenericTheorem,
  .derivedByComputation,
  .instanceBridge,
  .optimizedImplementation,
  .policySelected,
  .generatedRoute,
  .generatedAudit
]

/-- Stable spelling used by generated JSON artifacts. -/
def key : Provision → String
  | .frameworkConstant => "framework_constant"
  | .userDefinition => "user_definition"
  | .userOperator => "user_operator"
  | .userFiniteEnumeration => "user_finite_enumeration"
  | .typeclassInferred => "typeclass_inferred"
  | .derivedDefinitionally => "derived_definitionally"
  | .derivedFromPredecessor => "derived_from_predecessor"
  | .derivedByGenericSearch => "derived_by_generic_search"
  | .derivedByGenericTheorem => "derived_by_generic_theorem"
  | .derivedByComputation => "derived_by_computation"
  | .instanceBridge => "instance_bridge"
  | .optimizedImplementation => "optimized_implementation"
  | .policySelected => "policy_selected"
  | .generatedRoute => "generated_route"
  | .generatedAudit => "generated_audit"

/-- Whether the proof instance must supply the referenced object. -/
def isAuthorProvided : Provision → Bool
  | .userDefinition
  | .userOperator
  | .userFiniteEnumeration
  | .instanceBridge
  | .optimizedImplementation => true
  | _ => false

/-- Whether the object is constructed by reusable framework mechanism. -/
def isFrameworkDerived : Provision → Bool
  | .frameworkConstant
  | .typeclassInferred
  | .derivedDefinitionally
  | .derivedFromPredecessor
  | .derivedByGenericSearch
  | .derivedByGenericTheorem
  | .derivedByComputation
  | .policySelected
  | .generatedRoute
  | .generatedAudit => true
  | _ => false

end Provision

/-- Execution mechanism used by a node. -/
inductive ExecutionClass where
  | definitional
  | typeclass
  | finiteSearch
  | verifiedComputation
  | genericTheorem
  | instanceBridge
  | interactiveFallback
  deriving Repr, DecidableEq

namespace ExecutionClass

def all : List ExecutionClass := [
  .definitional,
  .typeclass,
  .finiteSearch,
  .verifiedComputation,
  .genericTheorem,
  .instanceBridge,
  .interactiveFallback
]

def key : ExecutionClass → String
  | .definitional => "definitional"
  | .typeclass => "typeclass"
  | .finiteSearch => "finiteSearch"
  | .verifiedComputation => "verifiedComputation"
  | .genericTheorem => "genericTheorem"
  | .instanceBridge => "instanceBridge"
  | .interactiveFallback => "interactiveFallback"

end ExecutionClass

/-- A stable declaration reference with its provision classification. -/
structure ProvisionedRef where
  ref : String
  provision : Provision
  deriving Repr, DecidableEq

/-- Lean-side automation metadata exported for one node. -/
structure NodeAutomationContract where
  nodeId : String
  executionClass : ExecutionClass
  authorInputs : List ProvisionedRef
  derivedInputs : List ProvisionedRef
  frameworkTheorems : List String
  /-- Exact states, decisions, certificates, or residuals produced by this
  node.  These are outputs of reusable framework code, never caller-supplied
  completed decisions. -/
  generatedOutputs : List ProvisionedRef := []
  manualObligations : List String
  deriving Repr, DecidableEq

namespace NodeAutomationContract

/-- Inputs synthesized by typeclass search. -/
def inferredInputs (contract : NodeAutomationContract) : List ProvisionedRef :=
  contract.derivedInputs.filter fun input =>
    input.provision == .typeclassInferred

/-- Inputs whose values are fixed by the immediately preceding typed state. -/
def predecessorInputs (contract : NodeAutomationContract) : List ProvisionedRef :=
  contract.derivedInputs.filter fun input =>
    input.provision == .derivedFromPredecessor

/-- Framework-created dependencies other than inferred or predecessor state. -/
def frameworkDerivedInputs
    (contract : NodeAutomationContract) : List ProvisionedRef :=
  contract.derivedInputs.filter fun input =>
    input.provision != .typeclassInferred &&
      input.provision != .derivedFromPredecessor

/-- Complete dependency projection used by audit artifacts. -/
def transitiveDependencies
    (contract : NodeAutomationContract) : List ProvisionedRef :=
  contract.authorInputs ++ contract.derivedInputs ++
    contract.frameworkTheorems.map fun theoremName =>
      ⟨theoremName, .derivedByGenericTheorem⟩

end NodeAutomationContract

/-- Lean-side automation metadata exported for one tactic capability. -/
structure CapabilityContract where
  capabilityId : String
  tacticId : String
  requiredDefinitions : List ProvisionedRef
  requiredInstances : List String
  derivedOperations : List String
  deriving Repr, DecidableEq

/-- A tactic may expose narrower capability profiles for common structural
shapes.  The primary capability contract remains the fully general API;
profiles record which author fields a framework constructor replaces. -/
abbrev CapabilityProfile := CapabilityContract

/-- One semantic field carried by a residual. -/
structure ResidualFieldContract where
  fieldName : String
  leanType : String
  provision : Provision
  deriving Repr, DecidableEq

/-- Which shared context a semantic residual inherits without reconstruction. -/
inductive InheritedContext where
  | branch
  | avoidingBranch
  | minimalCounterexampleBranch
  | loopState
  deriving Repr, DecidableEq

namespace InheritedContext

def key : InheritedContext → String
  | .branch => "branch"
  | .avoidingBranch => "avoidingBranch"
  | .minimalCounterexampleBranch => "minimalCounterexampleBranch"
  | .loopState => "loopState"

end InheritedContext

/-- Stable, router-facing contract for one semantic residual family. -/
structure ResidualKindContract where
  residualKindId : String
  leanType : String
  semanticFields : List ResidualFieldContract
  inheritedContext : InheritedContext
  deriving Repr, DecidableEq

/-- Deterministic policy class used when a residual has enabled routes. -/
inductive RouteSelectionClass where
  | forced
  | priority
  | costOrdered
  | manualPolicy
  deriving Repr, DecidableEq

namespace RouteSelectionClass

def key : RouteSelectionClass → String
  | .forced => "forced"
  | .priority => "priority"
  | .costOrdered => "costOrdered"
  | .manualPolicy => "manualPolicy"

end RouteSelectionClass

/-- How a route obtains the semantic datum from which the target trigger is
constructed.  Capability discovery needs no route-specific adapter.  A
problem-semantic adapter is an explicit, reusable input to the route rule. -/
inductive RouteSemanticDiscovery where
  | capabilityDiscovery
  | problemSemanticAdapter (adapterType : String)
  deriving Repr, DecidableEq

namespace RouteSemanticDiscovery

/-- Stable spelling used by catalog consumers. -/
def key : RouteSemanticDiscovery → String
  | .capabilityDiscovery => "capabilityDiscovery"
  | .problemSemanticAdapter _ => "problemSemanticAdapter"

/-- The problem-authored adapter interface, when semantic discovery cannot be
obtained from the target capability itself. -/
def adapterType? : RouteSemanticDiscovery → Option String
  | .capabilityDiscovery => none
  | .problemSemanticAdapter adapterType => some adapterType

end RouteSemanticDiscovery

/-- Typed roles for every problem-specific value accepted by a route API. -/
inductive RouteProblemInput where
  | targetCapability
  | minimalityKernel
  | semanticDiscoveryAdapter
  deriving Repr, DecidableEq

namespace RouteProblemInput

def key : RouteProblemInput → String
  | .targetCapability => "targetCapability"
  | .minimalityKernel => "minimalityKernel"
  | .semanticDiscoveryAdapter => "semanticDiscoveryAdapter"

end RouteProblemInput

/-- Framework obligations discharged once by every registered route rule. -/
inductive RouteFrameworkResponsibility where
  | routeRuleConstruction
  | targetContextConstruction
  | triggerConstruction
  | soundnessProof
  | contextPreservationProof
  | provenanceProof
  deriving Repr, DecidableEq

namespace RouteFrameworkResponsibility

def all : List RouteFrameworkResponsibility := [
  .routeRuleConstruction,
  .targetContextConstruction,
  .triggerConstruction,
  .soundnessProof,
  .contextPreservationProof,
  .provenanceProof
]

def key : RouteFrameworkResponsibility → String
  | .routeRuleConstruction => "routeRuleConstruction"
  | .targetContextConstruction => "targetContextConstruction"
  | .triggerConstruction => "triggerConstruction"
  | .soundnessProof => "soundnessProof"
  | .contextPreservationProof => "contextPreservationProof"
  | .provenanceProof => "provenanceProof"

end RouteFrameworkResponsibility

/-- Lean-owned route metadata.  The authoring boundary states exactly which
problem values the generic rule accepts and whether semantic discovery needs
a problem adapter.  Route construction, trigger construction, and all listed
correctness proofs remain framework-owned. -/
structure RouteContract where
  routeId : String
  sourceResidualKind : String
  targetTacticId : String
  discovery : String
  triggerConstructor : String
  soundnessTheorem : String
  contextPreservationTheorem : String
  provenanceTheorem : String
  selectionClass : RouteSelectionClass
  semanticDiscovery : RouteSemanticDiscovery
  problemSpecificInputs : List RouteProblemInput
  deriving Repr, DecidableEq

end StructuralExhaustion.Core
