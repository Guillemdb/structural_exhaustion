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
  | frameworkTransition
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
  .frameworkTransition,
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
  | .frameworkTransition => "framework_transition"
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
  | .frameworkTransition
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

/-- Stable, transition-facing contract for one semantic residual family. -/
structure ResidualKindContract where
  residualKindId : String
  leanType : String
  semanticFields : List ResidualFieldContract
  inheritedContext : InheritedContext
  deriving Repr, DecidableEq

/-- Deterministic policy class used when a residual enables an executable
transition profile. -/
inductive TransitionSelectionClass where
  | forced
  | priority
  | costOrdered
  | manualPolicy
  deriving Repr, DecidableEq

namespace TransitionSelectionClass

def key : TransitionSelectionClass → String
  | .forced => "forced"
  | .priority => "priority"
  | .costOrdered => "costOrdered"
  | .manualPolicy => "manualPolicy"

end TransitionSelectionClass

/-- How a transition obtains the semantic datum from which the target trigger
is constructed.  Capability discovery needs no profile-specific adapter.  A
problem-semantic adapter is an explicit, reusable profile input. -/
inductive TransitionSemanticDiscovery where
  | capabilityDiscovery
  | problemSemanticAdapter (adapterType : String)
  deriving Repr, DecidableEq

namespace TransitionSemanticDiscovery

/-- Stable spelling used by catalog consumers. -/
def key : TransitionSemanticDiscovery → String
  | .capabilityDiscovery => "capabilityDiscovery"
  | .problemSemanticAdapter _ => "problemSemanticAdapter"

/-- The problem-authored adapter interface, when semantic discovery cannot be
obtained from the target capability itself. -/
def adapterType? : TransitionSemanticDiscovery → Option String
  | .capabilityDiscovery => none
  | .problemSemanticAdapter adapterType => some adapterType

end TransitionSemanticDiscovery

/-- Typed roles for every problem-specific value accepted by a transition
profile constructor. -/
inductive TransitionProblemInput where
  | targetCapability
  | minimalityKernel
  | semanticDiscoveryAdapter
  deriving Repr, DecidableEq

namespace TransitionProblemInput

def key : TransitionProblemInput → String
  | .targetCapability => "targetCapability"
  | .minimalityKernel => "minimalityKernel"
  | .semanticDiscoveryAdapter => "semanticDiscoveryAdapter"

end TransitionProblemInput

/-- Metadata for a non-CT semantic producer handoff.  This record is not an
executable CT transition and deliberately cannot appear in the registered
transition registry. -/
structure SemanticHandoffContract where
  handoffId : String
  sourceResidualKind : String
  targetConsumerId : String
  discovery : String
  consumerInputConstructor : String
  soundnessTheorem : String
  contextPreservationTheorem : String
  provenanceTheorem : String
  deriving Repr, DecidableEq

/-- Catalog contract for one executable profile of a typed CT-to-CT family.
Its owner is a `Core.Routing.CTTransition`, execution is mandatory, and its
output is the full accumulated ledger.  Multiple profiles may share the same
source/target pair while retaining distinct mathematical trigger and result
types. -/
structure CTTransitionProfileContract where
  profileId : String
  sourceTacticId : String
  targetTacticId : String
  sourceResidualKind : String
  targetExecutableInterface : String
  transitionConstructor : String
  advanceExecutor : String
  selectionClass : TransitionSelectionClass
  semanticDiscovery : TransitionSemanticDiscovery
  problemSpecificInputs : List TransitionProblemInput
  deriving Repr, DecidableEq

namespace CTTransitionProfileContract

/-- The unique family identity; profiles never redefine the meaning of their
source and target CTs. -/
def familyId (contract : CTTransitionProfileContract) : String :=
  contract.sourceTacticId ++ "->" ++ contract.targetTacticId

end CTTransitionProfileContract

/-- Obligations discharged uniformly by the executable transition kernel. -/
inductive CTTransitionFrameworkResponsibility where
  | exactSourceLedger
  | semanticDiscovery
  | targetContextConstruction
  | triggerConstruction
  | targetExecution
  | accumulatedLedgerOutput
  | transitionProvenance
  deriving Repr, DecidableEq

namespace CTTransitionFrameworkResponsibility

def all : List CTTransitionFrameworkResponsibility := [
  .exactSourceLedger,
  .semanticDiscovery,
  .targetContextConstruction,
  .triggerConstruction,
  .targetExecution,
  .accumulatedLedgerOutput,
  .transitionProvenance
]

def key : CTTransitionFrameworkResponsibility → String
  | .exactSourceLedger => "exactSourceLedger"
  | .semanticDiscovery => "semanticDiscovery"
  | .targetContextConstruction => "targetContextConstruction"
  | .triggerConstruction => "triggerConstruction"
  | .targetExecution => "targetExecution"
  | .accumulatedLedgerOutput => "accumulatedLedgerOutput"
  | .transitionProvenance => "transitionProvenance"

end CTTransitionFrameworkResponsibility

end StructuralExhaustion.Core
