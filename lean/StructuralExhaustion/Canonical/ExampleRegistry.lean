import Lean

namespace StructuralExhaustion.Canonical

/-!
Lean-owned descriptions of the worked examples displayed by the web explorer.

The descriptions contain only semantic references.  `ExampleExport` resolves
those references against the compiled environment and enriches them with
types, source modules, and declaration ranges.
-/

/-- Whether an example or workflow reaches its advertised mathematical target. -/
inductive ExampleCompletion where
  | complete
  | partialProof
  deriving Repr, DecidableEq

namespace ExampleCompletion

def key : ExampleCompletion → String
  | .complete => "complete"
  | .partialProof => "partial"

end ExampleCompletion

/-- The semantic role of a node in an example workflow. -/
inductive ExampleStageKind where
  | problem
  | tactic
  | adapter
  | certificate
  | theorem
  | fixture
  deriving Repr, DecidableEq

namespace ExampleStageKind

def key : ExampleStageKind → String
  | .problem => "problem"
  | .tactic => "tactic"
  | .adapter => "adapter"
  | .certificate => "certificate"
  | .theorem => "theorem"
  | .fixture => "fixture"

end ExampleStageKind

/-- The precise claim made by an arrow in an example workflow. -/
inductive ExampleLinkKind where
  /-- An executable profile registered in a typed CT transition family. -/
  | registeredTransition
  /-- Problem-level orchestration of framework tactics without a registered transition. -/
  | frameworkComposition
  /-- A proof object or certificate is consumed by the target stage. -/
  | proofData
  /-- A tactic validates a certificate that is already available. -/
  | validation
  /-- An execution audits a schedule but does not itself construct the result. -/
  | scheduleAudit
  /-- Two stages are instantiated from the same problem data, not pipelined. -/
  | sharedProblem
  deriving Repr, DecidableEq

namespace ExampleLinkKind

def key : ExampleLinkKind → String
  | .registeredTransition => "registeredTransition"
  | .frameworkComposition => "frameworkComposition"
  | .proofData => "proofData"
  | .validation => "validation"
  | .scheduleAudit => "scheduleAudit"
  | .sharedProblem => "sharedProblem"

end ExampleLinkKind

/-- How a Lean proof step relates to the mathematical manuscript. -/
inductive ExampleCorrespondenceKind where
  | exact
  | equivalentEncoding
  | specialization
  | composite
  | support
  | partialCoverage
  deriving Repr, DecidableEq

namespace ExampleCorrespondenceKind

def key : ExampleCorrespondenceKind → String
  | .exact => "exact"
  | .equivalentEncoding => "equivalentEncoding"
  | .specialization => "specialization"
  | .composite => "composite"
  | .support => "support"
  | .partialCoverage => "partial"

end ExampleCorrespondenceKind

/-- Implementation state of one manuscript-facing proof step. -/
inductive ExampleImplementationStatus where
  | implemented
  | next
  | notStarted
  deriving Repr, DecidableEq

namespace ExampleImplementationStatus

def key : ExampleImplementationStatus → String
  | .implemented => "implemented"
  | .next => "next"
  | .notStarted => "notStarted"

end ExampleImplementationStatus

/-- Verification state of one manuscript-node obligation.  Unlike a proof-step
status, this is property-level: a diagram node is complete only when every
obligation attached to that node is proved. -/
inductive ExampleNodeObligationStatus where
  | isProved
  | isPartial
  | isMissing
  deriving Repr, DecidableEq

namespace ExampleNodeObligationStatus

def key : ExampleNodeObligationStatus → String
  | .isProved => "proved"
  | .isPartial => "partial"
  | .isMissing => "missing"

end ExampleNodeObligationStatus

/-- The mathematical or verification role shared by a group of declarations. -/
inductive ExampleDeclarationRole where
  | mathematicalDefinition
  | semanticTheorem
  | encodingBridge
  | tacticExecution
  | executionAudit
  | soundnessTotality
  | workBound
  | compositionProvenance
  | frameworkInterface
  | externalTheorem
  | fixture
  deriving Repr, DecidableEq

namespace ExampleDeclarationRole

def key : ExampleDeclarationRole → String
  | .mathematicalDefinition => "mathematicalDefinition"
  | .semanticTheorem => "semanticTheorem"
  | .encodingBridge => "encodingBridge"
  | .tacticExecution => "tacticExecution"
  | .executionAudit => "executionAudit"
  | .soundnessTotality => "soundnessTotality"
  | .workBound => "workBound"
  | .compositionProvenance => "compositionProvenance"
  | .frameworkInterface => "frameworkInterface"
  | .externalTheorem => "externalTheorem"
  | .fixture => "fixture"

end ExampleDeclarationRole

/-- Stable semantic reference into a mathematical manuscript. -/
structure ExampleManuscriptReference where
  label : String
  title : String
  nodeIds : List Nat := []
  deriving Repr, DecidableEq

/-- A set of Lean declarations serving one precisely described proof role. -/
structure ExampleDeclarationGroup where
  groupId : String
  title : String
  role : ExampleDeclarationRole
  explanation : String
  declarations : List Lean.Name
  deriving Repr, DecidableEq

/-- One manuscript-facing proof step and its complete displayed Lean evidence. -/
structure ExampleProofStepDescriptor where
  stepId : String
  stageId? : Option String := none
  title : String
  plainExplanation : String
  formalStatement : String
  status : ExampleImplementationStatus
  correspondence : ExampleCorrespondenceKind
  manuscriptRefs : List ExampleManuscriptReference := []
  declarationGroups : List ExampleDeclarationGroup := []
  scopeNotes : String
  workBound : String
  deriving Repr, DecidableEq

/-- One stable, paper-scoped responsibility of an original diagram node.

`evidenceStepIds` names the Lean-owned manuscript proof steps that implement
the responsibility.  Export validation rejects dangling evidence, evidence
that does not cite the same node, and green-node claims with unfinished
obligations. -/
structure ExampleNodeObligationDescriptor where
  nodeId : Nat
  obligationId : String
  title : String
  statement : String
  status : ExampleNodeObligationStatus
  evidenceStepIds : List String := []
  deriving Repr, DecidableEq

namespace ExampleNodeObligationDescriptor

/-- Build a proved property ledger for one node from one Lean proof step. -/
def provedForStep (nodeId : Nat) (stepId : String)
    (specifications : List (String × String)) :
    List ExampleNodeObligationDescriptor :=
  specifications.map fun specification => {
    nodeId := nodeId
    obligationId := specification.1
    title := specification.1
    statement := specification.2
    status := .isProved
    evidenceStepIds := [stepId]
  }

/-- Build a partially discharged property ledger from one evidence step. -/
def partialForStep (nodeId : Nat) (stepId : String)
    (specifications : List (String × String)) :
    List ExampleNodeObligationDescriptor :=
  specifications.map fun specification => {
    nodeId := nodeId
    obligationId := specification.1
    title := specification.1
    statement := specification.2
    status := .isPartial
    evidenceStepIds := [stepId]
  }

/-- Build an explicitly open property ledger without fabricating evidence. -/
def missing (nodeId : Nat) (specifications : List (String × String)) :
    List ExampleNodeObligationDescriptor :=
  specifications.map fun specification => {
    nodeId := nodeId
    obligationId := specification.1
    title := specification.1
    statement := specification.2
    status := .isMissing
  }

end ExampleNodeObligationDescriptor

/-- Manuscript and proof-step metadata used by the example theorem companion. -/
structure ExampleManuscriptDescriptor where
  title : String
  path : String
  /-- Diagram nodes whose complete displayed assertion is formalized.  A proof
  step may cite additional nodes for partial coverage and navigation without
  promoting those whole nodes to verified status. -/
  formalizedNodeIds : List Nat := []
  /-- Complete property-level ledgers for nodes that have undergone an audited
  obligation decomposition.  Nodes not yet migrated retain the legacy
  whole-cell status until their ledger is added. -/
  nodeObligations : List ExampleNodeObligationDescriptor := []
  proofSteps : List ExampleProofStepDescriptor
  deriving Repr, DecidableEq

/-- One inspectable unit in a workflow. -/
structure ExampleStageDescriptor where
  stageId : String
  title : String
  summary : String
  kind : ExampleStageKind
  tacticId? : Option String := none
  primaryDeclaration : Lean.Name
  evidenceDeclarations : List Lean.Name := []
  deriving Repr, DecidableEq

/-- A typed relationship between two workflow stages. -/
structure ExampleLinkDescriptor where
  linkId : String
  sourceStageId : String
  targetStageId : String
  kind : ExampleLinkKind
  label : String
  description : String
  transitionProfileId? : Option String := none
  /-- Framework-owned declarations that execute or certify this connection.
  Every ordinary direct transition between distinct CT stages must name at
  least one. A registered transition must leave this empty: the canonical
  transition registry resolves its executable owner from
  `transitionProfileId?` during export. -/
  automationDeclarations : List Lean.Name := []
  evidenceDeclarations : List Lean.Name := []
  deriving Repr, DecidableEq

/-- One independently selectable proof, audit, or compression workflow. -/
structure ExampleWorkflowDescriptor where
  workflowId : String
  title : String
  purpose : String
  completion : ExampleCompletion
  stages : List ExampleStageDescriptor
  links : List ExampleLinkDescriptor
  deriving Repr, DecidableEq

/-- A problem-specific declaration and the framework declaration it instantiates. -/
structure ExampleInterfaceBinding where
  bindingId : String
  stageId : String
  tacticId : String
  role : String
  description : String
  problemDeclaration : Lean.Name
  frameworkDeclaration : Lean.Name
  deriving Repr, DecidableEq

/-- The complete Lean-owned catalog row for an external worked example. -/
structure ExampleDescriptor where
  exampleId : String
  title : String
  summary : String
  proofStatus : ExampleCompletion
  workflows : List ExampleWorkflowDescriptor
  interfaceBindings : List ExampleInterfaceBinding
  manuscript? : Option ExampleManuscriptDescriptor := none
  deriving Repr, DecidableEq

end StructuralExhaustion.Canonical
