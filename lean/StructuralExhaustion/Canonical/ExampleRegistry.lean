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
  /-- A route registered in `Canonical.routes`. -/
  | registeredRoute
  /-- Problem-level orchestration of framework tactics without a registered route. -/
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
  | .registeredRoute => "registeredRoute"
  | .frameworkComposition => "frameworkComposition"
  | .proofData => "proofData"
  | .validation => "validation"
  | .scheduleAudit => "scheduleAudit"
  | .sharedProblem => "sharedProblem"

end ExampleLinkKind

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
  routeId? : Option String := none
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
  deriving Repr, DecidableEq

end StructuralExhaustion.Canonical
