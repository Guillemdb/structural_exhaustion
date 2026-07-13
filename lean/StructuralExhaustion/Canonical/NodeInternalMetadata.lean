import StructuralExhaustion.Core.Provision

namespace StructuralExhaustion.Canonical

/-!
Lean-owned presentation metadata for expanding one CT machine node into its
internal mathematical and implementation flow.  The source automation
contract remains authoritative; these descriptors are a deterministic,
auditable projection of that contract.
-/

inductive NodeInternalRole where
  | authorObject
  | inferredInstance
  | predecessorState
  | operation
  | theorem
  | output
  deriving Repr, DecidableEq

namespace NodeInternalRole

def key : NodeInternalRole → String
  | .authorObject => "authorObject"
  | .inferredInstance => "inferredInstance"
  | .predecessorState => "predecessorState"
  | .operation => "operation"
  | .theorem => "theorem"
  | .output => "output"

end NodeInternalRole

inductive NodeInternalRelation where
  | consumes
  | thenStep
  | produces
  | certifies
  deriving Repr, DecidableEq

namespace NodeInternalRelation

def key : NodeInternalRelation → String
  | .consumes => "consumes"
  | .thenStep => "then"
  | .produces => "produces"
  | .certifies => "certifies"

end NodeInternalRelation

structure NodeInternalStepDescriptor where
  stepId : String
  role : NodeInternalRole
  reference : Core.ProvisionedRef
  deriving Repr, DecidableEq

structure NodeInternalEdgeDescriptor where
  edgeId : String
  sourceStepId : String
  targetStepId : String
  relation : NodeInternalRelation
  deriving Repr, DecidableEq

structure NodeInternalFlowDescriptor where
  nodeId : String
  steps : List NodeInternalStepDescriptor
  edges : List NodeInternalEdgeDescriptor
  deriving Repr, DecidableEq

private def internalSteps
    (phasePrefix : String) (role : NodeInternalRole)
    (references : List Core.ProvisionedRef) : List NodeInternalStepDescriptor :=
  references.mapIdx fun index reference => {
    stepId := s!"{phasePrefix}.{index + 1}"
    role := role
    reference := reference
  }

private def relationBetween
    (source target : NodeInternalStepDescriptor) : NodeInternalRelation :=
  if target.role == .theorem then .thenStep
  else if target.role == .output && source.role == .theorem then .certifies
  else if target.role == .output then .produces
  else .consumes

private def phaseEdges
    (nodeId : String) (source target : List NodeInternalStepDescriptor) :
    List NodeInternalEdgeDescriptor :=
  source.flatMap fun first =>
    target.map fun second => {
      edgeId := s!"{nodeId}.internal.{first.stepId}-to-{second.stepId}"
      sourceStepId := first.stepId
      targetStepId := second.stepId
      relation := relationBetween first second
    }

private def adjacentPhaseEdges
    (nodeId : String) : List (List NodeInternalStepDescriptor) →
    List NodeInternalEdgeDescriptor
  | first :: second :: rest =>
      phaseEdges nodeId first second ++ adjacentPhaseEdges nodeId (second :: rest)
  | _ => []

/-- Build the stable, readable low-level flow directly from the exact
automation boundary already audited for a nonterminal node. -/
def NodeInternalFlowDescriptor.ofContract
    (contract : Core.NodeAutomationContract) : NodeInternalFlowDescriptor :=
  let author := internalSteps "author" .authorObject contract.authorInputs
  let inferred := internalSteps "inferred" .inferredInstance contract.inferredInputs
  let predecessor :=
    internalSteps "predecessor" .predecessorState contract.predecessorInputs
  let operations :=
    internalSteps "operation" .operation contract.frameworkDerivedInputs
  let theorems := internalSteps "theorem" .theorem <|
    contract.frameworkTheorems.map fun name =>
      Core.ProvisionedRef.mk name .derivedByGenericTheorem
  let outputs := internalSteps "output" .output contract.generatedOutputs
  let phases := [author ++ inferred ++ predecessor, operations, theorems, outputs]
    |>.filter fun phase => !phase.isEmpty
  {
    nodeId := contract.nodeId
    steps := phases.flatten
    edges := adjacentPhaseEdges contract.nodeId phases
  }

end StructuralExhaustion.Canonical
