import StructuralExhaustion.CT4.Types

namespace StructuralExhaustion.CT4.Graph

inductive NodeId where
  | entry
  | scopeDecision
  | scopeTerminal
  | assignmentCertification
  | availabilityDecision
  | ct13Terminal
  | fibreDecision
  | ct9Terminal
  | comparisonDecision
  | c4Terminal
  | ct14Terminal
  deriving Repr, DecidableEq

namespace NodeId

def code : NodeId → String
  | .entry => "CT4.entry"
  | .scopeDecision => "CT4.decide.scope"
  | .scopeTerminal => "CT4.terminal.scope"
  | .assignmentCertification => "CT4.certify.assignment"
  | .availabilityDecision => "CT4.decide.availability"
  | .ct13Terminal => "CT4.terminal.ct13"
  | .fibreDecision => "CT4.decide.fibres"
  | .ct9Terminal => "CT4.terminal.ct9"
  | .comparisonDecision => "CT4.decide.comparison"
  | .c4Terminal => "CT4.terminal.c4"
  | .ct14Terminal => "CT4.terminal.ct14"

end NodeId

inductive Terminal where
  | scope
  | ct13
  | ct9
  | c4
  | ct14
  deriving Repr, DecidableEq

namespace Terminal

def nodeId : Terminal → NodeId
  | .scope => .scopeTerminal
  | .ct13 => .ct13Terminal
  | .ct9 => .ct9Terminal
  | .c4 => .c4Terminal
  | .ct14 => .ct14Terminal

end Terminal

inductive Edge (F : Framework) (input : Input F) : NodeId → NodeId → Type where
  | beginScope : Edge F input .entry .scopeDecision
  | scopeExit (candidate : ScopeCandidate F input) :
      Edge F input .scopeDecision .scopeTerminal
  | scopeReady (state : ScopedState F input) :
      Edge F input .scopeDecision .assignmentCertification
  | assignmentCertified (state : AssignmentState F input) :
      Edge F input .assignmentCertification .availabilityDecision
  | availabilityMissing {assignment : AssignmentState F input}
      (payload : CT13Payload F input assignment) :
      Edge F input .availabilityDecision .ct13Terminal
  | availabilityTotal {assignment : AssignmentState F input}
      (state : TotalAssignmentState F input assignment) :
      Edge F input .availabilityDecision .fibreDecision
  | fibresOverloaded {assignment : AssignmentState F input}
      {total : TotalAssignmentState F input assignment}
      (payload : CT9Payload F input total) :
      Edge F input .fibreDecision .ct9Terminal
  | fibresBounded {assignment : AssignmentState F input}
      {total : TotalAssignmentState F input assignment}
      (state : BoundedFibreState F input total) :
      Edge F input .fibreDecision .comparisonDecision
  | comparisonClose {assignment : AssignmentState F input}
      {total : TotalAssignmentState F input assignment}
      {bounded : BoundedFibreState F input total}
      (certificate : C4Certificate F input bounded) :
      Edge F input .comparisonDecision .c4Terminal
  | comparisonResidual {assignment : AssignmentState F input}
      {total : TotalAssignmentState F input assignment}
      {bounded : BoundedFibreState F input total}
      (payload : CT14Payload F input bounded) :
      Edge F input .comparisonDecision .ct14Terminal

namespace Edge

def source {F : Framework} {input : Input F} {src dst : NodeId}
    (_edge : Edge F input src dst) : NodeId := src

end Edge

inductive Path (F : Framework) (input : Input F) : NodeId → NodeId → Type where
  | nil (node : NodeId) : Path F input node node
  | cons {first second last : NodeId} :
      Edge F input first second → Path F input second last →
      Path F input first last

namespace Path

def trace {F : Framework} {input : Input F} {first last : NodeId} :
    Path F input first last → List NodeId
  | .nil node => [node]
  | .cons edge rest => edge.source :: rest.trace

end Path

def ValidTrace {F : Framework} {input : Input F} (nodes : List NodeId) : Prop :=
  ∃ terminal : Terminal,
    ∃ path : Path F input .entry terminal.nodeId,
      path.trace = nodes

end StructuralExhaustion.CT4.Graph
