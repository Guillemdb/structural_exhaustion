import StructuralExhaustion.CT4.Search

namespace StructuralExhaustion.CT4.Graph

inductive NodeId where
  | entry | assignment | availability | fibres | comparison
  | missingTerminal | overloadTerminal | c4Terminal | capacityTerminal
  deriving Repr, DecidableEq
namespace NodeId
def code : NodeId → String
  | .entry => "CT4.entry"
  | .assignment => "CT4.compute.assignment"
  | .availability => "CT4.search.availability"
  | .fibres => "CT4.compute.fibres"
  | .comparison => "CT4.decide.capacity"
  | .missingTerminal => "CT4.terminal.residual.missingPayer"
  | .overloadTerminal => "CT4.terminal.residual.overloadedFibre"
  | .c4Terminal => "CT4.terminal.c4"
  | .capacityTerminal => "CT4.terminal.residual.capacity"
end NodeId
inductive Terminal where | missing | overload | c4 | capacity
  deriving Repr, DecidableEq
namespace Terminal
def nodeId : Terminal → NodeId
  | .missing => .missingTerminal
  | .overload => .overloadTerminal
  | .c4 => .c4Terminal
  | .capacity => .capacityTerminal
end Terminal

variable {P : Core.Problem} (S : Spec P) (capability : Capability S)
variable (input : Input P)
inductive Edge : NodeId → NodeId → Type _ where
  | beginAssignment : Edge .entry .assignment
  | assigned (state : AssignmentState S capability input) :
      Edge .assignment .availability
  | missing (residual : MissingPayerResidual S input) :
      Edge .availability .missingTerminal
  | total (state : TotalAssignmentState S capability input) :
      Edge .availability .fibres
  | overloaded (residual : OverloadedFibreResidual S capability input) :
      Edge .fibres .overloadTerminal
  | bounded (state : BoundedFibreState S capability input) :
      Edge .fibres .comparison
  | c4 (certificate : C4Certificate S capability input) :
      Edge .comparison .c4Terminal
  | capacity (residual : CapacityResidual S capability input) :
      Edge .comparison .capacityTerminal
namespace Edge
def source {a b} (_ : Edge S capability input a b) := a
end Edge
inductive Path : NodeId → NodeId → Type _ where
  | nil (node) : Path node node
  | cons {a b c} : Edge S capability input a b → Path b c → Path a c
namespace Path
def trace {a b} : Path S capability input a b → List NodeId
  | .nil node => [node]
  | .cons edge rest => edge.source :: rest.trace
end Path
def ValidTrace (nodes : List NodeId) : Prop :=
  ∃ terminal : Terminal, ∃ path : Path S capability input .entry terminal.nodeId,
    path.trace = nodes

end StructuralExhaustion.CT4.Graph
