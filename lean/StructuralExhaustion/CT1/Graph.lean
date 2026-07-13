import StructuralExhaustion.CT1.State

namespace StructuralExhaustion.CT1.Graph

universe uAmbient uBranch uIndex uWitness

/-- Exact automation-first CT1 nodes. -/
inductive NodeId where
  | entry
  | equivalenceCertification
  | realizationDecision
  | c1Terminal
  | avoidingTerminal
  deriving Repr, DecidableEq

namespace NodeId

def code : NodeId → String
  | .entry => "CT1.entry"
  | .equivalenceCertification => "CT1.certify.equivalence"
  | .realizationDecision => "CT1.decide.realization"
  | .c1Terminal => "CT1.terminal.c1"
  | .avoidingTerminal => "CT1.terminal.avoiding"

end NodeId

inductive Terminal where
  | c1
  | avoiding
  deriving Repr, DecidableEq

namespace Terminal

def nodeId : Terminal → NodeId
  | .c1 => .c1Terminal
  | .avoiding => .avoidingTerminal

end Terminal

/-- Every nontrivial transition carries the exact evidence emitted by its
source node. -/
inductive Edge {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec.{uIndex, uWitness} P) (input : Input P) :
    NodeId → NodeId → Type (max (uIndex + 1) (uWitness + 1)) where
  | beginEquivalence :
      Edge S input .entry .equivalenceCertification
  | equivalenceCertified
      (equivalence : EquivalenceState S input) :
      Edge S input .equivalenceCertification .realizationDecision
  | realizationHit
      {equivalence : EquivalenceState S input}
      (certificate : C1Certificate S input equivalence) :
      Edge S input .realizationDecision .c1Terminal
  | realizationAvoiding
      {equivalence : EquivalenceState S input}
      (state : AvoidingState S input equivalence) :
      Edge S input .realizationDecision .avoidingTerminal

namespace Edge

def source {P : Core.Problem.{uAmbient, uBranch}}
    {S : Spec.{uIndex, uWitness} P} {input : Input P}
    {first second : NodeId} (_edge : Edge S input first second) : NodeId :=
  first

def target {P : Core.Problem.{uAmbient, uBranch}}
    {S : Spec.{uIndex, uWitness} P} {input : Input P}
    {first second : NodeId} (_edge : Edge S input first second) : NodeId :=
  second

end Edge

/-- A dependent execution path; ill-composed traces are unrepresentable. -/
inductive Path {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec.{uIndex, uWitness} P) (input : Input P) :
    NodeId → NodeId → Type (max (uIndex + 1) (uWitness + 1)) where
  | nil (node : NodeId) : Path S input node node
  | cons {first second last : NodeId} :
      Edge S input first second →
      Path S input second last →
      Path S input first last

namespace Path

def trace {P : Core.Problem.{uAmbient, uBranch}}
    {S : Spec.{uIndex, uWitness} P} {input : Input P}
    {first last : NodeId} : Path S input first last → List NodeId
  | .nil node => [node]
  | .cons edge rest => edge.source :: rest.trace

end Path

def ValidTrace {P : Core.Problem.{uAmbient, uBranch}}
    {S : Spec.{uIndex, uWitness} P} {input : Input P}
    (nodes : List NodeId) : Prop :=
  ∃ terminal : Terminal,
    ∃ path : Path S input .entry terminal.nodeId,
      path.trace = nodes

end StructuralExhaustion.CT1.Graph
