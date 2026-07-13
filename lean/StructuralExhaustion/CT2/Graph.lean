import StructuralExhaustion.CT2.Search

namespace StructuralExhaustion.CT2.Graph

universe uAmbient uBranch uPiece uInterface uAbstract uContext uCandidate

/-! The automation-first CT2 graph.  Every nontrivial edge carries the exact
evidence returned by its framework node. -/

inductive NodeId where
  | entry
  | deletionDecision
  | replacementAnalysis
  | deletionC2Terminal
  | replacementC2Terminal
  | separatingTerminal
  | criticalityTerminal
  deriving Repr, DecidableEq

namespace NodeId

def code : NodeId → String
  | .entry => "CT2.entry"
  | .deletionDecision => "CT2.decide.deletion"
  | .replacementAnalysis => "CT2.search.replacements"
  | .deletionC2Terminal => "CT2.terminal.c2.deletion"
  | .replacementC2Terminal => "CT2.terminal.c2.replacement"
  | .separatingTerminal => "CT2.terminal.residual.separatingContext"
  | .criticalityTerminal => "CT2.terminal.residual.criticality"

end NodeId

inductive Terminal where
  | deletionC2
  | replacementC2
  | separating
  | criticality
  deriving Repr, DecidableEq

namespace Terminal

def nodeId : Terminal → NodeId
  | .deletionC2 => .deletionC2Terminal
  | .replacementC2 => .replacementC2Terminal
  | .separating => .separatingTerminal
  | .criticality => .criticalityTerminal

def code : Terminal → String
  | .deletionC2 => "c2.deletion"
  | .replacementC2 => "c2.replacement"
  | .separating => "residual.separatingContext"
  | .criticality => "residual.criticality"

end Terminal

variable {P : Core.Problem.{uAmbient, uBranch}}
variable {Target : P.Ambient → Prop}
variable (capability : Capability.{uAmbient, uBranch, uPiece, uInterface,
  uAbstract, uContext, uCandidate} P Target)
variable (ctx : Core.MinimalCounterexampleContext P Target)
variable (input : Input capability ctx)

inductive Edge : NodeId → NodeId → Type _ where
  | beginDeletion : Edge .entry .deletionDecision
  | deletionCloses
      (witness : DeletionWitness capability ctx input) :
      Edge .deletionDecision .deletionC2Terminal
  | deletionCritical
      (state : DeletionCriticalState capability ctx input) :
      Edge .deletionDecision .replacementAnalysis
  | replacementCloses
      (witness : ReplacementWitness capability ctx input) :
      Edge .replacementAnalysis .replacementC2Terminal
  | replacementSeparating
      (residual : SeparatingContextResidual capability ctx input) :
      Edge .replacementAnalysis .separatingTerminal
  | replacementCritical
      (residual : CriticalityResidual capability ctx input) :
      Edge .replacementAnalysis .criticalityTerminal

namespace Edge

def source {start finish : NodeId} (_edge : Edge capability ctx input start finish) :
    NodeId := start

def target {start finish : NodeId} (_edge : Edge capability ctx input start finish) :
    NodeId := finish

end Edge

inductive Path : NodeId → NodeId → Type _ where
  | nil (node : NodeId) : Path node node
  | cons {first second last : NodeId} :
      Edge capability ctx input first second →
      Path second last → Path first last

namespace Path

def trace {first last : NodeId} : Path capability ctx input first last → List NodeId
  | .nil node => [node]
  | .cons edge rest => edge.source :: rest.trace

theorem startsAt {last : NodeId}
    (path : Path capability ctx input .entry last) : path.trace.head? = some .entry := by
  cases path with
  | nil => rfl
  | cons edge rest => rfl

end Path

def ValidTrace (nodes : List NodeId) : Prop :=
  ∃ terminal : Terminal,
    ∃ path : Path capability ctx input .entry terminal.nodeId,
      path.trace = nodes

end StructuralExhaustion.CT2.Graph
