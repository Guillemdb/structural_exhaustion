import StructuralExhaustion.CT12.Types

namespace StructuralExhaustion.CT12.Graph

inductive NodeId where
  | entry
  | scopeDecision
  | scopeTerminal
  | measureCertification
  | saturationDecision
  | c4Terminal
  | peelCertification
  | restorationDecision
  | ct4Terminal
  | ct13Terminal
  | decreaseCertification
  deriving Repr, DecidableEq

namespace NodeId
def code : NodeId → String
  | .entry => "CT12.entry" | .scopeDecision => "CT12.decide.scope"
  | .scopeTerminal => "CT12.terminal.scope"
  | .measureCertification => "CT12.certify.measure"
  | .saturationDecision => "CT12.decide.saturation"
  | .c4Terminal => "CT12.terminal.c4"
  | .peelCertification => "CT12.certify.peel"
  | .restorationDecision => "CT12.decide.restoration"
  | .ct4Terminal => "CT12.terminal.ct4" | .ct13Terminal => "CT12.terminal.ct13"
  | .decreaseCertification => "CT12.certify.decrease"
end NodeId

inductive Terminal where
  | scope
  | c4
  | ct4
  | ct13
  deriving Repr, DecidableEq
namespace Terminal
def nodeId : Terminal → NodeId
  | .scope => .scopeTerminal | .c4 => .c4Terminal
  | .ct4 => .ct4Terminal | .ct13 => .ct13Terminal
end Terminal

inductive Edge (F : Framework) (input : Input F) : NodeId → NodeId → Type where
  | beginScope : Edge F input .entry .scopeDecision
  | scopeExit (candidate : ScopeCandidate F input) : Edge F input .scopeDecision .scopeTerminal
  | scopeReady (scope : ScopedState F input) : Edge F input .scopeDecision .measureCertification
  | measureCertified (state : LoopState F input input.load) :
      Edge F input .measureCertification .saturationDecision
  | saturationClose {load : Nat} {state : LoopState F input load}
      (certificate : C4Certificate F input state) :
      Edge F input .saturationDecision .c4Terminal
  | saturationPeel {load : Nat} {state : LoopState F input load}
      (peelable : PeelableState F input state) :
      Edge F input .saturationDecision .peelCertification
  | peelCertified {load : Nat} {state : LoopState F input load}
      {peelable : PeelableState F input state} (peeled : PeeledState F input peelable) :
      Edge F input .peelCertification .restorationDecision
  | restorationToCT4 {load : Nat} {state : LoopState F input load}
      {peelable : PeelableState F input state} {peeled : PeeledState F input peelable}
      (payload : CT4Payload F input peeled) : Edge F input .restorationDecision .ct4Terminal
  | restorationToCT13 {load : Nat} {state : LoopState F input load}
      {peelable : PeelableState F input state} {peeled : PeeledState F input peelable}
      (payload : CT13Payload F input peeled) : Edge F input .restorationDecision .ct13Terminal
  | restorationContinue {load : Nat} {state : LoopState F input load}
      {peelable : PeelableState F input state} {peeled : PeeledState F input peelable}
      {next : Nat} (restored : RestoredState F input peeled next) :
      Edge F input .restorationDecision .decreaseCertification
  | decreaseLoop {load : Nat} {state : LoopState F input load}
      {peelable : PeelableState F input state} {peeled : PeeledState F input peelable}
      {next : Nat} {restored : RestoredState F input peeled next}
      (decreased : DecreasedState F input restored) :
      Edge F input .decreaseCertification .saturationDecision

namespace Edge
def source {F : Framework} {input : Input F} {src dst : NodeId}
    (_edge : Edge F input src dst) : NodeId := src

/-- Every runtime back edge contains the strict-decrease proof required by S-Meas. -/
theorem loop_decreases {F : Framework} {input : Input F}
    (edge : Edge F input .decreaseCertification .saturationDecision) :
    ∃ current next : Nat, next < current := by
  cases edge with
  | decreaseLoop decreased => exact ⟨_, _, decreased.decreases⟩
end Edge

inductive Path (F : Framework) (input : Input F) : NodeId → NodeId → Type where
  | nil (node : NodeId) : Path F input node node
  | cons {first second last : NodeId} : Edge F input first second →
      Path F input second last → Path F input first last
namespace Path
def trace {F : Framework} {input : Input F} {first last : NodeId} :
    Path F input first last → List NodeId
  | .nil node => [node]
  | .cons edge rest => edge.source :: rest.trace
end Path
def ValidTrace {F : Framework} {input : Input F} (nodes : List NodeId) : Prop :=
  ∃ terminal : Terminal, ∃ path : Path F input .entry terminal.nodeId, path.trace = nodes

end StructuralExhaustion.CT12.Graph
