import StructuralExhaustion.CT1.Types

namespace StructuralExhaustion.CT1.Graph

/-! Evidence-carrying semantic control-flow graph for CT1. -/

inductive NodeId where
  | entry
  | scopeDecision
  | scopeTerminal
  | equivalenceCertification
  | realizationDecision
  | c1Terminal
  | payloadDecision
  | ct2Terminal
  | ct3Terminal
  | ct4Terminal
  | ct5Terminal
  | ct6Terminal
  | ct17Terminal
  deriving Repr, DecidableEq

namespace NodeId

def code : NodeId → String
  | .entry => "CT1.entry"
  | .scopeDecision => "CT1.decide.scope"
  | .scopeTerminal => "CT1.terminal.scope"
  | .equivalenceCertification => "CT1.certify.equivalence"
  | .realizationDecision => "CT1.decide.realization"
  | .c1Terminal => "CT1.terminal.c1"
  | .payloadDecision => "CT1.decide.payload"
  | .ct2Terminal => "CT1.terminal.ct2"
  | .ct3Terminal => "CT1.terminal.ct3"
  | .ct4Terminal => "CT1.terminal.ct4"
  | .ct5Terminal => "CT1.terminal.ct5"
  | .ct6Terminal => "CT1.terminal.ct6"
  | .ct17Terminal => "CT1.terminal.ct17"

end NodeId

inductive Terminal where
  | scope
  | c1
  | ct2
  | ct3
  | ct4
  | ct5
  | ct6
  | ct17
  deriving Repr, DecidableEq

namespace Terminal

def nodeId : Terminal → NodeId
  | .scope => .scopeTerminal
  | .c1 => .c1Terminal
  | .ct2 => .ct2Terminal
  | .ct3 => .ct3Terminal
  | .ct4 => .ct4Terminal
  | .ct5 => .ct5Terminal
  | .ct6 => .ct6Terminal
  | .ct17 => .ct17Terminal

end Terminal

inductive Edge (F : Framework) (input : Input F) : NodeId → NodeId → Type where
  | beginScope :
      Edge F input .entry .scopeDecision
  | scopeExit (candidate : ScopeCandidate F input) :
      Edge F input .scopeDecision .scopeTerminal
  | scopeReady (state : ScopedState F input) :
      Edge F input .scopeDecision .equivalenceCertification
  | equivalenceCertified (state : EquivalenceState F input) :
      Edge F input .equivalenceCertification .realizationDecision
  | realizationHit (certificate : C1Certificate F input) :
      Edge F input .realizationDecision .c1Terminal
  | realizationAvoiding (state : AvoidingState F input) :
      Edge F input .realizationDecision .payloadDecision
  | payloadToCT2 {avoiding : AvoidingState F input}
      (payload : CT2Payload F input avoiding) :
      Edge F input .payloadDecision .ct2Terminal
  | payloadToCT3 {avoiding : AvoidingState F input}
      (payload : CT3Payload F input avoiding) :
      Edge F input .payloadDecision .ct3Terminal
  | payloadToCT4 {avoiding : AvoidingState F input}
      (payload : CT4Payload F input avoiding) :
      Edge F input .payloadDecision .ct4Terminal
  | payloadToCT5 {avoiding : AvoidingState F input}
      (payload : CT5Payload F input avoiding) :
      Edge F input .payloadDecision .ct5Terminal
  | payloadToCT6 {avoiding : AvoidingState F input}
      (payload : CT6Payload F input avoiding) :
      Edge F input .payloadDecision .ct6Terminal
  | payloadToCT17 {avoiding : AvoidingState F input}
      (payload : CT17Payload F input avoiding) :
      Edge F input .payloadDecision .ct17Terminal

namespace Edge

def source {F : Framework} {input : Input F} {src dst : NodeId}
    (_edge : Edge F input src dst) : NodeId := src

def target {F : Framework} {input : Input F} {src dst : NodeId}
    (_edge : Edge F input src dst) : NodeId := dst

end Edge

inductive Path (F : Framework) (input : Input F) : NodeId → NodeId → Type where
  | nil (node : NodeId) : Path F input node node
  | cons {first second last : NodeId} :
      Edge F input first second →
      Path F input second last →
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

end StructuralExhaustion.CT1.Graph
