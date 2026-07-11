import StructuralExhaustion.CT5.Graph
import StructuralExhaustion.CT5.Nodes

namespace StructuralExhaustion.CT5

structure CorePlan (F : Framework) (input : Input F) where
  scope : Nodes.Scope.Plan F input
  locality : Nodes.Locality.Plan F input
  deficit : Nodes.Deficit.Plan F input
  summation : Nodes.Summation.Plan F input
  comparison : Nodes.Comparison.Plan F input

inductive RawOutcome (F : Framework) (input : Input F) :
    Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : RawOutcome F input .scope
  | ct11 {locality : LocalityState F input}
      (payload : CT11Payload F input locality) : RawOutcome F input .ct11
  | c4 {locality : LocalityState F input}
      {ledger : LocalLedgerState F input locality}
      {summation : SummationState F input ledger}
      (certificate : C4Certificate F input summation) : RawOutcome F input .c4
  | ct4 {locality : LocalityState F input}
      {ledger : LocalLedgerState F input locality}
      {summation : SummationState F input ledger}
      (payload : CT4Payload F input summation) : RawOutcome F input .ct4
  | ct14 {locality : LocalityState F input}
      {ledger : LocalLedgerState F input locality}
      {summation : SummationState F input ledger}
      (payload : CT14Payload F input summation) : RawOutcome F input .ct14

structure CoreResult (F : Framework) (input : Input F) where
  terminal : Graph.Terminal
  path : Graph.Path F input .entry terminal.nodeId
  outcome : RawOutcome F input terminal

namespace CoreResult

def trace {F : Framework} {input : Input F} (result : CoreResult F input) :
    List Graph.NodeId := result.path.trace

end CoreResult

def runCore (F : Framework) (input : Input F)
    (plan : CorePlan F input) : CoreResult F input :=
  let entry := Nodes.Entry.run input
  match Nodes.Scope.run entry plan.scope with
  | .exit candidate =>
      ⟨.scope,
        .cons .beginScope (.cons (.scopeExit candidate) (.nil .scopeTerminal)),
        .scope candidate⟩
  | .ready scopeState =>
      let locality := Nodes.Locality.run plan.locality scopeState
      match Nodes.Deficit.run plan.deficit locality with
      | .toCT11 payload =>
          ⟨.ct11,
            .cons .beginScope
              (.cons (.scopeReady scopeState)
                (.cons (.localityCertified locality)
                  (.cons (.deficitToCT11 payload) (.nil .ct11Terminal)))),
            .ct11 payload⟩
      | .ledger ledger =>
          let summation := Nodes.Summation.run plan.summation ledger
          match Nodes.Comparison.run plan.comparison summation with
          | .close certificate =>
              ⟨.c4,
                .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.localityCertified locality)
                      (.cons (.deficitLedger ledger)
                        (.cons (.summationCertified summation)
                          (.cons (.comparisonClose certificate) (.nil .c4Terminal)))))),
                .c4 certificate⟩
          | .toCT4 payload =>
              ⟨.ct4,
                .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.localityCertified locality)
                      (.cons (.deficitLedger ledger)
                        (.cons (.summationCertified summation)
                          (.cons (.comparisonToCT4 payload) (.nil .ct4Terminal)))))),
                .ct4 payload⟩
          | .toCT14 payload =>
              ⟨.ct14,
                .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.localityCertified locality)
                      (.cons (.deficitLedger ledger)
                        (.cons (.summationCertified summation)
                          (.cons (.comparisonToCT14 payload) (.nil .ct14Terminal)))))),
                .ct14 payload⟩

inductive Outcome (F : Framework) (input : Input F) (port : Port F input) :
    Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : Outcome F input port .scope
  | ct11 {locality : LocalityState F input}
      (payload : CT11Payload F input locality)
      (accepted : port.accepts (.ct11 payload)) : Outcome F input port .ct11
  | c4 {locality : LocalityState F input}
      {ledger : LocalLedgerState F input locality}
      {summation : SummationState F input ledger}
      (certificate : C4Certificate F input summation) : Outcome F input port .c4
  | ct4 {locality : LocalityState F input}
      {ledger : LocalLedgerState F input locality}
      {summation : SummationState F input ledger}
      (payload : CT4Payload F input summation)
      (accepted : port.accepts (.ct4 payload)) : Outcome F input port .ct4
  | ct14 {locality : LocalityState F input}
      {ledger : LocalLedgerState F input locality}
      {summation : SummationState F input ledger}
      (payload : CT14Payload F input summation)
      (accepted : port.accepts (.ct14 payload)) : Outcome F input port .ct14

def OutcomeClaim {F : Framework} {input : Input F} {port : Port F input}
    {terminal : Graph.Terminal} : Outcome F input port terminal → Prop
  | .scope _ => ¬ ScopeReadyAt F input
  | .ct11 payload _ => port.accepts (.ct11 payload)
  | .c4 _ => F.ct4.C4Claim input.G input.branch
  | .ct4 payload _ => port.accepts (.ct4 payload)
  | .ct14 payload _ => port.accepts (.ct14 payload)

structure ExecutionResult (F : Framework) (input : Input F)
    (port : Port F input) where
  terminal : Graph.Terminal
  path : Graph.Path F input .entry terminal.nodeId
  outcome : Outcome F input port terminal

namespace ExecutionResult

def trace {F : Framework} {input : Input F} {port : Port F input}
    (result : ExecutionResult F input port) : List Graph.NodeId :=
  result.path.trace

end ExecutionResult

def certify (F : Framework) (input : Input F) (port : Port F input)
    (handoff : HandoffPlan F input port)
    (result : CoreResult F input) : ExecutionResult F input port :=
  match result with
  | ⟨_, path, .scope candidate⟩ => ⟨.scope, path, .scope candidate⟩
  | ⟨_, path, .ct11 payload⟩ =>
      ⟨.ct11, path, .ct11 payload (handoff.accept (.ct11 payload))⟩
  | ⟨_, path, .c4 certificate⟩ => ⟨.c4, path, .c4 certificate⟩
  | ⟨_, path, .ct4 payload⟩ =>
      ⟨.ct4, path, .ct4 payload (handoff.accept (.ct4 payload))⟩
  | ⟨_, path, .ct14 payload⟩ =>
      ⟨.ct14, path, .ct14 payload (handoff.accept (.ct14 payload))⟩

def runTraced (F : Framework) (input : Input F)
    (plan : CorePlan F input) (port : Port F input)
    (handoff : HandoffPlan F input port) : ExecutionResult F input port :=
  certify F input port handoff (runCore F input plan)

def SomeOutcome (F : Framework) (input : Input F) (port : Port F input) :=
  Σ terminal : Graph.Terminal, Outcome F input port terminal

def run (F : Framework) (input : Input F)
    (plan : CorePlan F input) (port : Port F input)
    (handoff : HandoffPlan F input port) : SomeOutcome F input port :=
  let result := runTraced F input plan port handoff
  ⟨result.terminal, result.outcome⟩

end StructuralExhaustion.CT5
