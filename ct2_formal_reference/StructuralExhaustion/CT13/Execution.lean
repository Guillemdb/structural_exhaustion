import StructuralExhaustion.CT13.Nodes
import StructuralExhaustion.CT13.Graph

namespace StructuralExhaustion.CT13

structure CorePlan (F : Framework) (input : Input F) where
  scope : Nodes.Scope.Plan F input
  availability : Nodes.Availability.Plan F input
  tierOne : Nodes.TierOne.Plan F input
  tierOneRouting : Nodes.TierOneRouting.Plan F input
  fallback : Nodes.Fallback.Plan F input
  reconciliation : Nodes.Reconciliation.Plan F input
  comparison : Nodes.Comparison.Plan F input
  routing : Nodes.Routing.Plan F input

inductive RawOutcome (F : Framework) (input : Input F) : Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : RawOutcome F input .scope
  | ct4 {scope : ScopedState F input} {available : AvailableState F input scope}
      {tierOne : TierOneState F input available} (payload : CT4Payload F input tierOne) :
      RawOutcome F input .ct4
  | c4 {scope : ScopedState F input} {unavailable : UnavailableState F input scope}
      {fallback : FallbackState F input unavailable}
      {reconciled : ReconciledState F input fallback}
      (certificate : C4Certificate F input reconciled) : RawOutcome F input .c4
  | ct9 {scope : ScopedState F input} {unavailable : UnavailableState F input scope}
      {fallback : FallbackState F input unavailable}
      {overlap : OverlapState F input fallback} (payload : CT9Payload F input overlap) :
      RawOutcome F input .ct9
  | ct14 {scope : ScopedState F input} {unavailable : UnavailableState F input scope}
      {fallback : FallbackState F input unavailable}
      {overlap : OverlapState F input fallback} (payload : CT14Payload F input overlap) :
      RawOutcome F input .ct14

structure CoreResult (F : Framework) (input : Input F) where
  terminal : Graph.Terminal
  path : Graph.Path F input .entry terminal.nodeId
  outcome : RawOutcome F input terminal

def runCore (F : Framework) (input : Input F) (plan : CorePlan F input) :
    CoreResult F input :=
  let entry := Nodes.Entry.run input
  match Nodes.Scope.run entry plan.scope with
  | .exit candidate =>
      ⟨.scope, .cons .beginScope (.cons (.scopeExit candidate) (.nil .scopeTerminal)),
        .scope candidate⟩
  | .ready scope =>
      match Nodes.Availability.run plan.availability scope with
      | .available available =>
          let tierOne := Nodes.TierOne.run plan.tierOne available
          let payload := Nodes.TierOneRouting.run plan.tierOneRouting tierOne
          ⟨.ct4,
            .cons .beginScope
              (.cons (.scopeReady scope)
                (.cons (.availabilityYes available)
                  (.cons (.tierOneCertified tierOne)
                    (.cons (.tierOneToCT4 payload) (.nil .ct4Terminal))))),
            .ct4 payload⟩
      | .unavailable unavailable =>
          let fallback := Nodes.Fallback.run plan.fallback unavailable
          match Nodes.Reconciliation.run plan.reconciliation fallback with
          | .reconciled reconciled =>
              let certificate := Nodes.Comparison.run plan.comparison reconciled
              ⟨.c4,
                .cons .beginScope
                  (.cons (.scopeReady scope)
                    (.cons (.availabilityNo unavailable)
                      (.cons (.fallbackCertified fallback)
                        (.cons (.reconciliationYes reconciled)
                          (.cons (.comparisonClose certificate) (.nil .c4Terminal)))))),
                .c4 certificate⟩
          | .overlap overlap =>
              match Nodes.Routing.run plan.routing overlap with
              | .toCT9 payload =>
                  ⟨.ct9,
                    .cons .beginScope
                      (.cons (.scopeReady scope)
                        (.cons (.availabilityNo unavailable)
                          (.cons (.fallbackCertified fallback)
                            (.cons (.reconciliationOverlap overlap)
                              (.cons (.overlapToCT9 payload) (.nil .ct9Terminal)))))),
                    .ct9 payload⟩
              | .toCT14 payload =>
                  ⟨.ct14,
                    .cons .beginScope
                      (.cons (.scopeReady scope)
                        (.cons (.availabilityNo unavailable)
                          (.cons (.fallbackCertified fallback)
                            (.cons (.reconciliationOverlap overlap)
                              (.cons (.overlapToCT14 payload) (.nil .ct14Terminal)))))),
                    .ct14 payload⟩

inductive Outcome (F : Framework) (input : Input F) (port : Port F input) :
    Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : Outcome F input port .scope
  | ct4 {scope : ScopedState F input} {available : AvailableState F input scope}
      {tierOne : TierOneState F input available} (payload : CT4Payload F input tierOne)
      (accepted : port.accepts (.ct4 payload)) : Outcome F input port .ct4
  | c4 {scope : ScopedState F input} {unavailable : UnavailableState F input scope}
      {fallback : FallbackState F input unavailable}
      {reconciled : ReconciledState F input fallback}
      (certificate : C4Certificate F input reconciled) : Outcome F input port .c4
  | ct9 {scope : ScopedState F input} {unavailable : UnavailableState F input scope}
      {fallback : FallbackState F input unavailable}
      {overlap : OverlapState F input fallback} (payload : CT9Payload F input overlap)
      (accepted : port.accepts (.ct9 payload)) : Outcome F input port .ct9
  | ct14 {scope : ScopedState F input} {unavailable : UnavailableState F input scope}
      {fallback : FallbackState F input unavailable}
      {overlap : OverlapState F input fallback} (payload : CT14Payload F input overlap)
      (accepted : port.accepts (.ct14 payload)) : Outcome F input port .ct14

def OutcomeClaim {F : Framework} {input : Input F} {port : Port F input}
    {terminal : Graph.Terminal} : Outcome F input port terminal → Prop
  | .scope _ => ¬ ScopeReadyAt F input
  | .ct4 payload _ => port.accepts (.ct4 payload)
  | .c4 _ => F.entry.C4Claim input.G input.branch
  | .ct9 payload _ => port.accepts (.ct9 payload)
  | .ct14 payload _ => port.accepts (.ct14 payload)

structure ExecutionResult (F : Framework) (input : Input F) (port : Port F input) where
  terminal : Graph.Terminal
  path : Graph.Path F input .entry terminal.nodeId
  outcome : Outcome F input port terminal
namespace ExecutionResult
def trace {F : Framework} {input : Input F} {port : Port F input}
    (result : ExecutionResult F input port) : List Graph.NodeId := result.path.trace
end ExecutionResult

def certify (F : Framework) (input : Input F) (port : Port F input)
    (handoff : HandoffPlan F input port) (result : CoreResult F input) :
    ExecutionResult F input port :=
  match result with
  | ⟨_, path, .scope candidate⟩ => ⟨.scope, path, .scope candidate⟩
  | ⟨_, path, .ct4 payload⟩ =>
      ⟨.ct4, path, .ct4 payload (handoff.accept (.ct4 payload))⟩
  | ⟨_, path, .c4 certificate⟩ => ⟨.c4, path, .c4 certificate⟩
  | ⟨_, path, .ct9 payload⟩ =>
      ⟨.ct9, path, .ct9 payload (handoff.accept (.ct9 payload))⟩
  | ⟨_, path, .ct14 payload⟩ =>
      ⟨.ct14, path, .ct14 payload (handoff.accept (.ct14 payload))⟩

def runTraced (F : Framework) (input : Input F) (plan : CorePlan F input)
    (port : Port F input) (handoff : HandoffPlan F input port) :
    ExecutionResult F input port := certify F input port handoff (runCore F input plan)
def SomeOutcome (F : Framework) (input : Input F) (port : Port F input) :=
  Σ terminal : Graph.Terminal, Outcome F input port terminal
def run (F : Framework) (input : Input F) (plan : CorePlan F input)
    (port : Port F input) (handoff : HandoffPlan F input port) :
    SomeOutcome F input port :=
  let result := runTraced F input plan port handoff
  ⟨result.terminal, result.outcome⟩

end StructuralExhaustion.CT13
