import StructuralExhaustion.CT4.Graph
import StructuralExhaustion.CT4.Nodes

namespace StructuralExhaustion.CT4

structure CorePlan (F : Framework) (input : Input F) where
  scope : Nodes.Scope.Plan F input
  assignment : Nodes.Assignment.Plan F input
  availability : Nodes.Availability.Plan F input
  fibres : Nodes.Fibres.Plan F input
  comparison : Nodes.Comparison.Plan F input

inductive RawOutcome (F : Framework) (input : Input F) :
    Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : RawOutcome F input .scope
  | ct13 {assignment : AssignmentState F input}
      (payload : CT13Payload F input assignment) : RawOutcome F input .ct13
  | ct9 {assignment : AssignmentState F input}
      {total : TotalAssignmentState F input assignment}
      (payload : CT9Payload F input total) : RawOutcome F input .ct9
  | c4 {assignment : AssignmentState F input}
      {total : TotalAssignmentState F input assignment}
      {bounded : BoundedFibreState F input total}
      (certificate : C4Certificate F input bounded) : RawOutcome F input .c4
  | ct14 {assignment : AssignmentState F input}
      {total : TotalAssignmentState F input assignment}
      {bounded : BoundedFibreState F input total}
      (payload : CT14Payload F input bounded) : RawOutcome F input .ct14

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
      let assignment := Nodes.Assignment.run plan.assignment scopeState
      match Nodes.Availability.run plan.availability assignment with
      | .missing payload =>
          ⟨.ct13,
            .cons .beginScope
              (.cons (.scopeReady scopeState)
                (.cons (.assignmentCertified assignment)
                  (.cons (.availabilityMissing payload) (.nil .ct13Terminal)))),
            .ct13 payload⟩
      | .total total =>
          match Nodes.Fibres.run plan.fibres total with
          | .overloaded payload =>
              ⟨.ct9,
                .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.assignmentCertified assignment)
                      (.cons (.availabilityTotal total)
                        (.cons (.fibresOverloaded payload) (.nil .ct9Terminal))))),
                .ct9 payload⟩
          | .bounded bounded =>
              match Nodes.Comparison.run plan.comparison bounded with
              | .close certificate =>
                  ⟨.c4,
                    .cons .beginScope
                      (.cons (.scopeReady scopeState)
                        (.cons (.assignmentCertified assignment)
                          (.cons (.availabilityTotal total)
                            (.cons (.fibresBounded bounded)
                              (.cons (.comparisonClose certificate) (.nil .c4Terminal)))))),
                    .c4 certificate⟩
              | .residual payload =>
                  ⟨.ct14,
                    .cons .beginScope
                      (.cons (.scopeReady scopeState)
                        (.cons (.assignmentCertified assignment)
                          (.cons (.availabilityTotal total)
                            (.cons (.fibresBounded bounded)
                              (.cons (.comparisonResidual payload) (.nil .ct14Terminal)))))),
                    .ct14 payload⟩

inductive Outcome (F : Framework) (input : Input F) (port : Port F input) :
    Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : Outcome F input port .scope
  | ct13 {assignment : AssignmentState F input}
      (payload : CT13Payload F input assignment)
      (accepted : port.accepts (.ct13 payload)) : Outcome F input port .ct13
  | ct9 {assignment : AssignmentState F input}
      {total : TotalAssignmentState F input assignment}
      (payload : CT9Payload F input total)
      (accepted : port.accepts (.ct9 payload)) : Outcome F input port .ct9
  | c4 {assignment : AssignmentState F input}
      {total : TotalAssignmentState F input assignment}
      {bounded : BoundedFibreState F input total}
      (certificate : C4Certificate F input bounded) : Outcome F input port .c4
  | ct14 {assignment : AssignmentState F input}
      {total : TotalAssignmentState F input assignment}
      {bounded : BoundedFibreState F input total}
      (payload : CT14Payload F input bounded)
      (accepted : port.accepts (.ct14 payload)) : Outcome F input port .ct14

def OutcomeClaim {F : Framework} {input : Input F} {port : Port F input}
    {terminal : Graph.Terminal} : Outcome F input port terminal → Prop
  | .scope _ => ¬ ScopeReadyAt F input
  | .ct13 payload _ => port.accepts (.ct13 payload)
  | .ct9 payload _ => port.accepts (.ct9 payload)
  | .c4 _ => F.C4Claim input.G input.branch
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
  | ⟨_, path, .ct13 payload⟩ =>
      ⟨.ct13, path, .ct13 payload (handoff.accept (.ct13 payload))⟩
  | ⟨_, path, .ct9 payload⟩ =>
      ⟨.ct9, path, .ct9 payload (handoff.accept (.ct9 payload))⟩
  | ⟨_, path, .c4 certificate⟩ => ⟨.c4, path, .c4 certificate⟩
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

end StructuralExhaustion.CT4
