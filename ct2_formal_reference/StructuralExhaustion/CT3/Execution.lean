import StructuralExhaustion.CT3.Graph
import StructuralExhaustion.CT3.Nodes

namespace StructuralExhaustion.CT3

structure CorePlan (F : Framework) (input : Input F) where
  scope : Nodes.Scope.Plan F input
  equivalence : Nodes.Equivalence.Plan F input
  compression : Nodes.Compression.Plan F input
  defect : Nodes.Defect.Plan F input
  table : Nodes.Table.Plan F input

inductive RawOutcome (F : Framework) (input : Input F) :
    Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : RawOutcome F input .scope
  | c2 {equivalence : EquivalenceState F input}
      (certificate : C2Certificate F input equivalence) : RawOutcome F input .c2
  | c3 {equivalence : EquivalenceState F input}
      {state : UncompressibleState F input equivalence}
      (certificate : C3Certificate F input state) : RawOutcome F input .c3
  | ct7 {equivalence : EquivalenceState F input}
      {state : UncompressibleState F input equivalence}
      (payload : CT7Payload F input state) : RawOutcome F input .ct7
  | ct12 {equivalence : EquivalenceState F input}
      {state : UncompressibleState F input equivalence}
      (payload : CT12Payload F input state) : RawOutcome F input .ct12
  | c5 {equivalence : EquivalenceState F input}
      {state : UncompressibleState F input equivalence}
      {persistent : PersistentState F input state}
      (certificate : C5Certificate F input persistent) : RawOutcome F input .c5
  | ct8 {equivalence : EquivalenceState F input}
      {state : UncompressibleState F input equivalence}
      {persistent : PersistentState F input state}
      (payload : CT8Payload F input persistent) : RawOutcome F input .ct8

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
      let equivalence := Nodes.Equivalence.run plan.equivalence scopeState
      match Nodes.Compression.run plan.compression equivalence with
      | .close certificate =>
          ⟨.c2,
            .cons .beginScope
              (.cons (.scopeReady scopeState)
                (.cons (.equivalenceCertified equivalence)
                  (.cons (.compressionClose certificate) (.nil .c2Terminal)))),
            .c2 certificate⟩
      | .residual state =>
          match Nodes.Defect.run plan.defect state with
          | .close certificate =>
              ⟨.c3,
                .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.equivalenceCertified equivalence)
                      (.cons (.compressionResidual state)
                        (.cons (.defectClose certificate) (.nil .c3Terminal))))),
                .c3 certificate⟩
          | .toCT7 payload =>
              ⟨.ct7,
                .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.equivalenceCertified equivalence)
                      (.cons (.compressionResidual state)
                        (.cons (.defectToCT7 payload) (.nil .ct7Terminal))))),
                .ct7 payload⟩
          | .toCT12 payload =>
              ⟨.ct12,
                .cons .beginScope
                  (.cons (.scopeReady scopeState)
                    (.cons (.equivalenceCertified equivalence)
                      (.cons (.compressionResidual state)
                        (.cons (.defectToCT12 payload) (.nil .ct12Terminal))))),
                .ct12 payload⟩
          | .persistent persistent =>
              match Nodes.Table.run plan.table persistent with
              | .close certificate =>
                  ⟨.c5,
                    .cons .beginScope
                      (.cons (.scopeReady scopeState)
                        (.cons (.equivalenceCertified equivalence)
                          (.cons (.compressionResidual state)
                            (.cons (.defectPersistent persistent)
                              (.cons (.tableClose certificate) (.nil .c5Terminal)))))),
                    .c5 certificate⟩
              | .toCT8 payload =>
                  ⟨.ct8,
                    .cons .beginScope
                      (.cons (.scopeReady scopeState)
                        (.cons (.equivalenceCertified equivalence)
                          (.cons (.compressionResidual state)
                            (.cons (.defectPersistent persistent)
                              (.cons (.tableToCT8 payload) (.nil .ct8Terminal)))))),
                    .ct8 payload⟩

inductive Outcome (F : Framework) (input : Input F) (port : Port F input) :
    Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : Outcome F input port .scope
  | c2 {equivalence : EquivalenceState F input}
      (certificate : C2Certificate F input equivalence) : Outcome F input port .c2
  | c3 {equivalence : EquivalenceState F input}
      {state : UncompressibleState F input equivalence}
      (certificate : C3Certificate F input state) : Outcome F input port .c3
  | ct7 {equivalence : EquivalenceState F input}
      {state : UncompressibleState F input equivalence}
      (payload : CT7Payload F input state)
      (accepted : port.accepts (.ct7 payload)) : Outcome F input port .ct7
  | ct12 {equivalence : EquivalenceState F input}
      {state : UncompressibleState F input equivalence}
      (payload : CT12Payload F input state)
      (accepted : port.accepts (.ct12 payload)) : Outcome F input port .ct12
  | c5 {equivalence : EquivalenceState F input}
      {state : UncompressibleState F input equivalence}
      {persistent : PersistentState F input state}
      (certificate : C5Certificate F input persistent) : Outcome F input port .c5
  | ct8 {equivalence : EquivalenceState F input}
      {state : UncompressibleState F input equivalence}
      {persistent : PersistentState F input state}
      (payload : CT8Payload F input persistent)
      (accepted : port.accepts (.ct8 payload)) : Outcome F input port .ct8

def OutcomeClaim {F : Framework} {input : Input F} {port : Port F input}
    {terminal : Graph.Terminal} : Outcome F input port terminal → Prop
  | .scope _ => ¬ TypeIndexFiniteAt F input
  | .c2 _ => F.C2Claim input.G input.branch
  | .c3 _ => F.C3Claim input.G input.branch
  | .ct7 payload _ => port.accepts (.ct7 payload)
  | .ct12 payload _ => port.accepts (.ct12 payload)
  | .c5 _ => F.C5Claim input.G input.branch
  | .ct8 payload _ => port.accepts (.ct8 payload)

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
  | ⟨_, path, .c2 certificate⟩ => ⟨.c2, path, .c2 certificate⟩
  | ⟨_, path, .c3 certificate⟩ => ⟨.c3, path, .c3 certificate⟩
  | ⟨_, path, .ct7 payload⟩ =>
      ⟨.ct7, path, .ct7 payload (handoff.accept (.ct7 payload))⟩
  | ⟨_, path, .ct12 payload⟩ =>
      ⟨.ct12, path, .ct12 payload (handoff.accept (.ct12 payload))⟩
  | ⟨_, path, .c5 certificate⟩ => ⟨.c5, path, .c5 certificate⟩
  | ⟨_, path, .ct8 payload⟩ =>
      ⟨.ct8, path, .ct8 payload (handoff.accept (.ct8 payload))⟩

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

end StructuralExhaustion.CT3
