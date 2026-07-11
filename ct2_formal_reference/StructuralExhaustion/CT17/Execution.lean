import StructuralExhaustion.CT17.Nodes
import StructuralExhaustion.CT17.Graph
namespace StructuralExhaustion.CT17
structure CorePlan (F : Framework) (input : Input F) where
  scope : Nodes.Scope.Plan F input
  compatibility : Nodes.Compatibility.Plan F input
  separation : Nodes.Separation.Plan F input
  block : Nodes.Block.Plan F input
  scale : Nodes.Scale.Plan F input
  survivors : Nodes.Survivors.Plan F input
  arithmetic : Nodes.Arithmetic.Plan F input
inductive RawOutcome (F : Framework) (input : Input F) : Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : RawOutcome F input .scope
  | ct3 {scope : ScopedState F input} {state : IncompatibleState F input scope}
      (payload : CT3Payload F input state) : RawOutcome F input .ct3
  | ct10 {scope : ScopedState F input} {state : IncompatibleState F input scope}
      (payload : CT10Payload F input state) : RawOutcome F input .ct10
  | c5 {scope : ScopedState F input} {compatible : CompatibleState F input scope}
      {block : BlockState F input compatible} {finite : FiniteState F input block}
      (certificate : C5Certificate F input finite) : RawOutcome F input .c5
  | ct8 {scope : ScopedState F input} {compatible : CompatibleState F input scope}
      {block : BlockState F input compatible} {finite : FiniteState F input block}
      (payload : CT8Payload F input finite) : RawOutcome F input .ct8
  | c1 {scope : ScopedState F input} {compatible : CompatibleState F input scope}
      {block : BlockState F input compatible} {repeated : RepeatedState F input block}
      (certificate : C1Certificate F input repeated) : RawOutcome F input .c1
  | ct14 {scope : ScopedState F input} {compatible : CompatibleState F input scope}
      {block : BlockState F input compatible} {repeated : RepeatedState F input block}
      (payload : CT14Payload F input repeated) : RawOutcome F input .ct14
structure CoreResult (F : Framework) (input : Input F) where
  terminal : Graph.Terminal
  path : Graph.Path F input .entry terminal.nodeId
  outcome : RawOutcome F input terminal
def runCore (F : Framework) (input : Input F) (plan : CorePlan F input) : CoreResult F input :=
  let entry := Nodes.Entry.run input
  match Nodes.Scope.run entry plan.scope with
  | .exit candidate =>
      ⟨.scope, .cons .beginScope (.cons (.scopeExit candidate) (.nil .scopeTerminal)), .scope candidate⟩
  | .ready scope =>
      match Nodes.Compatibility.run plan.compatibility scope with
      | .incompatible state =>
          match Nodes.Separation.run plan.separation state with
          | .toCT3 payload =>
              ⟨.ct3, .cons .beginScope (.cons (.scopeReady scope)
                (.cons (.compatibilityNo state)
                  (.cons (.separationToCT3 payload) (.nil .ct3Terminal)))), .ct3 payload⟩
          | .toCT10 payload =>
              ⟨.ct10, .cons .beginScope (.cons (.scopeReady scope)
                (.cons (.compatibilityNo state)
                  (.cons (.separationToCT10 payload) (.nil .ct10Terminal)))), .ct10 payload⟩
      | .compatible compatible =>
          let block := Nodes.Block.run plan.block compatible
          match Nodes.Scale.run plan.scale block with
          | .finite finite =>
              match Nodes.Survivors.run plan.survivors finite with
              | .exhausted certificate =>
                  ⟨.c5, .cons .beginScope (.cons (.scopeReady scope)
                    (.cons (.compatibilityYes compatible) (.cons (.blockCertified block)
                      (.cons (.scaleFinite finite)
                        (.cons (.survivorsExhausted certificate) (.nil .c5Terminal)))))),
                    .c5 certificate⟩
              | .persist payload =>
                  ⟨.ct8, .cons .beginScope (.cons (.scopeReady scope)
                    (.cons (.compatibilityYes compatible) (.cons (.blockCertified block)
                      (.cons (.scaleFinite finite)
                        (.cons (.survivorsToCT8 payload) (.nil .ct8Terminal)))))), .ct8 payload⟩
          | .repeated repeated =>
              match Nodes.Arithmetic.run plan.arithmetic repeated with
              | .close certificate =>
                  ⟨.c1, .cons .beginScope (.cons (.scopeReady scope)
                    (.cons (.compatibilityYes compatible) (.cons (.blockCertified block)
                      (.cons (.scaleRepeated repeated)
                        (.cons (.arithmeticClose certificate) (.nil .c1Terminal)))))),
                    .c1 certificate⟩
              | .residual payload =>
                  ⟨.ct14, .cons .beginScope (.cons (.scopeReady scope)
                    (.cons (.compatibilityYes compatible) (.cons (.blockCertified block)
                      (.cons (.scaleRepeated repeated)
                        (.cons (.arithmeticToCT14 payload) (.nil .ct14Terminal)))))),
                    .ct14 payload⟩
inductive Outcome (F : Framework) (input : Input F) (port : Port F input) :
    Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : Outcome F input port .scope
  | ct3 {scope : ScopedState F input} {state : IncompatibleState F input scope}
      (p : CT3Payload F input state) (h : port.accepts (.ct3 p)) : Outcome F input port .ct3
  | ct10 {scope : ScopedState F input} {state : IncompatibleState F input scope}
      (p : CT10Payload F input state) (h : port.accepts (.ct10 p)) : Outcome F input port .ct10
  | c5 {scope : ScopedState F input} {compatible : CompatibleState F input scope}
      {block : BlockState F input compatible} {finite : FiniteState F input block}
      (c : C5Certificate F input finite) : Outcome F input port .c5
  | ct8 {scope : ScopedState F input} {compatible : CompatibleState F input scope}
      {block : BlockState F input compatible} {finite : FiniteState F input block}
      (p : CT8Payload F input finite) (h : port.accepts (.ct8 p)) : Outcome F input port .ct8
  | c1 {scope : ScopedState F input} {compatible : CompatibleState F input scope}
      {block : BlockState F input compatible} {repeated : RepeatedState F input block}
      (c : C1Certificate F input repeated) : Outcome F input port .c1
  | ct14 {scope : ScopedState F input} {compatible : CompatibleState F input scope}
      {block : BlockState F input compatible} {repeated : RepeatedState F input block}
      (p : CT14Payload F input repeated) (h : port.accepts (.ct14 p)) : Outcome F input port .ct14
def OutcomeClaim {F : Framework} {input : Input F} {port : Port F input}
    {terminal : Graph.Terminal} : Outcome F input port terminal → Prop
  | .scope _ => ¬ ScopeReadyAt F input | .ct3 p _ => port.accepts (.ct3 p)
  | .ct10 p _ => port.accepts (.ct10 p) | .c5 _ => F.entry.C5Claim input.G input.branch
  | .ct8 p _ => port.accepts (.ct8 p) | .c1 _ => F.entry.C1Claim input.G input.branch
  | .ct14 p _ => port.accepts (.ct14 p)
structure ExecutionResult (F : Framework) (input : Input F) (port : Port F input) where
  terminal : Graph.Terminal
  path : Graph.Path F input .entry terminal.nodeId
  outcome : Outcome F input port terminal
namespace ExecutionResult
def trace {F : Framework} {input : Input F} {port : Port F input}
    (r : ExecutionResult F input port) : List Graph.NodeId := r.path.trace
end ExecutionResult
def certify (F : Framework) (input : Input F) (port : Port F input)
    (handoff : HandoffPlan F input port) (r : CoreResult F input) : ExecutionResult F input port :=
  match r with
  | ⟨_, path, .scope c⟩ => ⟨.scope, path, .scope c⟩
  | ⟨_, path, .ct3 p⟩ => ⟨.ct3, path, .ct3 p (handoff.accept (.ct3 p))⟩
  | ⟨_, path, .ct10 p⟩ => ⟨.ct10, path, .ct10 p (handoff.accept (.ct10 p))⟩
  | ⟨_, path, .c5 c⟩ => ⟨.c5, path, .c5 c⟩
  | ⟨_, path, .ct8 p⟩ => ⟨.ct8, path, .ct8 p (handoff.accept (.ct8 p))⟩
  | ⟨_, path, .c1 c⟩ => ⟨.c1, path, .c1 c⟩
  | ⟨_, path, .ct14 p⟩ => ⟨.ct14, path, .ct14 p (handoff.accept (.ct14 p))⟩
def runTraced (F : Framework) (input : Input F) (plan : CorePlan F input)
    (port : Port F input) (handoff : HandoffPlan F input port) : ExecutionResult F input port :=
  certify F input port handoff (runCore F input plan)
def SomeOutcome (F : Framework) (input : Input F) (port : Port F input) :=
  Σ terminal : Graph.Terminal, Outcome F input port terminal
def run (F : Framework) (input : Input F) (plan : CorePlan F input)
    (port : Port F input) (handoff : HandoffPlan F input port) : SomeOutcome F input port :=
  let r := runTraced F input plan port handoff; ⟨r.terminal, r.outcome⟩
end StructuralExhaustion.CT17
