import StructuralExhaustion.CT15.Nodes
import StructuralExhaustion.CT15.Graph
namespace StructuralExhaustion.CT15
structure CorePlan (F : Framework) (input : Input F) where
  scope : Nodes.Scope.Plan F input
  rank : Nodes.Rank.Plan F input
  rankDrop : Nodes.RankDrop.Plan F input
  dependenceRouting : Nodes.DependenceRouting.Plan F input
  ledger : Nodes.Ledger.Plan F input
  comparison : Nodes.Comparison.Plan F input
inductive RawOutcome (F : Framework) (input : Input F) : Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : RawOutcome F input .scope
  | ct3 {rank : RankState F input} {dependence : DependenceState F input rank}
      (payload : CT3Payload F input dependence) : RawOutcome F input .ct3
  | ct7 {rank : RankState F input} {dependence : DependenceState F input rank}
      (payload : CT7Payload F input dependence) : RawOutcome F input .ct7
  | ct16 {rank : RankState F input} {dependence : DependenceState F input rank}
      (payload : CT16Payload F input dependence) : RawOutcome F input .ct16
  | c4 {rank : RankState F input} {full : FullRankState F input rank}
      {ledger : LedgerState F input full} (certificate : C4Certificate F input ledger) :
      RawOutcome F input .c4
  | ct4 {rank : RankState F input} {full : FullRankState F input rank}
      {ledger : LedgerState F input full} (payload : CT4Payload F input ledger) :
      RawOutcome F input .ct4
structure CoreResult (F : Framework) (input : Input F) where
  terminal : Graph.Terminal
  path : Graph.Path F input .entry terminal.nodeId
  outcome : RawOutcome F input terminal
def runCore (F : Framework) (input : Input F) (plan : CorePlan F input) : CoreResult F input :=
  let entry := Nodes.Entry.run input
  match Nodes.Scope.run entry plan.scope with
  | .exit candidate =>
      ⟨.scope, .cons .beginScope (.cons (.scopeExit candidate) (.nil .scopeTerminal)),
        .scope candidate⟩
  | .ready scope =>
      let rank := Nodes.Rank.run plan.rank scope
      match Nodes.RankDrop.run plan.rankDrop rank with
      | .dependent dependence =>
          match Nodes.DependenceRouting.run plan.dependenceRouting dependence with
          | .toCT3 payload =>
              ⟨.ct3, .cons .beginScope (.cons (.scopeReady scope)
                (.cons (.rankCertified rank) (.cons (.rankDependent dependence)
                  (.cons (.dependenceToCT3 payload) (.nil .ct3Terminal))))), .ct3 payload⟩
          | .toCT7 payload =>
              ⟨.ct7, .cons .beginScope (.cons (.scopeReady scope)
                (.cons (.rankCertified rank) (.cons (.rankDependent dependence)
                  (.cons (.dependenceToCT7 payload) (.nil .ct7Terminal))))), .ct7 payload⟩
          | .toCT16 payload =>
              ⟨.ct16, .cons .beginScope (.cons (.scopeReady scope)
                (.cons (.rankCertified rank) (.cons (.rankDependent dependence)
                  (.cons (.dependenceToCT16 payload) (.nil .ct16Terminal))))), .ct16 payload⟩
      | .full full =>
          let ledger := Nodes.Ledger.run plan.ledger full
          match Nodes.Comparison.run plan.comparison ledger with
          | .close certificate =>
              ⟨.c4, .cons .beginScope (.cons (.scopeReady scope)
                (.cons (.rankCertified rank) (.cons (.rankFull full)
                  (.cons (.ledgerCertified ledger)
                    (.cons (.comparisonClose certificate) (.nil .c4Terminal)))))),
                .c4 certificate⟩
          | .toCT4 payload =>
              ⟨.ct4, .cons .beginScope (.cons (.scopeReady scope)
                (.cons (.rankCertified rank) (.cons (.rankFull full)
                  (.cons (.ledgerCertified ledger)
                    (.cons (.comparisonToCT4 payload) (.nil .ct4Terminal)))))),
                .ct4 payload⟩
inductive Outcome (F : Framework) (input : Input F) (port : Port F input) :
    Graph.Terminal → Type where
  | scope (candidate : ScopeCandidate F input) : Outcome F input port .scope
  | ct3 {rank : RankState F input} {dependence : DependenceState F input rank}
      (payload : CT3Payload F input dependence) (accepted : port.accepts (.ct3 payload)) :
      Outcome F input port .ct3
  | ct7 {rank : RankState F input} {dependence : DependenceState F input rank}
      (payload : CT7Payload F input dependence) (accepted : port.accepts (.ct7 payload)) :
      Outcome F input port .ct7
  | ct16 {rank : RankState F input} {dependence : DependenceState F input rank}
      (payload : CT16Payload F input dependence) (accepted : port.accepts (.ct16 payload)) :
      Outcome F input port .ct16
  | c4 {rank : RankState F input} {full : FullRankState F input rank}
      {ledger : LedgerState F input full} (certificate : C4Certificate F input ledger) :
      Outcome F input port .c4
  | ct4 {rank : RankState F input} {full : FullRankState F input rank}
      {ledger : LedgerState F input full} (payload : CT4Payload F input ledger)
      (accepted : port.accepts (.ct4 payload)) : Outcome F input port .ct4
def OutcomeClaim {F : Framework} {input : Input F} {port : Port F input}
    {terminal : Graph.Terminal} : Outcome F input port terminal → Prop
  | .scope _ => ¬ ScopeReadyAt F input
  | .ct3 p _ => port.accepts (.ct3 p) | .ct7 p _ => port.accepts (.ct7 p)
  | .ct16 p _ => port.accepts (.ct16 p) | .c4 _ => F.entry.C4Claim input.G input.branch
  | .ct4 p _ => port.accepts (.ct4 p)
structure ExecutionResult (F : Framework) (input : Input F) (port : Port F input) where
  terminal : Graph.Terminal
  path : Graph.Path F input .entry terminal.nodeId
  outcome : Outcome F input port terminal
namespace ExecutionResult
def trace {F : Framework} {input : Input F} {port : Port F input}
    (result : ExecutionResult F input port) : List Graph.NodeId := result.path.trace
end ExecutionResult
def certify (F : Framework) (input : Input F) (port : Port F input)
    (handoff : HandoffPlan F input port) (result : CoreResult F input) : ExecutionResult F input port :=
  match result with
  | ⟨_, path, .scope c⟩ => ⟨.scope, path, .scope c⟩
  | ⟨_, path, .ct3 p⟩ => ⟨.ct3, path, .ct3 p (handoff.accept (.ct3 p))⟩
  | ⟨_, path, .ct7 p⟩ => ⟨.ct7, path, .ct7 p (handoff.accept (.ct7 p))⟩
  | ⟨_, path, .ct16 p⟩ => ⟨.ct16, path, .ct16 p (handoff.accept (.ct16 p))⟩
  | ⟨_, path, .c4 c⟩ => ⟨.c4, path, .c4 c⟩
  | ⟨_, path, .ct4 p⟩ => ⟨.ct4, path, .ct4 p (handoff.accept (.ct4 p))⟩
def runTraced (F : Framework) (input : Input F) (plan : CorePlan F input)
    (port : Port F input) (handoff : HandoffPlan F input port) : ExecutionResult F input port :=
  certify F input port handoff (runCore F input plan)
def SomeOutcome (F : Framework) (input : Input F) (port : Port F input) :=
  Σ terminal : Graph.Terminal, Outcome F input port terminal
def run (F : Framework) (input : Input F) (plan : CorePlan F input)
    (port : Port F input) (handoff : HandoffPlan F input port) : SomeOutcome F input port :=
  let r := runTraced F input plan port handoff; ⟨r.terminal, r.outcome⟩
end StructuralExhaustion.CT15
