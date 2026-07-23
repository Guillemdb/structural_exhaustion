import Hypostructure.Core.Strategy
import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Query
import Hypostructure.PDE.Model

/-!
# PDE adapters for reusable strategies

The PDE specialization supplies only represented states, observable schedules,
and analytic predicates.  Core owns dichotomy composition, ledger extension,
and terminal routing.  In particular, these interfaces never enumerate the
continuum: finite schedules are queries on the active residual.
-/

namespace Hypostructure.PDE.Strategy

universe uPrevious uModel uItem uCoordinate uValue

open Hypostructure

structure ObservableScan (Previous : Type uPrevious) (M : PDE.LocalModel.{uModel}) where
  state : Core.Residual.Query Previous
    (fun _previous => M.problem.Ambient)
  Item : Previous -> Type uItem
  schedule : Core.Residual.Query Previous
    (fun previous => Core.Finite.Enumeration (Item previous))
  observe : (previous : Previous) -> M.problem.Ambient ->
    Item previous -> Bool

structure ResponseProfile (Previous : Type uPrevious) where
  Coordinate : Previous -> Type uCoordinate
  schedule : Core.Residual.Query Previous
    (fun previous => Core.Finite.Enumeration (Coordinate previous))
  observe : (previous : Previous) -> Coordinate previous -> Bool

structure ChargeProfile (Previous : Type uPrevious) where
  Item : Previous -> Type uItem
  schedule : Core.Residual.Query Previous
    (fun previous => Core.Finite.Enumeration (Item previous))
  charge : (previous : Previous) -> Item previous -> Int

/-! A residual-owned scale/window schedule for concentration and regularity
strategies.  The type is abstract: an application may use dyadic windows,
profiles, channels, or any other finite represented index. -/
structure ScaleWindowProfile (Previous : Type uPrevious) where
  Scale : Previous -> Type uValue
  schedule : Core.Residual.Query Previous
    (fun previous => Core.Finite.Enumeration (Scale previous))
  active : (previous : Previous) -> Scale previous -> Prop
  activeDecidable : (previous : Previous) -> (scale : Scale previous) ->
    Decidable (active previous scale)

abbrev Dichotomy (Previous : Type uPrevious) :=
  Core.Strategy.Dichotomy Previous

abbrev ClosedDichotomy (Previous : Type uPrevious) :=
  Core.Strategy.ClosedDichotomy Previous

abbrev StrategyContract (Previous : Type uPrevious) :=
  Core.Strategy.Contract Previous

abbrev ProblemInput (P : Core.Problem) :=
  Core.Strategy.ProblemInput P

abbrev InitStage (P : Core.Problem) :=
  Core.Strategy.InitStage P

abbrev InitStrategy (P : Core.Problem) :=
  Core.Strategy.InitStrategy P

abbrev StrategyProjection (Previous : Type uPrevious) :=
  Core.Strategy.StrategyProjection Previous

abbrev ClosedPipeline (Previous : Type uPrevious) :=
  Core.Strategy.ClosedPipeline Previous

abbrev Pipeline (Previous : Type uPrevious) :=
  Core.Strategy.Pipeline Previous

def chainPipelines {Previous : Type uPrevious}
    (first : Pipeline Previous)
    (next : (stage : Core.Residual.Ledger.Extension Previous
      (fun stage => Sigma (first.execution.Payload stage))) ->
      Pipeline (Core.Residual.Ledger.Extension Previous
        (fun stage => Sigma (first.execution.Payload stage))))
    (previous : Previous) :=
  Core.Strategy.pipelineChain first next previous

/-! These are aliases, not PDE-specific strategy engines.  Their schedules,
observations, and semantic predicates remain PDE inputs while Core retains
the reusable finite-routing contracts. -/

abbrev OrderedWitnessScan (Previous : Type uPrevious) :=
  Core.Strategy.OrderedWitnessScan Previous

abbrev ResponseClassifier (Previous : Type uPrevious) :=
  Core.Strategy.ResponseClassifier Previous

abbrev CapacityLedger (Previous : Type uPrevious) :=
  Core.Strategy.CapacityLedger Previous

abbrev SupportLocalization (Previous : Type uPrevious) :=
  Core.Strategy.SupportLocalization Previous

abbrev TargetAvoidingContinuation (Previous : Type uPrevious) :=
  Core.Strategy.TargetAvoidingContinuation Previous

abbrev RankBudgetSplit (Previous : Type uPrevious) :=
  Core.Strategy.RankBudgetSplit Previous

abbrev ClosedCodeExhaustion (Previous : Type uPrevious) :=
  Core.Strategy.ClosedCodeExhaustion Previous

abbrev CTAdapter (Previous : Type uPrevious) :=
  Core.Strategy.CTAdapter Previous

abbrev BranchPipelines (Previous : Type uPrevious) :=
  Core.Strategy.BranchPipelines Previous

abbrev WorkEvidence (Previous : Type uPrevious) :=
  Core.Strategy.WorkEvidence Previous

abbrev WorkProfile (Previous : Type uPrevious) :=
  Core.Strategy.WorkProfile Previous

abbrev TerminalCertificate (Previous : Type uPrevious) :=
  Core.Strategy.TerminalCertificate Previous

abbrev TerminalKind :=
  Core.Strategy.TerminalKind

abbrev RoutedClosure (Previous : Type uPrevious) :=
  Core.Strategy.RoutedClosure Previous

abbrev DomainStrategy (Previous : Type uPrevious) :=
  Core.Strategy.DomainStrategy Previous

/-! ## PDE-facing execution of a Core-owned domain strategy

The returned stage is the literal Core ledger extension.  PDE rows provide
the contract and its residual-owned work profile; this helper only exposes
the common execution shape under the PDE namespace.
-/

def runDomainStrategy {Previous : Type uPrevious}
    (strategy : DomainStrategy Previous) (previous : Previous) :=
  Core.Strategy.run strategy.execution previous

def domainWork {Previous : Type uPrevious}
    (strategy : DomainStrategy Previous) (previous : Previous) : Nat :=
  strategy.work.work previous

abbrev BinaryTerminal :=
  Core.Strategy.BinaryTerminal

end Hypostructure.PDE.Strategy
