import StructuralExhaustion.Graph.AdjacencyResponse
import StructuralExhaustion.Graph.SurplusPortActivity
import StructuralExhaustion.Routes.CT9ToCT7

namespace StructuralExhaustion.Graph.OpenPortResponse

open StructuralExhaustion

universe u uLedger

/-!
# Routed response comparison for overloaded open-port fibres

This module is the reusable graph interpretation of the CT9-to-CT7 route.
An overloaded centre fibre supplies two exact open surplus slots; the route
maps them to their canonical port endpoints, and CT7 compares those endpoints
against every declared vertex adjacency context.
-/

def adapter (object : FiniteObject V)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    Routes.CT9ToCT7.ObjectAdapter
      (SurplusPortActivity.OpenPortSlot object deletionCritical) V where
  object := fun slot => SurplusPortActivity.portEndpoint object slot.1

theorem capacityOne
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    ∀ center,
      (SurplusPortActivity.openPairCapability
        base object deletionCritical).capacity center = 1 :=
  fun _center => rfl

abbrev SourceResidual
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :=
  CT9.OverloadResidual
    (SurplusPortActivity.openPairCapability base object deletionCritical)
    (SurplusPortActivity.openPairInput
      base object baseline deletionCritical)

abbrev transition
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :=
  Routes.CT9ToCT7.transition
    (sourceCapability := SurplusPortActivity.openPairCapability
      base object deletionCritical)
    (sourceInput := SurplusPortActivity.openPairInput
      base object baseline deletionCritical)
    (AdjacencyResponse.capability base) (adapter object deletionCritical)
    (capacityOne base object deletionCritical)

def executionStage
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    {Ledger : Sort uLedger}
    (sourceLedger : Core.Routing.ResidualStage .ct9 Ledger)
    (source : SourceResidual base object baseline deletionCritical) :=
  Routes.CT9ToCT7.advance (AdjacencyResponse.capability base)
    (adapter object deletionCritical) (capacityOne base object deletionCritical)
    (fun _ledger => source) sourceLedger

abbrev ExecutionLedger
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    {Ledger : Sort uLedger}
    (sourceLedger : Core.Routing.ResidualStage .ct9 Ledger)
    (source : SourceResidual base object baseline deletionCritical) :=
  ((transition base object baseline deletionCritical).onLedger
    (fun _ledger => source)).EnabledStage sourceLedger

/-- Complete CT7 ledger, including the exact CT9 overload predecessor. -/
def ledgerStage
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    {Ledger : Sort uLedger}
    (sourceLedger : Core.Routing.ResidualStage .ct9 Ledger)
    (source : SourceResidual base object baseline deletionCritical) :=
  (executionStage base object baseline deletionCritical sourceLedger source
    ).ledgerStage

def routedInput
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    {Ledger : Sort uLedger}
    (sourceLedger : Core.Routing.ResidualStage .ct9 Ledger)
    (source : SourceResidual base object baseline deletionCritical) :
    CT7.Input (AdjacencyResponse.spec base)
      (AdjacencyResponse.context base object baseline) :=
  let transition := transition base object baseline deletionCritical
  let accumulated := transition.onLedger (fun _ledger => source)
  accumulated.trigger sourceLedger ()

def run
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    {Ledger : Sort uLedger}
    (sourceLedger : Core.Routing.ResidualStage .ct9 Ledger)
    (source : SourceResidual base object baseline deletionCritical) :=
  (executionStage base object baseline deletionCritical sourceLedger source
    ).targetResult

theorem transition_profile_id
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    (transition base object baseline deletionCritical).profileId =
      "CT9.residual.overload->CT7" :=
  Routes.CT9ToCT7.transition_profile_id _ _ _

theorem context_preserved
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    {Ledger : Sort uLedger}
    (sourceLedger : Core.Routing.ResidualStage .ct9 Ledger)
    (source : SourceResidual base object baseline deletionCritical) :
    ((transition base object baseline deletionCritical).onLedger
      (fun _ledger => source)).targetContext sourceLedger =
      AdjacencyResponse.context base object baseline :=
  rfl

structure RoutedStage
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    {Ledger : Sort uLedger}
    (sourceLedger : Core.Routing.ResidualStage .ct9 Ledger)
    (source : SourceResidual base object baseline deletionCritical) : Prop where
  transitionProfileId :
    (transition base object baseline deletionCritical).profileId =
      "CT9.residual.overload->CT7"
  verified :
    (run base object baseline deletionCritical sourceLedger source).outcome.Valid
  traceValid : CT7.Graph.ValidTrace
    (AdjacencyResponse.spec base) (AdjacencyResponse.capability base)
    (AdjacencyResponse.context base object baseline)
    (routedInput base object baseline deletionCritical sourceLedger source)
    (run base object baseline deletionCritical sourceLedger source).trace
  responseState :
    (∃ vertex : V,
      (AdjacencyResponse.spec base).response
          (AdjacencyResponse.context base object baseline)
          (routedInput base object baseline deletionCritical
            sourceLedger source).left vertex ≠
        (AdjacencyResponse.spec base).response
          (AdjacencyResponse.context base object baseline)
          (routedInput base object baseline deletionCritical
            sourceLedger source).right vertex) ∨
    (∀ vertex : V,
      (AdjacencyResponse.spec base).response
          (AdjacencyResponse.context base object baseline)
          (routedInput base object baseline deletionCritical
            sourceLedger source).left vertex =
        (AdjacencyResponse.spec base).response
          (AdjacencyResponse.context base object baseline)
          (routedInput base object baseline deletionCritical
            sourceLedger source).right vertex)
  linear : AdjacencyResponse.checks object ≤
    2 * object.input.vertices.card + 1

def routedStage
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    {Ledger : Sort uLedger}
    (sourceLedger : Core.Routing.ResidualStage .ct9 Ledger)
    (source : SourceResidual base object baseline deletionCritical) :
    RoutedStage base object baseline deletionCritical sourceLedger source where
  transitionProfileId :=
    transition_profile_id base object baseline deletionCritical
  verified := CT7.run_verified _ _ _ _
  traceValid := CT7.run_trace_valid _ _ _ _
  responseState := AdjacencyResponse.stateSpace base object baseline
    (routedInput base object baseline deletionCritical sourceLedger source).left
    (routedInput base object baseline deletionCritical sourceLedger source).right
  linear := AdjacencyResponse.checks_linear object

def RoutedLedger
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    {Ledger : Sort uLedger}
    (sourceLedger : Core.Routing.ResidualStage .ct9 Ledger)
    (source : SourceResidual base object baseline deletionCritical) :=
  Core.Routing.LedgerExtension
    (ExecutionLedger base object baseline deletionCritical sourceLedger source)
    (fun _execution =>
      RoutedStage base object baseline deletionCritical sourceLedger source)

def routedLedgerStage
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    {Ledger : Sort uLedger}
    (sourceLedger : Core.Routing.ResidualStage .ct9 Ledger)
    (source : SourceResidual base object baseline deletionCritical) :
    Core.Routing.ResidualStage .ct7
      (RoutedLedger base object baseline deletionCritical sourceLedger source) :=
  (ledgerStage base object baseline deletionCritical sourceLedger source).extend
    (routedStage base object baseline deletionCritical sourceLedger source)

inductive StateSpace
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    {Ledger : Sort uLedger}
    (sourceLedger : Core.Routing.ResidualStage .ct9 Ledger) where
  | bounded (certificate : ∀ center,
      CT9.fibreCount
        (SurplusPortActivity.openPairCapability
          base object deletionCritical)
        (SurplusPortActivity.openPairInput
          base object baseline deletionCritical) center ≤ 1)
  | routed (source : SourceResidual base object baseline deletionCritical)

/-- Exact state-space stratification: the bounded CT9 branch remains intact;
only the overload branch is routed into CT7. -/
def stateSpace
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    {Ledger : Sort uLedger}
    (sourceLedger : Core.Routing.ResidualStage .ct9 Ledger) :
    StateSpace base object baseline deletionCritical sourceLedger := by
  generalize resultEquation :
    SurplusPortActivity.openPairResult
      base object baseline deletionCritical = result
  cases result with
  | mk terminal path outcome =>
      cases outcome with
      | bounded certificate => exact .bounded certificate.bounded
      | overloaded residual =>
          exact .routed residual

end StructuralExhaustion.Graph.OpenPortResponse
