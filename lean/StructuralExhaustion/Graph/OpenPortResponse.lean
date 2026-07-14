import StructuralExhaustion.Graph.AdjacencyResponse
import StructuralExhaustion.Graph.SurplusPortActivity
import StructuralExhaustion.Routes.CT9ToCT7

namespace StructuralExhaustion.Graph.OpenPortResponse

open StructuralExhaustion

universe u

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

def routedInput
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (source : SourceResidual base object baseline deletionCritical) :
    CT7.Input (AdjacencyResponse.spec base)
      (AdjacencyResponse.context base object baseline) :=
  Routes.CT9ToCT7.buildInput (AdjacencyResponse.capability base)
    (adapter object deletionCritical)
    (capacityOne base object deletionCritical) source

def run
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (source : SourceResidual base object baseline deletionCritical) :=
  CT7.run (AdjacencyResponse.spec base) (AdjacencyResponse.capability base)
    (AdjacencyResponse.context base object baseline)
    (routedInput base object baseline deletionCritical source)

theorem route_id
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (source : SourceResidual base object baseline deletionCritical) :
    ((Routes.CT9ToCT7.rule (AdjacencyResponse.capability base)
      (adapter object deletionCritical)
      (capacityOne base object deletionCritical)).generate source ()).routeId =
        "CT9.residual.overload->CT7" :=
  Routes.CT9ToCT7.generated_route_id _ _ _ source

theorem context_preserved
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (source : SourceResidual base object baseline deletionCritical) :
    Routes.CT9ToCT7.targetContext source =
      AdjacencyResponse.context base object baseline :=
  rfl

structure RoutedStage
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (source : SourceResidual base object baseline deletionCritical) : Prop where
  routeId :
    ((Routes.CT9ToCT7.rule (AdjacencyResponse.capability base)
      (adapter object deletionCritical)
      (capacityOne base object deletionCritical)).generate source ()).routeId =
        "CT9.residual.overload->CT7"
  verified : (run base object baseline deletionCritical source).outcome.Valid
  traceValid : CT7.Graph.ValidTrace
    (AdjacencyResponse.spec base) (AdjacencyResponse.capability base)
    (AdjacencyResponse.context base object baseline)
    (routedInput base object baseline deletionCritical source)
    (run base object baseline deletionCritical source).trace
  responseState :
    (∃ vertex : V,
      (AdjacencyResponse.spec base).response
          (AdjacencyResponse.context base object baseline)
          (routedInput base object baseline deletionCritical source).left vertex ≠
        (AdjacencyResponse.spec base).response
          (AdjacencyResponse.context base object baseline)
          (routedInput base object baseline deletionCritical source).right vertex) ∨
    (∀ vertex : V,
      (AdjacencyResponse.spec base).response
          (AdjacencyResponse.context base object baseline)
          (routedInput base object baseline deletionCritical source).left vertex =
        (AdjacencyResponse.spec base).response
          (AdjacencyResponse.context base object baseline)
          (routedInput base object baseline deletionCritical source).right vertex)
  linear : AdjacencyResponse.checks object ≤
    2 * object.input.vertices.card + 1

def routedStage
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (source : SourceResidual base object baseline deletionCritical) :
    RoutedStage base object baseline deletionCritical source where
  routeId := route_id base object baseline deletionCritical source
  verified := CT7.run_verified _ _ _ _
  traceValid := CT7.run_trace_valid _ _ _ _
  responseState := AdjacencyResponse.stateSpace base object baseline
    (routedInput base object baseline deletionCritical source).left
    (routedInput base object baseline deletionCritical source).right
  linear := AdjacencyResponse.checks_linear object

/-- Exact state-space stratification: the bounded CT9 branch remains intact;
only the overload branch is routed into CT7. -/
theorem stateSpace
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    (∀ center,
      CT9.fibreCount
        (SurplusPortActivity.openPairCapability
          base object deletionCritical)
        (SurplusPortActivity.openPairInput
          base object baseline deletionCritical) center ≤ 1) ∨
      (∃ source : SourceResidual base object baseline deletionCritical,
        RoutedStage base object baseline deletionCritical source) := by
  generalize resultEquation :
    SurplusPortActivity.openPairResult
      base object baseline deletionCritical = result
  cases result with
  | mk terminal path outcome =>
      cases outcome with
      | bounded certificate => exact Or.inl certificate.bounded
      | overloaded residual =>
          exact Or.inr ⟨residual,
            routedStage base object baseline deletionCritical residual⟩

end StructuralExhaustion.Graph.OpenPortResponse
