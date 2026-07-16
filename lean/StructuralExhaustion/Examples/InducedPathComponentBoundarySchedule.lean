import StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule

namespace StructuralExhaustion.Examples.ComponentBoundarySchedule

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathColdSkeleton
open StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule

universe u

variable {V : Type u} {object : FiniteObject V}

/-!
A theorem-independent transfer of the component-boundary scheduler.  The
source supplies one literal ambient-cubic boundary stub and a graph theorem
that its edge is not a bridge.  The reusable graph layer constructs every
other object.
-/

structure Source (object : FiniteObject V) where
  anchor : BoundaryStub object
  notBridge : ¬object.graph.IsBridge
    (InducedPathColdCorridor.CubicStub.dart
      { token := anchor.token, cubic := anchor.cubic }).edge

namespace Source

noncomputable def input (source : Source object) :
    InducedPathComponentBoundarySchedule.Input object where
  anchor := source.anchor
  notBridge := source.notBridge

theorem produces_distinct_same_component (source : Source object) :
    (successor source.input ≠ source.anchor) ∧
      component (successor source.input) = component source.anchor :=
  ⟨successor_distinct source.input, successor_same_component source.input⟩

theorem exit_is_computed_scan (source : Source object) :
    source.input.exitCertificate =
      scanExit source.input.ambientReturn source.input.InAnchorComponent
        source.input.anchor_in_component
        source.input.window_vertex_not_in_component := rfl

theorem stored_schedule_complete_and_nontrivial (source : Source object) :
    (∀ stub, stub ∈ incidentStubs source.input ↔
      component stub = component source.anchor) ∧
      2 ≤ (incidentStubs source.input).length :=
  ⟨mem_incidentStubs_iff source.input,
    two_le_incidentStubs_length source.input⟩

theorem successor_is_true_cyclic_next (source : Source object) :
    successor source.input =
      @List.next _ (boundaryStubs object).decEq
        (incidentStubs source.input) source.anchor
        (anchor_mem_incidentStubs source.input) := rfl

theorem finite_slot_search_is_exact (source : Source object) :
    InducedPathColdLedger.AmbientCubic object
        source.input.windowPosition.1.1 ∧
      InducedPathWindowLedger.selectedWindow object
        source.input.windowPosition.1.1 source.input.windowPosition.1.2 =
          source.input.insideEndpoint :=
  source.input.windowPosition.2

theorem finite_slot_first_hit_provenance (source : Source object) :
    ∃ hit, source.input.slotScan = .found hit ∧
      source.input.windowPosition.1 = hit.value ∧
      ∀ candidate ∈ hit.before,
        ¬source.input.SlotPredicate candidate :=
  source.input.windowPosition_firstHit

theorem produces_shortest_component_path (source : Source object) :
    (componentPath source.input).IsPath ∧
      (componentPath source.input).length =
        (component source.anchor).toSimpleGraph.dist
          (twoStubComponent source.input).componentRoot
          (twoStubComponent source.input).componentTarget :=
  ⟨componentPath_isPath source.input,
    componentPath_shortest source.input⟩

theorem exact_local_work (source : Source object) :
    visibleChecks source.input =
      InducedPathWindowLedger.checks object +
        13 * InducedPathWindowLedger.packingNumber object +
        source.input.ambientReturn.length *
          (outsideObject object).input.vertices.card +
        (outsideBfsProfile source.input).budget
          (outsideObject object).input.vertices.card +
        (outsideObject object).input.vertices.card ^ 2 +
        (InducedPathWindowLedger.tokens object).card *
          (2 + 13 * InducedPathWindowLedger.packingNumber object +
            (outsideObject object).input.vertices.card) +
        (bfsProfile source.input).budget
          (componentObject source.input).input.vertices.card :=
  visibleChecks_eq source.input

theorem full_work_is_polynomial (source : Source object) :
    visibleChecks source.input ≤ 50 * localScale source.input ^ 3 :=
  visibleChecks_polynomial source.input

end Source

end StructuralExhaustion.Examples.ComponentBoundarySchedule
