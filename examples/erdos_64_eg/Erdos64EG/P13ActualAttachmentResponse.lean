import Erdos64EG.CT10P13MultiScaleCurvature
import StructuralExhaustion.Core.LocalBooleanRealization

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
# Actual attachment responses of one selected P13 window

This file records the strongest Boolean response system that can currently be
constructed from the selected graph and one literal CT12 window without
inventing completion states.  Its states are actual ambient vertices outside
the window, its thirteen coordinates are the path positions, and its response
bits are literal graph adjacencies.

This is intentionally not the manuscript's claimed 91-barrier, multi-scale
system.  The node-[21] prefix contains the finite compatibility tables but no
family of graph completions at separated dyadic scales and no theorem saying
that those completions realize arbitrary products of barrier responses.  In
particular, this file does not turn the 91 injective barrier indices into a
Boolean cube.
-/

/-- An actual ambient vertex outside a fixed selected window. -/
abbrev P13ActualAttachmentState
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : InducedP13Window ctx) :=
  {vertex : ctx.G.Vertex //
    ∀ position : Fin 13, vertex ≠ window position}

@[implicit_reducible]
noncomputable def p13ActualAttachmentStates
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : InducedP13Window ctx) :
    FinEnum (P13ActualAttachmentState ctx window) := by
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  infer_instance

/-- The literal, graph-owned response system at one selected window. -/
noncomputable def p13ActualAttachmentSystem
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : InducedP13Window ctx) :
    Core.LocalBooleanRealization.System where
  Coordinate := Fin 13
  State := P13ActualAttachmentState ctx window
  coordinates := inferInstance
  states := p13ActualAttachmentStates ctx window
  value := fun state position =>
    @decide (ctx.G.object.graph.Adj state.1 (window position))
      (ctx.G.object.input.decideAdj state.1 (window position))

@[simp] theorem p13ActualAttachmentSystem_value_eq_true_iff
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : InducedP13Window ctx)
    (state : P13ActualAttachmentState ctx window) (position : Fin 13) :
    (p13ActualAttachmentSystem ctx window).value state position = true ↔
      ctx.G.object.graph.Adj state.1 (window position) := by
  simp [p13ActualAttachmentSystem, decide_eq_true_eq]

/-- The response vector of an actual state is exactly its graph-theoretic
attachment label, not a caller-authored Boolean assignment. -/
theorem p13ActualAttachmentSystem_value_iff_labelMembership
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : InducedP13Window ctx)
    (state : P13ActualAttachmentState ctx window) (position : Fin 13) :
    (p13ActualAttachmentSystem ctx window).value state position = true ↔
      position ∈ packedStaticInput.inducedPathAttachmentLabel
        13 ctx window state.1 := by
  rw [p13ActualAttachmentSystem_value_eq_true_iff]
  letI : DecidableRel ctx.G.object.graph.Adj :=
    ctx.G.object.input.decideAdj
  exact (Graph.InducedPathAttachment.mem_attachmentLabel_iff
    window state.1 position).symm

/-- The grounded system has exactly the thirteen path-position coordinates.
The 91 barrier relations are therefore not already present as response
coordinates in the graph data. -/
theorem p13ActualAttachmentSystem_coordinateCard
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : InducedP13Window ctx) :
    (p13ActualAttachmentSystem ctx window).coordinates.card = 13 := by
  change (inferInstance : FinEnum (Fin 13)).card = 13
  native_decide

/-- Complete realization of all thirteen raw attachment bits is impossible in
the selected target-avoiding graph: the all-true assignment would attach one
outside vertex at path positions `0` and `2`, closing a four-cycle.  This is a
pre-density fact and uses no 91-coordinate completion-state premise. -/
theorem p13RawAttachmentSystem_hot_impossible
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : InducedP13Window ctx) :
    ¬(p13ActualAttachmentSystem ctx window).HotCertificate := by
  intro hot
  let assignment :
      (p13ActualAttachmentSystem ctx window).Assignment := fun _ ↦ true
  obtain ⟨state, realized⟩ := hot.realizes assignment
  have atZero : (p13ActualAttachmentSystem ctx window).value state
      ⟨0, by decide⟩ = true := by
    rw [realized]
  have atTwo : (p13ActualAttachmentSystem ctx window).value state
      ⟨2, by decide⟩ = true := by
    rw [realized]
  have adjacentZero : ctx.G.object.graph.Adj state.1 (window ⟨0, by decide⟩) :=
    (p13ActualAttachmentSystem_value_eq_true_iff ctx window state
      ⟨0, by decide⟩).1 atZero
  have adjacentTwo : ctx.G.object.graph.Adj state.1 (window ⟨2, by decide⟩) :=
    (p13ActualAttachmentSystem_value_eq_true_iff ctx window state
      ⟨2, by decide⟩).1 atTwo
  let cycle := Graph.InducedPathAttachment.cycleOfAttachments
    PowerOfTwoLength window state.1 state.2
      ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide)
      adjacentZero adjacentTwo (by
        change PowerOfTwoLength 4
        exact ⟨2, by decide, by norm_num⟩)
  exact ctx.avoids ⟨cycle⟩

end Erdos64EG.Internal
