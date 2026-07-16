import Erdos64EG.P13ActualAttachmentResponse

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

set_option maxHeartbeats 0

/-!
# Node [158]: parallel actual-attachment cold fork

This branch is separate from the still-open node-[21]-to-[22] 91-coordinate
realization interface.  The literal thirteen-coordinate attachment classifier
cannot be hot in a target-avoiding graph.  Its canonical cold residual is
therefore retained with the same selected window as the exact trigger for the
subsequent graph-owned surplus/corridor classifier.
-/

abbrev P13ActualSelectedWindow
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  {window : InducedP13Window ctx // window ∈ p13Windows ctx}

structure P13ActualAttachmentColdFork
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (window : P13ActualSelectedWindow ctx) where
  predecessor : VerifiedP13MultiScaleCurvaturePrefix ctx
  selectedWindow : P13ActualSelectedWindow ctx
  sameWindow : selectedWindow = window
  residual : (p13ActualAttachmentSystem ctx window.1).ColdResidual
  classifierExact : (p13ActualAttachmentSystem ctx window.1).classify =
    .cold residual

/-- Execute the literal finite classifier.  The hot constructor is eliminated
by the four-cycle theorem, not by a classical decision on an unconstructed
91-coordinate proposition. -/
noncomputable def p13ActualAttachmentColdFork
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (window : P13ActualSelectedWindow ctx) :
    P13ActualAttachmentColdFork ctx previous window := by
  cases equation : (p13ActualAttachmentSystem ctx window.1).classify with
  | hot certificate =>
      exact (p13RawAttachmentSystem_hot_impossible ctx window.1 certificate).elim
  | cold residual =>
      exact {
        predecessor := previous
        selectedWindow := window
        sameWindow := rfl
        residual := residual
        classifierExact := equation }

theorem p13ActualAttachment_classify_cold
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (window : P13ActualSelectedWindow ctx) :
    ∃ residual, (p13ActualAttachmentSystem ctx window.1).classify =
      .cold residual := by
  let fork := p13ActualAttachmentColdFork ctx previous window
  exact ⟨fork.residual, fork.classifierExact⟩

theorem p13ActualAttachmentColdFork_missing
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {window : P13ActualSelectedWindow ctx}
    (fork : P13ActualAttachmentColdFork ctx previous window) :
    ∀ state, (p13ActualAttachmentSystem ctx window.1).value state ≠
      fork.residual.assignment :=
  fork.residual.noState

/-- The retained selected window is the exact trigger for the subsequent
surplus/corridor node; node `[158]` does not execute or charge that node. -/
theorem p13ActualAttachmentColdFork_same_selected_window
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {window : P13ActualSelectedWindow ctx}
    (fork : P13ActualAttachmentColdFork ctx previous window) :
    fork.selectedWindow = window :=
  fork.sameWindow

/-- Worst-case classifier reference budget: `2^13` assignments, at most `n`
actual outside-vertex states, and thirteen adjacency-bit comparisons per
state. -/
noncomputable def p13ActualAttachmentColdForkCheckBudget
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13ActualSelectedWindow ctx) : Nat :=
  (p13ActualAttachmentSystem ctx window.1).assignments.card *
    (p13ActualAttachmentSystem ctx window.1).states.card * 13

theorem p13ActualAttachmentColdFork_states_card_le_vertices
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13ActualSelectedWindow ctx) :
    (p13ActualAttachmentSystem ctx window.1).states.card ≤
      ctx.G.object.input.vertices.card := by
  change (p13ActualAttachmentStates ctx window.1).card ≤
    ctx.G.object.input.vertices.card
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  letI : FinEnum (P13ActualAttachmentState ctx window.1) :=
    p13ActualAttachmentStates ctx window.1
  rw [FinEnum.card_eq_fintypeCard, FinEnum.card_eq_fintypeCard]
  exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective

theorem p13ActualAttachmentColdForkCheckBudget_linear
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13ActualSelectedWindow ctx) :
    p13ActualAttachmentColdForkCheckBudget ctx window ≤
      106496 * ctx.G.object.input.vertices.card := by
  have assignments :
      (p13ActualAttachmentSystem ctx window.1).assignments.card = 8192 := by
    rw [(p13ActualAttachmentSystem ctx window.1).assignments_card,
      p13ActualAttachmentSystem_coordinateCard]
    native_decide
  rw [p13ActualAttachmentColdForkCheckBudget, assignments]
  have stateBound := p13ActualAttachmentColdFork_states_card_le_vertices ctx window
  omega

end Erdos64EG.Internal
