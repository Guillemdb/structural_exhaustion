import Erdos64EG.Shared.P13MultiScaleConnectorState

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Residual-owned compatible completions

These are the graph-semantic objects consumed by Core's sequential
compatible-extension ledger.  They contain no node predecessor, handoff,
route, or decision: the framework stage owns all of that bookkeeping.
-/

/-- One graph-owned completion of one selected window. -/
structure P13LocalGraphCompletion
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13SelectedConnectorWindow ctx) where
  object : Graph.FiniteObject ctx.G.Vertex
  windowPath : SimpleGraph.pathGraph 13 ↪g object.graph
  windowExact : ∀ position, windowPath position = window.1 position
  support : Finset ctx.G.Vertex
  windowSupported : ∀ position, window.1 position ∈ support
  outsideSupportPreserved : ∀ left right,
    left ∉ support → right ∉ support →
      (object.graph.Adj left right ↔ ctx.G.object.graph.Adj left right)
  connector : Fin 15 → ctx.G.Vertex
  connectorOutside : ∀ slot position, connector slot ≠ window.1 position
  connectorSupported : ∀ slot, connector slot ∈ support
  connectorSimple : ∀ left right, connector left = connector right → left = right
  connectorAdjacent : ∀ slot : Fin 14,
    object.graph.Adj (connector ⟨slot.1, by omega⟩)
      (connector ⟨slot.1 + 1, by omega⟩)
  safeBarrier : ∀ index : P13BarrierIndex,
    let source := by
      letI : DecidableRel object.graph.Adj := object.input.decideAdj
      exact Graph.InducedPathAttachment.attachmentLabel windowPath
        (connector ⟨0, by decide⟩)
    let middle := by
      letI : DecidableRel object.graph.Adj := object.input.decideAdj
      exact Graph.InducedPathAttachment.attachmentLabel windowPath
        (connector (p13BarrierLeftSlot index))
    let target := by
      letI : DecidableRel object.graph.Adj := object.input.decideAdj
      exact Graph.InducedPathAttachment.attachmentLabel windowPath
        (connector (p13BarrierTotalSlot index))
    P13Legal source ∧ P13Legal middle ∧ P13Legal target ∧
      p13C index.leftLength source middle = 1 ∧
      p13C index.rightLength middle target = 1
  baseline : packedStaticInput.minimumDegree ≤ object.minDegree
  targetAvoiding : ¬PackedTarget (Graph.PackedFiniteObject.pack object)

noncomputable def p13LocalResponse
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {window : P13SelectedConnectorWindow ctx}
    (state : P13LocalGraphCompletion ctx window)
    (index : P13BarrierIndex) : Bool := by
  letI : DecidableRel state.object.graph.Adj := state.object.input.decideAdj
  let source := Graph.InducedPathAttachment.attachmentLabel state.windowPath
    (state.connector ⟨0, by decide⟩)
  let target := Graph.InducedPathAttachment.attachmentLabel state.windowPath
    (state.connector (p13BarrierTotalSlot index))
  exact decide (p13C (index.leftLength + index.rightLength) source target = 1)

/-- One graph-owned completion shared by every currently retained window. -/
structure P13GlobalGraphCompletion
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) where
  object : Graph.FiniteObject ctx.G.Vertex
  windowPath : ∀ window : P13SelectedConnectorWindow ctx,
    SimpleGraph.pathGraph 13 ↪g object.graph
  windowExact : ∀ window position, windowPath window position = window.1 position
  baseline : packedStaticInput.minimumDegree ≤ object.minDegree
  targetAvoiding : ¬PackedTarget (Graph.PackedFiniteObject.pack object)

noncomputable def p13OriginalGlobalCompletion
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    P13GlobalGraphCompletion ctx where
  object := ctx.G.object
  windowPath := fun window => window.1
  windowExact := by intros; rfl
  baseline := ctx.baseline
  targetAvoiding := ctx.avoids

noncomputable def p13GlobalResponse
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (global : P13GlobalGraphCompletion ctx)
    (window : P13SelectedConnectorWindow ctx)
    (localState : P13LocalGraphCompletion ctx window)
    (index : P13BarrierIndex) : Bool := by
  letI : DecidableRel global.object.graph.Adj := global.object.input.decideAdj
  let source := Graph.InducedPathAttachment.attachmentLabel
    (global.windowPath window) (localState.connector ⟨0, by decide⟩)
  let target := Graph.InducedPathAttachment.attachmentLabel
    (global.windowPath window)
      (localState.connector (p13BarrierTotalSlot index))
  exact decide (p13C (index.leftLength + index.rightLength) source target = 1)

end Erdos64EG.Internal
