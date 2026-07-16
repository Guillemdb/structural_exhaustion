import StructuralExhaustion.Core.FiniteSearch
import StructuralExhaustion.Graph.InducedPathConnectorCycle
import StructuralExhaustion.Graph.InducedPathColdStubSelection
import StructuralExhaustion.Graph.InducedPathColdGermScale
import StructuralExhaustion.Graph.Path

namespace StructuralExhaustion.Examples.FiniteConnectorSequence

open StructuralExhaustion

/-!
# Transfer fixture for graph-owned connector-sequence search

This fixture is independent of the Erdos application.  It searches literal
three-slot vertex sequences in the three-vertex path graph, using only the
graph's decidable adjacency and a finite sequence universe.  It exercises the
same proof-carrying finite-search pattern as the multi-scale window connector
layer.
-/

abbrev Sequence := Fin 3 → Fin 3

@[implicit_reducible]
def sequences : FinEnum Sequence := inferInstance

def Valid (sequence : Sequence) : Prop :=
  Function.Injective sequence ∧
    (SimpleGraph.pathGraph 3).Adj (sequence 0) (sequence 1) ∧
    (SimpleGraph.pathGraph 3).Adj (sequence 1) (sequence 2)

def validDecidable (sequence : Sequence) : Decidable (Valid sequence) := by
  letI : DecidableRel (SimpleGraph.pathGraph 3).Adj :=
    Graph.pathGraphAdjDecidable 3
  unfold Valid Function.Injective
  infer_instance

def canonical : Sequence := fun position => position

theorem canonical_valid : Valid canonical := by
  constructor
  · intro left right equal
    exact equal
  · constructor <;> simp [canonical, SimpleGraph.pathGraph_adj]

def run := Core.FiniteSearch.search sequences Valid validDecidable

/-- The generic proof-carrying search finds an actual connector sequence; no
state or nonemptiness certificate is supplied to the runner. -/
theorem run_finds_actual_sequence :
    ∃ sequence, run.value? = some sequence ∧ Valid sequence := by
  exact Core.FiniteSearch.search_complete sequences Valid validDecidable
    ⟨canonical, canonical_valid⟩

/-- Non-Erdős transfer of the arbitrary outside-connector cycle theorem,
with the accepted length specialized to the literal constructed length. -/
def connectorClosesExactLength
    {V : Type} {G : SimpleGraph V} {order : Nat}
    (path : SimpleGraph.pathGraph order ↪g G)
    {leftOutside rightOutside : V}
    (connector : G.Walk leftOutside rightOutside)
    (connectorPath : connector.IsPath)
    (connectorOutside : ∀ vertex ∈ connector.support,
      ∀ position : Fin order, vertex ≠ path position)
    (outsideDistinct : leftOutside ≠ rightOutside)
    (leftPosition rightPosition : Fin order)
    (leftAdjacent : G.Adj leftOutside (path leftPosition))
    (rightAdjacent : G.Adj rightOutside (path rightPosition)) :
    Graph.CycleWithLength G (fun length => length =
      connector.length + 2 +
        Graph.InducedPathAttachment.positionDistance
          leftPosition rightPosition) :=
  Graph.InducedPathConnectorCycle.connectorCycle
    (fun length => length = connector.length + 2 +
      Graph.InducedPathAttachment.positionDistance leftPosition rightPosition)
    path connector connectorPath connectorOutside outsideDistinct
    leftPosition rightPosition leftAdjacent rightAdjacent rfl

/-- Problem-independent transfer of the selected-window entry classifier.
For any finite graph with pointwise degree at least three, the framework
itself finds either a literal high-degree window position or a canonical
external cubic stub; neither witness is supplied by the caller. -/
theorem coldStubSelectionIsExhaustive
    {V : Type} (object : Graph.FiniteObject V)
    (baseline : ∀ vertex, 3 ≤ object.degree vertex)
    (window : Graph.InducedPathWindowLedger.WindowIndex object) :
    (∃ position high,
      Graph.InducedPathColdStubSelection.classify object baseline window =
        .high position high) ∨
    (∃ stub same,
      Graph.InducedPathColdStubSelection.classify object baseline window =
        .cubic stub same) :=
  Graph.InducedPathColdStubSelection.classify_exhaustive
    object baseline window

/-- Non-Erdős transfer of the exact graph-owned germ scale split.  The short
side retains a bounded literal two-endpoint path residual; the long side
retains the strict inequality and canonical finite support positions. -/
theorem coldGermScaleIsExhaustive
    {V : Type} {object : Graph.FiniteObject V}
    (producer : Graph.InducedPathColdCorridor.Producer object)
    (LengthOK : Nat → Prop)
    (stub : Graph.InducedPathColdCorridor.CubicStub object)
    (germ : Graph.InducedPathColdCorridor.Producer.ColdStructuralGerm
      producer LengthOK stub) (scale : Nat) :
    (∃ residual,
      Graph.InducedPathColdGermScale.route producer LengthOK stub germ scale =
        .short residual) ∨
    (∃ residual,
      Graph.InducedPathColdGermScale.route producer LengthOK stub germ scale =
        .long residual) :=
  Graph.InducedPathColdGermScale.route_exhaustive
    producer LengthOK stub germ scale

end StructuralExhaustion.Examples.FiniteConnectorSequence
