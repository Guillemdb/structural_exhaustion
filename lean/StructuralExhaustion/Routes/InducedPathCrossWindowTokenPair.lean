import StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange

namespace StructuralExhaustion.Routes.InducedPathCrossWindowTokenPair

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathWindowLedger
open scoped Sym2

universe u

variable {V : Type u} {object : FiniteObject V}
variable {input : InducedPathColdSkeletonOwnerChange.Input object}
variable {table : InducedPathColdSkeletonOwnerChange.Input.OwnerTable input}
variable {hit : Core.FiniteSearch.FirstHit input.edgeOrder
  (input.OwnerChangeAt table)}

/-!
# Exact cross-window token-pair handoff

This route performs no search.  It projects the two already computed endpoint
tokens of a `FirstCrossWindow` and records that they are the opposite oriented
contributions of one literal undirected graph edge.
-/

/-- Exact typed bookkeeping output for one cross-window edge. -/
structure CrossWindowTokenPair
    (source : InducedPathColdSkeletonOwnerChange.FirstCrossWindow
      input table hit) where
  leftToken : Token object
  leftTokenExact : leftToken = source.leftToken
  rightToken : Token object
  rightTokenExact : rightToken = source.rightToken
  tokensDistinct : leftToken ≠ rightToken
  leftSubtype : tokenSubtype object leftToken = .crossWindow
  rightSubtype : tokenSubtype object rightToken = .crossWindow
  leftWindow : WindowIndex object
  leftWindowExact : leftWindow = source.leftSlot.window
  leftPosition : Fin 13
  leftPositionExact : leftPosition = source.leftSlot.position
  rightWindow : WindowIndex object
  rightWindowExact : rightWindow = source.rightSlot.window
  rightPosition : Fin 13
  rightPositionExact : rightPosition = source.rightSlot.position
  leftVertex : V
  leftVertexExact : leftVertex = input.path.getVert hit.value.1
  rightVertex : V
  rightVertexExact : rightVertex = input.path.getVert (hit.value.1 + 1)
  adjacent : object.graph.Adj leftVertex rightVertex
  leftOrientedContribution :
    selectedWindow object leftToken.1 leftToken.2.1 = leftVertex ∧
      leftToken.2.2.1 = rightVertex
  rightOrientedContribution :
    selectedWindow object rightToken.1 rightToken.2.1 = rightVertex ∧
      rightToken.2.2.1 = leftVertex
  sameLiteralEdge : s(leftVertex, rightVertex) = s(rightVertex, leftVertex)

/-- Execute the zero-check projection route. -/
noncomputable def route
    (source : InducedPathColdSkeletonOwnerChange.FirstCrossWindow
      input table hit) : CrossWindowTokenPair source := by
  classical
  refine {
    leftToken := source.leftToken
    leftTokenExact := rfl
    rightToken := source.rightToken
    rightTokenExact := rfl
    tokensDistinct := ?_
    leftSubtype := source.leftTokenSubtype
    rightSubtype := source.rightTokenSubtype
    leftWindow := source.leftSlot.window
    leftWindowExact := rfl
    leftPosition := source.leftSlot.position
    leftPositionExact := rfl
    rightWindow := source.rightSlot.window
    rightWindowExact := rfl
    rightPosition := source.rightSlot.position
    rightPositionExact := rfl
    leftVertex := input.path.getVert hit.value.1
    leftVertexExact := rfl
    rightVertex := input.path.getVert (hit.value.1 + 1)
    rightVertexExact := rfl
    adjacent := source.adjacent
    leftOrientedContribution := ?_
    rightOrientedContribution := ?_
    sameLiteralEdge := Sym2.eq_swap
  }
  · intro equal
    have windowEqual : source.leftSlot.window = source.rightSlot.window := by
      calc
        source.leftSlot.window = source.leftToken.1 :=
          source.leftTokenWindow.symm
        _ = source.rightToken.1 := congrArg Sigma.fst equal
        _ = source.rightSlot.window := source.rightTokenWindow
    exact source.ownersDistinct windowEqual
  · constructor
    · simpa only [source.leftTokenWindow, source.leftTokenPosition] using
        source.leftSlot.exact
    · exact source.leftTokenNeighbor
  · constructor
    · simpa only [source.rightTokenWindow, source.rightTokenPosition] using
        source.rightSlot.exact
    · exact source.rightTokenNeighbor

/-- The route adds no primitive checks after node 169. -/
def additionalChecks : Nat := 0

theorem additionalChecks_eq_zero : additionalChecks = 0 := rfl

end StructuralExhaustion.Routes.InducedPathCrossWindowTokenPair
