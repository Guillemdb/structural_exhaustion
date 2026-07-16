import StructuralExhaustion.Examples.InducedPathColdSkeletonOwnerChange
import StructuralExhaustion.Routes.InducedPathCrossWindowTokenPair

namespace StructuralExhaustion.Examples.CrossWindowTokenPairRoute

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Examples.PackedSupportOwnerChange

universe u

variable {V : Type u} {object : FiniteObject V}

/-- Exact non-Erdős transfer: the executed one-edge owner-change fixture feeds
the same zero-check route and pins both supplied window endpoints. -/
theorem exact_transfer (edge : CrossWindowEdge object) :
    ∃ table hit crossing,
      InducedPathColdSkeletonOwnerChange.run edge.input =
          .firstCrossWindow table hit crossing ∧
      (Routes.InducedPathCrossWindowTokenPair.route crossing).leftWindow =
          edge.leftWindow ∧
        (Routes.InducedPathCrossWindowTokenPair.route crossing).leftPosition =
          edge.leftPosition ∧
        (Routes.InducedPathCrossWindowTokenPair.route crossing).rightWindow =
          edge.rightWindow ∧
        (Routes.InducedPathCrossWindowTokenPair.route crossing).rightPosition =
          edge.rightPosition ∧
        (Routes.InducedPathCrossWindowTokenPair.route crossing).leftToken.2.2.1 =
          InducedPathWindowLedger.selectedWindow object edge.rightWindow
            edge.rightPosition ∧
        (Routes.InducedPathCrossWindowTokenPair.route crossing).rightToken.2.2.1 =
          InducedPathWindowLedger.selectedWindow object edge.leftWindow
            edge.leftPosition := by
  rcases edge.run_firstCrossWindow_exact with
    ⟨table, hit, crossing, runExact, _hitZero, leftWindow, leftPosition,
      rightWindow, rightPosition, _leftVertex, _rightVertex,
      _leftTokenWindow, leftNeighbor, _leftSubtype,
      _rightTokenWindow, rightNeighbor, _rightSubtype⟩
  refine ⟨table, hit, crossing, runExact, ?_⟩
  exact ⟨(Routes.InducedPathCrossWindowTokenPair.route crossing).leftWindowExact.trans
      leftWindow,
    (Routes.InducedPathCrossWindowTokenPair.route crossing).leftPositionExact.trans
      leftPosition,
    (Routes.InducedPathCrossWindowTokenPair.route crossing).rightWindowExact.trans
      rightWindow,
    (Routes.InducedPathCrossWindowTokenPair.route crossing).rightPositionExact.trans
      rightPosition,
    leftNeighbor,
    rightNeighbor⟩

theorem zero_new_checks :
    Routes.InducedPathCrossWindowTokenPair.additionalChecks = 0 :=
  Routes.InducedPathCrossWindowTokenPair.additionalChecks_eq_zero

end StructuralExhaustion.Examples.CrossWindowTokenPairRoute
