import StructuralExhaustion.Examples.DeletedEdgeReturnBoundaryStar
import StructuralExhaustion.Examples.DeletedEdgeReturnChordResolution
import StructuralExhaustion.Graph.DeletedEdgeReturnNormalizedBoundary

namespace StructuralExhaustion.Examples.DeletedEdgeReturnNormalizedBoundaryK4

open StructuralExhaustion
open StructuralExhaustion.Examples.DeletedEdgeReturnThirdIncidenceK4

/-!
The textbook graph `K₄` exercises both inputs of the normalized one-return
boundary.  The chord branch chooses the strict shorter return and its old
first step as outside incidence.  The pre-existing outside branch retains its
return and selected third incidence.  Both use the same graph-owned cubic
ownership theorem and perform no new scan.
-/

namespace Chord

open StructuralExhaustion.Examples.DeletedEdgeReturnChordResolutionK4

noncomputable def rejectedRun :
    Graph.DeletedEdgeReturnNormalizedBoundary.RejectedChordRun
      chordSetup LengthFour inferInstance where
  input := input
  lengthRejected := by native_decide
  shorter := input.shorterReturn
  shorterExact := rfl
  strict := input.shorterReturn_strict
  runExact := rfl

noncomputable def normalizedInput :
    Graph.DeletedEdgeReturnNormalizedBoundary.Input
      chordSetup LengthFour inferInstance 4 :=
  .rejectedChord rejectedRun (by native_decide)

noncomputable def normalized :=
  Graph.DeletedEdgeReturnNormalizedBoundary.normalize normalizedInput

example : normalized.selectedReturn.path.length <
    chordSetup.returnPath.path.length :=
  normalized.decreaseEvidence

example : chordSetup.firstNext ∉ normalized.selectedReturn.path.support := by
  simpa [normalized,
    Graph.DeletedEdgeReturnNormalizedBoundary.normalize,
    normalizedInput] using normalized.outside_not_mem_support

example : normalized.selectedReturn.path.support.length ≤ 4 :=
  normalized.support_bound

example (vertex : Vertex) (adjacent : object.graph.Adj rootDart.snd vertex) :
    vertex = normalized.cubicStar.first ∨
      vertex = normalized.cubicStar.second ∨
      vertex = normalized.cubicStar.third :=
  normalized.ownsAllRootIncidences vertex adjacent

end Chord

namespace Outside

open StructuralExhaustion.Examples.DeletedEdgeReturnBoundaryStarK4
open StructuralExhaustion.Examples.DeletedEdgeReturnChordResolutionK4

noncomputable def normalizedInput :
    Graph.DeletedEdgeReturnNormalizedBoundary.Input
      outsideSetup LengthFour inferInstance 3 :=
  .outsideBoundary branch (by native_decide)

noncomputable def normalized :=
  Graph.DeletedEdgeReturnNormalizedBoundary.normalize normalizedInput

example : normalized.selectedReturn.path.length =
    outsideSetup.returnPath.path.length :=
  normalized.decreaseEvidence

example : outsideSetup.third.hit.value ∉
    normalized.selectedReturn.path.support := by
  simpa [normalized,
    Graph.DeletedEdgeReturnNormalizedBoundary.normalize,
    normalizedInput] using normalized.outside_not_mem_support

example : normalized.selectedReturn.path.support.length ≤ 3 :=
  normalized.support_bound

example : Graph.DeletedEdgeReturnNormalizedBoundary.additionalChecks = 0 :=
  Graph.DeletedEdgeReturnNormalizedBoundary.additionalChecks_eq_zero

end Outside


end StructuralExhaustion.Examples.DeletedEdgeReturnNormalizedBoundaryK4
