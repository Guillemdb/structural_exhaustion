import StructuralExhaustion.Examples.DeletedEdgeReturnThirdIncidence
import StructuralExhaustion.Graph.DeletedEdgeReturnBoundaryStar

namespace StructuralExhaustion.Examples.DeletedEdgeReturnBoundaryStarK4

open StructuralExhaustion
open StructuralExhaustion.Examples.DeletedEdgeReturnThirdIncidenceK4

/-!
The shorter deleted-edge return in `K₄` transfers the exact reusable
outside-boundary-to-cubic-star construction.  The construction consumes the
already computed third-incidence outcome and performs no further scan.
-/

def outsideProof :
    outsideSetup.third.hit.value ∉ outsideSetup.returnPath.path.support := by
  native_decide

theorem outsideRunExact :
    Graph.DeletedEdgeReturnThirdIncidence.run outsideSetup =
      .outsideBoundary outsideProof := by
  simp only [Graph.DeletedEdgeReturnThirdIncidence.run]
  split
  · rename_i member
    exact (outsideProof member).elim
  · rfl

def branch :
    Graph.DeletedEdgeReturnBoundaryStar.OutsideRun outsideSetup where
  outside := outsideProof
  runExact := outsideRunExact

def boundary := branch.orientedBoundary

example : rootDart.snd ∈ outsideSetup.returnPath.path.support :=
  boundary.root_mem_support

example : outsideSetup.third.hit.value ∉
    outsideSetup.returnPath.path.support :=
  boundary.selected_not_mem_support

example : object.graph.Adj rootDart.snd outsideSetup.third.hit.value :=
  boundary.selected_adjacent

def star := branch.cubicStar

example : star.first = outsideSetup.firstNext := rfl

example : star.second = rootDart.fst := rfl

example : star.third = outsideSetup.third.hit.value := rfl

def shape := branch.switchBoundaryShape

example (vertex : Vertex)
    (adjacent : object.graph.Adj rootDart.snd vertex) :
    ∃ index, shape.boundaryVertex index = vertex :=
  branch.ownsAllRootIncidences vertex adjacent

example : branch.additionalChecks = 0 := branch.additionalChecks_eq_zero

end StructuralExhaustion.Examples.DeletedEdgeReturnBoundaryStarK4
