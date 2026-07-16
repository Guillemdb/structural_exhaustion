import StructuralExhaustion.Graph.InducedPathBranchExcessComponentEntry
import StructuralExhaustion.Graph.InducedPathColdBranchExcess
import StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange

namespace StructuralExhaustion.Routes.InducedPathCrossWindowIncidencePair

open StructuralExhaustion
open StructuralExhaustion.Graph
open InducedPathWindowLedger
open InducedPathColdCorridor
open InducedPathColdSkeleton
open InducedPathColdSkeletonOwnerChange
open scoped Sym2

universe u

variable {V : Type u} {object : FiniteObject V}

/-!
# Direct cross-window incidence-pair route

This route consumes the exact deleted-endpoint residual of one selected
branch-excess incidence.  It recovers the unique ambient-cubic packed-window
slot containing that endpoint and constructs the reverse incidence token.
The result is the two opposite orientations of one literal graph edge.

Unlike `InducedPathCrossWindowTokenPair`, this route does not manufacture an
owner-change path, owner table, or first-hit cursor.  It uses only the one
stored endpoint-membership proof and the disjointness of the selected packing.
-/

/-- Exact two-token handoff for one branch-excess edge joining distinct
selected ambient-cubic windows. -/
structure CrossWindowIncidencePair
    (stub : CubicStub object)
    (residual : InducedPathBranchExcessComponentEntry.CrossWindowResidual stub) where
  rightSlot : OwnedSlot object stub.neighbor
  leftWindow : WindowIndex object
  leftWindowExact : leftWindow = stub.window
  rightWindow : WindowIndex object
  rightWindowExact : rightWindow = rightSlot.window
  rightLocalToken :
    InducedPathColdBranchExcess.WindowToken object rightSlot.window
  rightLocalTokenNeighbor : rightLocalToken.2.1 =
    selectedWindow object stub.window stub.position
  windowsDistinct : leftWindow ≠ rightWindow
  leftToken : Token object
  leftTokenExact : leftToken = stub.token
  rightToken : Token object
  rightTokenExact : rightToken =
    InducedPathColdBranchExcess.toToken rightLocalToken
  rightTokenWindow : rightToken.1 = rightSlot.window
  rightTokenPosition : rightToken.2.1 = rightSlot.position
  rightTokenNeighbor : rightToken.2.2.1 =
    selectedWindow object stub.window stub.position
  tokensDistinct : leftToken ≠ rightToken
  leftSubtype : tokenSubtype object leftToken = .crossWindow
  rightSubtype : tokenSubtype object rightToken = .crossWindow
  adjacent : object.graph.Adj
    (selectedWindow object stub.window stub.position) stub.neighbor
  leftOrientedContribution :
    selectedWindow object leftToken.1 leftToken.2.1 =
        selectedWindow object stub.window stub.position ∧
      leftToken.2.2.1 = stub.neighbor
  rightOrientedContribution :
    selectedWindow object rightToken.1 rightToken.2.1 = stub.neighbor ∧
      rightToken.2.2.1 = selectedWindow object stub.window stub.position
  sameLiteralEdge :
    s(selectedWindow object stub.window stub.position, stub.neighbor) =
      s(stub.neighbor, selectedWindow object stub.window stub.position)

/-- Execute the local proof projection.  `OwnedSlot.exists_of_mem_deleted`
selects a witness from the already proved endpoint membership; no ambient
window or vertex family is scanned here. -/
noncomputable def route
    (stub : CubicStub object)
    (residual : InducedPathBranchExcessComponentEntry.CrossWindowResidual stub) :
    CrossWindowIncidencePair stub residual := by
  classical
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  let right : OwnedSlot object stub.neighbor :=
    Classical.choice (OwnedSlot.exists_of_mem_deleted residual.endpointDeleted)
  let left : OwnedSlot object
      (selectedWindow object stub.window stub.position) := {
    window := stub.window
    cubic := stub.cubic
    position := stub.position
    exact := rfl
  }
  have windowsDistinct : left.window ≠ right.window := by
    intro equal
    have rightExact := right.exact
    rw [← equal] at rightExact
    have ownSupport : stub.neighbor ∈
        InducedPathPacking.support object 13
          (selectedWindow object stub.window) :=
      (InducedPathPacking.mem_support_iff object 13
        (selectedWindow object stub.window) stub.neighbor).2
        ⟨right.position, by simpa [left] using rightExact⟩
    exact token_neighbor_not_mem_own_support object stub.token ownSupport
  have leftNotRightSupport :
      selectedWindow object stub.window stub.position ∉
        InducedPathPacking.support object 13
          (selectedWindow object right.window) := by
    intro member
    let candidate : OwnedSlot object
        (selectedWindow object stub.window stub.position) := {
      window := right.window
      cubic := right.cubic
      position := Classical.choose
        ((InducedPathPacking.mem_support_iff object 13
          (selectedWindow object right.window) _).1 member)
      exact := Classical.choose_spec
        ((InducedPathPacking.mem_support_iff object 13
          (selectedWindow object right.window) _).1 member)
    }
    exact windowsDistinct (OwnedSlot.window_unique left candidate)
  have leftExternal : selectedWindow object stub.window stub.position ∈
      externalNeighbors object right.window right.position := by
    rw [externalNeighbors, Finset.mem_sdiff]
    constructor
    · rw [ambientNeighbors, SimpleGraph.mem_neighborFinset, right.exact]
      exact stub.adjacent.symm
    · intro internal
      apply leftNotRightSupport
      rw [InducedPathPacking.mem_support_iff]
      unfold internalNeighbors at internal
      rw [Finset.mem_image] at internal
      rcases internal with ⟨position, _member, exact⟩
      exact ⟨position, exact⟩
  let reverseLocal : InducedPathColdBranchExcess.WindowToken object right.window :=
    ⟨right.position,
      ⟨selectedWindow object stub.window stub.position, leftExternal⟩⟩
  let reverse : Token object :=
    InducedPathColdBranchExcess.toToken reverseLocal
  refine {
    rightSlot := right
    leftWindow := stub.window
    leftWindowExact := rfl
    rightWindow := right.window
    rightWindowExact := rfl
    rightLocalToken := reverseLocal
    rightLocalTokenNeighbor := rfl
    windowsDistinct := windowsDistinct
    leftToken := stub.token
    leftTokenExact := rfl
    rightToken := reverse
    rightTokenExact := rfl
    rightTokenWindow := rfl
    rightTokenPosition := rfl
    rightTokenNeighbor := rfl
    tokensDistinct := ?_
    leftSubtype := ?_
    rightSubtype := ?_
    adjacent := stub.adjacent
    leftOrientedContribution := ⟨rfl, rfl⟩
    rightOrientedContribution := by
      dsimp [reverse, reverseLocal]
      exact ⟨right.exact, rfl⟩
    sameLiteralEdge := Sym2.eq_swap
  }
  · intro equal
    exact windowsDistinct (congrArg Sigma.fst equal)
  · rw [tokenSubtype, if_pos]
    change stub.neighbor ∈
      InducedPathPacking.coveredVertices object 13 (by decide)
    exact right.exact ▸ selectedWindow_mem_covered object
      right.window right.position
  · rw [tokenSubtype, if_pos]
    change selectedWindow object stub.window stub.position ∈
      InducedPathPacking.coveredVertices object 13 (by decide)
    exact selectedWindow_mem_covered object stub.window stub.position

/-- The route performs no new finite search after endpoint deletion membership
has been proved by its predecessor. -/
def additionalChecks : Nat := 0

theorem additionalChecks_eq_zero : additionalChecks = 0 := rfl

private theorem token_ext
    {left right : Token object}
    (windowEqual : left.1 = right.1)
    (positionEqual : left.2.1 = right.2.1)
    (neighborEqual : left.2.2.1 = right.2.2.1) : left = right := by
  rcases left with ⟨leftWindow, leftPosition, leftNeighbor⟩
  rcases right with ⟨rightWindow, rightPosition, rightNeighbor⟩
  dsimp at windowEqual positionEqual neighborEqual
  subst rightWindow
  subst rightPosition
  have neighborSubtypeEqual : leftNeighbor = rightNeighbor :=
    Subtype.ext neighborEqual
  subst rightNeighbor
  rfl

/-- Opposite orientation is injective on these exact incidence pairs: equality
of the right tokens forces equality of the left tokens. -/
theorem leftToken_eq_of_rightToken_eq
    {leftStub rightStub : CubicStub object}
    {leftResidual : InducedPathBranchExcessComponentEntry.CrossWindowResidual
      leftStub}
    {rightResidual : InducedPathBranchExcessComponentEntry.CrossWindowResidual
      rightStub}
    (leftPair : CrossWindowIncidencePair leftStub leftResidual)
    (rightPair : CrossWindowIncidencePair rightStub rightResidual)
    (equal : leftPair.rightToken = rightPair.rightToken) :
    leftPair.leftToken = rightPair.leftToken := by
  have sourceVertexEqual :
      selectedWindow object leftStub.window leftStub.position =
        selectedWindow object rightStub.window rightStub.position := by
    calc
      selectedWindow object leftStub.window leftStub.position =
          leftPair.rightToken.2.2.1 := leftPair.rightTokenNeighbor.symm
      _ = rightPair.rightToken.2.2.1 :=
        congrArg (fun token : Token object => token.2.2.1) equal
      _ = selectedWindow object rightStub.window rightStub.position :=
        rightPair.rightTokenNeighbor
  let leftSource : OwnedSlot object
      (selectedWindow object leftStub.window leftStub.position) := {
    window := leftStub.window
    cubic := leftStub.cubic
    position := leftStub.position
    exact := rfl
  }
  let rightSource : OwnedSlot object
      (selectedWindow object leftStub.window leftStub.position) := {
    window := rightStub.window
    cubic := rightStub.cubic
    position := rightStub.position
    exact := sourceVertexEqual.symm
  }
  have windowEqual : leftStub.window = rightStub.window :=
    OwnedSlot.window_unique leftSource rightSource
  have positionEqual : leftStub.position = rightStub.position :=
    OwnedSlot.position_unique leftSource rightSource windowEqual
  have neighborEqual : leftStub.neighbor = rightStub.neighbor := by
    calc
      leftStub.neighbor =
          selectedWindow object leftPair.rightToken.1
            leftPair.rightToken.2.1 :=
        leftPair.rightOrientedContribution.1.symm
      _ = selectedWindow object rightPair.rightToken.1
            rightPair.rightToken.2.1 := by rw [equal]
      _ = rightStub.neighbor := rightPair.rightOrientedContribution.1
  have stubTokenEqual : leftStub.token = rightStub.token := by
    exact token_ext windowEqual positionEqual neighborEqual
  exact leftPair.leftTokenExact.trans
    (stubTokenEqual.trans rightPair.leftTokenExact.symm)

end StructuralExhaustion.Routes.InducedPathCrossWindowIncidencePair
