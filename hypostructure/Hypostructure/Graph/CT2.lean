import Hypostructure.CT2.Automation
import Hypostructure.Graph.Progress

/-!
# Graph adapter for CT2 edge deletion

The graph layer supplies the primitive edge deletion and proves its strict
lexicographic decrease.  The finite edge carrier and selected index remain
owned by the incoming residual; this module does not enumerate graph edges.
-/

namespace Hypostructure.Graph.CT2

universe uVertex uBranch uPrevious

/-- Local CT2 specification for deleting one selected certified edge. -/
def edgeDeletionSpec
    (Baseline : FiniteObject.{uVertex} -> Prop)
    (BranchState : FiniteObject.{uVertex} -> Type uBranch)
    (Admissible : (object : FiniteObject.{uVertex}) ->
      BranchState object -> object.graph.edgeSet -> Prop)
    (Previous : Type uPrevious) :
    _root_.Hypostructure.CT2.Spec
      (problem Baseline BranchState) Previous where
  Piece := fun object => object.graph.edgeSet
  Proper := fun _edge => True
  Admissible := fun {object} state edge => Admissible object state edge
  delete := fun {object} edge => object.deleteEdge edge

/-- Build the selected-edge CT2 capability without deriving an edge schedule.
Applications provide the two semantic preservation lemmas; Graph discharges
properness and strict progress from the certified edge itself. -/
def edgeDeletionCapability
    {Previous : Type uPrevious}
    (Baseline : FiniteObject.{uVertex} -> Prop)
    (BranchState : FiniteObject.{uVertex} -> Type uBranch)
    (Target : FiniteObject.{uVertex} -> Prop)
    (Admissible : (object : FiniteObject.{uVertex}) ->
      BranchState object -> object.graph.edgeSet -> Prop)
    (context : Core.Residual.Query Previous fun _previous =>
      Core.MinimalCounterexampleContext
        (problem Baseline BranchState) Target
        (lexicographicProgress Baseline BranchState))
    (pieces : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration
        ((context.read previous).G.graph.edgeSet))
    (selectedIndex : Core.Residual.Query Previous fun previous =>
      Fin (pieces.read previous).card)
    (admissibleDecidable : (object : FiniteObject.{uVertex}) ->
      (state : BranchState object) -> (edge : object.graph.edgeSet) ->
        Decidable (Admissible object state edge))
    (preservesBaseline : forall {object : FiniteObject.{uVertex}}
      (state : BranchState object) (edge : object.graph.edgeSet),
      Admissible object state edge -> Baseline object ->
        Baseline (object.deleteEdge edge))
    (targetMonotone : forall {object : FiniteObject.{uVertex}}
      (state : BranchState object) (edge : object.graph.edgeSet),
      Admissible object state edge -> Baseline object ->
      Target (object.deleteEdge edge) -> Target object) :
    _root_.Hypostructure.CT2.Capability Target
      (lexicographicProgress Baseline BranchState)
      (edgeDeletionSpec Baseline BranchState Admissible Previous) where
  context := context
  pieces := pieces
  selectedIndex := selectedIndex
  properDecidable := fun _edge => .isTrue trivial
  admissibleDecidable := fun state edge =>
    admissibleDecidable _ state edge
  decreases := by
    intro object _state edge _proper _admissible
    exact (ProperSubgraph.deleteEdge object edge).smaller
      Baseline BranchState
  preservesBaseline := by
    intro object state edge _proper admissible baseline
    exact preservesBaseline state edge admissible baseline
  targetMonotone := by
    intro object state edge _proper admissible baseline reducedTarget
    exact targetMonotone state edge admissible baseline reducedTarget

/-- The framework-selected graph edge belongs to the exact inherited carrier. -/
theorem selectedEdge_mem
    {Previous : Type uPrevious}
    {Baseline : FiniteObject.{uVertex} -> Prop}
    {BranchState : FiniteObject.{uVertex} -> Type uBranch}
    {Target : FiniteObject.{uVertex} -> Prop}
    {Admissible : (object : FiniteObject.{uVertex}) ->
      BranchState object -> object.graph.edgeSet -> Prop}
    {capability : _root_.Hypostructure.CT2.Capability Target
      (lexicographicProgress Baseline BranchState)
      (edgeDeletionSpec Baseline BranchState Admissible Previous)}
    (previous : Previous) :
    capability.selectedPiece previous ∈
      (capability.piecesAt previous).values :=
  capability.selectedPiece_mem previous

/-- CT2 criticality says that the residual-selected edge cannot satisfy the
declared baseline-preserving deletion condition. -/
theorem selectedEdge_notAdmissible
    {Previous : Type uPrevious}
    {Baseline : FiniteObject.{uVertex} -> Prop}
    {BranchState : FiniteObject.{uVertex} -> Type uBranch}
    {Target : FiniteObject.{uVertex} -> Prop}
    {Admissible : (object : FiniteObject.{uVertex}) ->
      BranchState object -> object.graph.edgeSet -> Prop}
    {capability : _root_.Hypostructure.CT2.Capability Target
      (lexicographicProgress Baseline BranchState)
      (edgeDeletionSpec Baseline BranchState Admissible Previous)}
    (result : _root_.Hypostructure.CT2.ExecutionResult capability) :
    Not (Admissible
      (capability.contextAt result.stage.previous).G
      (capability.contextAt result.stage.previous).state
      (capability.selectedPiece result.stage.previous)) :=
  result.notAdmissible_of_proper trivial

end Hypostructure.Graph.CT2
