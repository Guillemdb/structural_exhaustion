import Hypostructure.CT2.Spec
import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Query

/-!
# CT2 local-deletion capability

Both the finite piece carrier and its selected index are queried from the
literal predecessor.  The framework never enumerates an ambient object type
and an application never passes a selected piece directly to the executor.
-/

namespace Hypostructure.CT2

universe uAmbient uBranch uMeasure uPrevious uPiece

/-- Minimal executable surface for one residual-selected local deletion. -/
structure Capability
    {P : Core.Problem.{uAmbient, uBranch}}
    (Target : P.Ambient -> Prop)
    (progress : Core.Progress.{uAmbient, uBranch, uMeasure} P)
    (spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous) where
  context : Core.Residual.Query Previous fun _previous =>
    Core.MinimalCounterexampleContext P Target progress
  pieces : Core.Residual.Query Previous fun previous =>
    Core.Finite.Enumeration (spec.Piece (context.read previous).G)
  selectedIndex : Core.Residual.Query Previous fun previous =>
    Fin (pieces.read previous).card
  properDecidable : {object : P.Ambient} ->
    (piece : spec.Piece object) -> Decidable (spec.Proper piece)
  admissibleDecidable : {object : P.Ambient} ->
    (state : P.BranchState object) -> (piece : spec.Piece object) ->
      Decidable (spec.Admissible state piece)
  decreases : {object : P.Ambient} ->
    (state : P.BranchState object) -> (piece : spec.Piece object) ->
    spec.Proper piece -> spec.Admissible state piece ->
      progress.Smaller (spec.delete piece) object
  preservesBaseline : {object : P.Ambient} ->
    (state : P.BranchState object) -> (piece : spec.Piece object) ->
    spec.Proper piece -> spec.Admissible state piece -> P.Baseline object ->
      P.Baseline (spec.delete piece)
  targetMonotone : {object : P.Ambient} ->
    (state : P.BranchState object) -> (piece : spec.Piece object) ->
    spec.Proper piece -> spec.Admissible state piece -> P.Baseline object ->
    Target (spec.delete piece) -> Target object

namespace Capability

/-- The inherited minimal-counterexample context at this exact predecessor. -/
def contextAt
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    (capability : Capability Target progress spec) (previous : Previous) :
    Core.MinimalCounterexampleContext P Target progress :=
  capability.context.read previous

/-- The exact finite piece carrier retrieved from the predecessor ledger. -/
def piecesAt
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    (capability : Capability Target progress spec) (previous : Previous) :
    Core.Finite.Enumeration
      (spec.Piece (capability.contextAt previous).G) :=
  capability.pieces.read previous

/-- Framework-owned selection by the residual-owned bounded index. -/
def selectedPiece
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    (capability : Capability Target progress spec) (previous : Previous) :
    spec.Piece (capability.contextAt previous).G :=
  (capability.piecesAt previous).get
    (capability.selectedIndex.read previous)

/-- Exact local predicate decided by the CT2 executor. -/
def Eligible
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    (capability : Capability Target progress spec) (previous : Previous) : Prop :=
  spec.Proper (capability.selectedPiece previous) ∧
    spec.Admissible (capability.contextAt previous).state
      (capability.selectedPiece previous)

/-- Eligibility is decided from the two primitive local deciders. -/
def eligibleDecidable
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    (capability : Capability Target progress spec) (previous : Previous) :
    Decidable (capability.Eligible previous) :=
  @instDecidableAnd _ _
    (capability.properDecidable (capability.selectedPiece previous))
    (capability.admissibleDecidable (capability.contextAt previous).state
      (capability.selectedPiece previous))

/-- The selected piece is definitionally a member of the inherited carrier. -/
theorem selectedPiece_mem
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    (capability : Capability Target progress spec) (previous : Previous) :
    capability.selectedPiece previous ∈
      (capability.piecesAt previous).values :=
  (capability.piecesAt previous).get_mem
    (capability.selectedIndex.read previous)

/-- One explicit local decision has a constant degree-zero work budget. -/
def localDeletionBudget
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    (capability : Capability Target progress spec) :
    Core.PolynomialCheckBudget Previous :=
  Core.PolynomialCheckBudget.constant
    (fun previous => (capability.piecesAt previous).card) 1

end Capability

end Hypostructure.CT2
