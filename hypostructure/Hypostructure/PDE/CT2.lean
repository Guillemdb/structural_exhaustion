import Hypostructure.CT2.Automation
import Hypostructure.PDE.Model

/-!
# PDE specialization of CT2

The PDE application supplies a local piece carrier, admissibility, deletion,
and the analytic preservation/progress laws.  CT2 still selects the piece
from the incoming residual and owns the executable eligibility decision.
-/

namespace Hypostructure.PDE.CT2

universe uPrevious uModel uBranch uMeasure uPiece

open Hypostructure

def localDeletionSpec {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (Piece : M.problem.Ambient -> Type uPiece)
    (Proper : {object : M.problem.Ambient} -> Piece object -> Prop)
    (Admissible : {object : M.problem.Ambient} ->
      M.problem.BranchState object -> Piece object -> Prop)
    (delete : {object : M.problem.Ambient} -> Piece object ->
      M.problem.Ambient) :
    _root_.Hypostructure.CT2.Spec M.problem Previous where
  Piece := Piece
  Proper := Proper
  Admissible := Admissible
  delete := delete

def capability {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (Target : M.problem.Ambient -> Prop)
    (progress : Core.Progress M.problem)
    (Piece : M.problem.Ambient -> Type uPiece)
    (Proper : {object : M.problem.Ambient} -> Piece object -> Prop)
    (Admissible : {object : M.problem.Ambient} ->
      M.problem.BranchState object -> Piece object -> Prop)
    (delete : {object : M.problem.Ambient} -> Piece object ->
      M.problem.Ambient)
    (context : Core.Residual.Query Previous fun _previous =>
      Core.MinimalCounterexampleContext M.problem Target progress)
    (pieces : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (Piece (context.read previous).G))
    (selectedIndex : Core.Residual.Query Previous fun previous =>
      Fin (pieces.read previous).card)
    (properDecidable : {object : M.problem.Ambient} ->
      (piece : Piece object) -> Decidable (Proper piece))
    (admissibleDecidable : {object : M.problem.Ambient} ->
      (state : M.problem.BranchState object) -> (piece : Piece object) ->
      Decidable (Admissible state piece))
    (decreases : {object : M.problem.Ambient} ->
      (state : M.problem.BranchState object) -> (piece : Piece object) ->
      Proper piece -> Admissible state piece ->
      progress.Smaller (delete piece) object)
    (preservesBaseline : {object : M.problem.Ambient} ->
      (state : M.problem.BranchState object) -> (piece : Piece object) ->
      Proper piece -> Admissible state piece -> M.problem.Baseline object ->
      M.problem.Baseline (delete piece))
    (targetMonotone : {object : M.problem.Ambient} ->
      (state : M.problem.BranchState object) -> (piece : Piece object) ->
      Proper piece -> Admissible state piece -> M.problem.Baseline object ->
      Target (delete piece) -> Target object) :
    _root_.Hypostructure.CT2.Capability (Previous := Previous) Target progress
      (localDeletionSpec (Previous := Previous) M Piece Proper Admissible delete) where
  context := context
  pieces := pieces
  selectedIndex := selectedIndex
  properDecidable := properDecidable
  admissibleDecidable := admissibleDecidable
  decreases := decreases
  preservesBaseline := preservesBaseline
  targetMonotone := targetMonotone

end Hypostructure.PDE.CT2
