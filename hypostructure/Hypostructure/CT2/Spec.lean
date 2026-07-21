import Hypostructure.Core.Context

/-!
# CT2 local-deletion specification

The first Hypostructure CT2 profile handles one local piece already selected
by the incoming residual.  The specification records only the primitive
mathematics of pieces and deletion; schedules, selection, decisions, and
routing belong to the executable capability.
-/

namespace Hypostructure.CT2

universe uAmbient uBranch uPrevious uPiece

/-- Domain-neutral mathematics of deleting one local piece. -/
structure Spec (P : Core.Problem.{uAmbient, uBranch})
    (Previous : Type uPrevious) where
  Piece : P.Ambient -> Type uPiece
  Proper : {object : P.Ambient} -> Piece object -> Prop
  Admissible : {object : P.Ambient} ->
    P.BranchState object -> Piece object -> Prop
  delete : {object : P.Ambient} -> Piece object -> P.Ambient

end Hypostructure.CT2
