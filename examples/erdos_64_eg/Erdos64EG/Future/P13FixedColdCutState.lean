import Erdos64EG.InternalProblem
import StructuralExhaustion.Core.FixedTwoBoundaryCutState

namespace Erdos64EG.P13FixedColdCutState

open StructuralExhaustion.Core.FixedTwoBoundaryCutState
open Erdos64EG.Internal

universe uPrefix uCoordinate uContext

/-!
# P13 specialization of the fixed two-boundary state

The connector length is observed only through the thirteen power-of-two
tests.  D4--D7 enter through the fixed finite `LocalCoordinate` alphabet and
its graph-derived projection.  This code is a corridor repetition invariant,
not by itself a CT3 target-compression table.
-/

structure Projection (Prefix : Type uPrefix)
    (LocalCoordinate : Type uCoordinate) where
  observations : PrefixObservations Prefix
  declaredLocal : LocalProjection Prefix LocalCoordinate

def Projection.code {Prefix : Type uPrefix}
    {LocalCoordinate : Type uCoordinate}
    (projection : Projection Prefix LocalCoordinate) (segment : Prefix) :
    State LocalCoordinate :=
  project PowerOfTwoLength powerOfTwoLengthDecidable
    projection.observations projection.declaredLocal segment

theorem Projection.targetResponse_true_iff
    {Prefix : Type uPrefix} {LocalCoordinate : Type uCoordinate}
    (projection : Projection Prefix LocalCoordinate) (segment : Prefix)
    (offset : Fin 13) :
    (projection.code segment).targetResponse offset = true ↔
      PowerOfTwoLength
        (projection.observations.connectorLength segment + offset.val) := by
  exact targetOffsetResponse_eq_true_iff PowerOfTwoLength
    powerOfTwoLengthDecidable
    (projection.observations.connectorLength segment) offset

theorem code_card (LocalCoordinate : Type uCoordinate)
    [Fintype LocalCoordinate] :
    Fintype.card (State LocalCoordinate) =
      4 ^ 2 * 13 ^ 2 * 2 ^ 13 * 2 ^ Fintype.card LocalCoordinate :=
  state_card LocalCoordinate

abbrev F2Distinction {Prefix : Type uPrefix} (Context : Type uContext)
    (response : Prefix → Context → Bool) (left right : Prefix) :=
  TargetResponseDistinction Prefix Context response left right

/-- Exact P13 both-sides comparison.  A distinction is retained as F2.  The
other branch proves equivalence only over the supplied compatible-context
type and for this pair; it is not an all-context theorem inferred from the
coarse code. -/
def Projection.compare
    {Prefix : Type uPrefix} {LocalCoordinate : Type uCoordinate}
    (projection : Projection Prefix LocalCoordinate)
    (Context : Type uContext) (response : Prefix → Context → Bool)
    (left right : Prefix)
    (contextComparison : PairContextComparison Prefix Context response left right)
    (equalCode : projection.code left = projection.code right) :
    EqualCodeComparison projection.declaredLocal Context response left right :=
  compareEqualCodes PowerOfTwoLength powerOfTwoLengthDecidable
    projection.observations projection.declaredLocal Context response
    left right contextComparison equalCode

end Erdos64EG.P13FixedColdCutState
