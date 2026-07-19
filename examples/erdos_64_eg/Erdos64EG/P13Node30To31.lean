import Erdos64EG.P13Node29To30
import StructuralExhaustion.Core.ExactHandoff

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact existing edge `[30] -> [31]`

Node `[31]` defines the curvature target-rank of the literal raw wedge
coordinates.  Rank is the maximum size of a declared subfamily on which every
functional admissible quotient is label-injective.  The framework represents
that maximum without enumerating subfamilies, quotients, or outside contexts.
The CT15 rank-drop decision belongs to node `[32]`, not this file.
-/

/-- The manuscript's target rank on the union of all raw remainder wedges. -/
noncomputable def p13CurvatureTargetRank
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Nat :=
  p13CanonicalCurvatureTargetRank ctx

/-- Complete node-[31] payload indexed by the literal node-[30] output. -/
structure VerifiedP13Node31CurvatureTargetRank
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21)
    (node26 : VerifiedP13Node26RemainderContinuation ctx node21 node24)
    (node27 : VerifiedP13Node27NoInternalThreeCore ctx node21 node24 node26)
    (node28 : VerifiedP13Node28PositiveDeficiency
      ctx node21 node24 node26 node27)
    (node29 : VerifiedP13Node29ExternalIncidenceSupply
      ctx node21 node24 node26 node27 node28)
    (node30 : VerifiedP13Node30WedgeLower
      ctx node21 node24 node26 node27 node28 node29) : Type (u + 3)
    extends Core.ExactHandoff node30 where
  coordinateCount :
    (p13CurvatureCoordinates ctx).card =
      (p13RemainderCurvatureProfile ctx).wedgeCount
  coordinateCubic :
    (p13CurvatureCoordinates ctx).card ≤ ctx.G.object.input.vertices.card ^ 3
  responseExact : ∀ coordinate outside,
    (p13CurvatureResponseProfile ctx).responseSystem.response coordinate outside = true ↔
      packedStaticInput.Target
        (Graph.PackedBoundariedGluing.glue ctx.G.object.input.vertices
          ((p13CurvatureResponseProfile ctx).coordinatePiece coordinate) outside)
  targetRankUpper :
    p13CurvatureTargetRank ctx ≤
      (p13RemainderCurvatureProfile ctx).wedgeCount
  maximumWitness :
    ∃ family : Finset (P13CurvatureCoordinate ctx),
      (p13CurvatureFunctionalRankProfile ctx).Survives family ∧
        family.card = p13CurvatureTargetRank ctx

/-- Execute only the manuscript's definitional `[30] -> [31]` edge. -/
noncomputable def VerifiedP13Node30WedgeLower.node31
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21}
    {node26 : VerifiedP13Node26RemainderContinuation ctx node21 node24}
    {node27 : VerifiedP13Node27NoInternalThreeCore ctx node21 node24 node26}
    {node28 : VerifiedP13Node28PositiveDeficiency
      ctx node21 node24 node26 node27}
    {node29 : VerifiedP13Node29ExternalIncidenceSupply
      ctx node21 node24 node26 node27 node28}
    (node30 : VerifiedP13Node30WedgeLower
      ctx node21 node24 node26 node27 node28 node29) :
    VerifiedP13Node31CurvatureTargetRank
      ctx node21 node24 node26 node27 node28 node29 node30 where
  previous := node30
  previousExact := rfl
  coordinateCount := p13CurvatureCoordinates_card_eq_wedgeCount ctx
  coordinateCubic := p13CurvatureCoordinates_card_le_cube ctx
  responseExact := (p13CurvatureResponseProfile ctx).response_true_iff
  targetRankUpper := by
    calc
      p13CurvatureTargetRank ctx ≤ (p13CurvatureCoordinates ctx).card :=
        (p13CurvatureFunctionalRankProfile ctx).rankProfile.targetRank_le_coordinates
      _ = (p13RemainderCurvatureProfile ctx).wedgeCount :=
        p13CurvatureCoordinates_card_eq_wedgeCount ctx
  maximumWitness :=
    exists_p13CanonicalCurvature_surviving_card_eq_targetRank ctx

end Erdos64EG.Internal
