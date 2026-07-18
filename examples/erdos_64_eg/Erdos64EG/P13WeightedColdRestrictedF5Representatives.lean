import Erdos64EG.P13WeightedColdRestrictedColdGermFrontier
import StructuralExhaustion.Graph.FiniteSameInterfaceExchange

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.PackedBoundariedGluing

universe u

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

namespace P13WeightedColdRestrictedPrefixPackage

variable (package : P13WeightedColdRestrictedPrefixPackage ctx node21)

/-!
# Exact representative data derivable on the repeated F5 edge

The two prefix pieces already share the abstract `Fin 2` boundary label type.
This module records them without asserting that their distinct moving ambient
endpoints form one literal graph interface.  It also computes the exact signed
edge increment.  Full boundary-profile equality, atom reconstruction, and the
finite response reflection table remain separate producer obligations.
-/

noncomputable def repeatedRepresentatives
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated) :
    FiniteSameInterfaceExchange.Representatives (Piece TwoBoundary) :=
  let pair := package.repeatedMatchedPriorPiecePair survivor repetition
  FiniteSameInterfaceExchange.Representatives.exact
    pair.CurrentPiece pair.EarlierPiece
    (fun piece => @Piece.edgeCount TwoBoundary twoBoundaryEnumeration piece)

@[simp] theorem repeatedRepresentatives_source
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated) :
    (package.repeatedRepresentatives survivor repetition).source =
      (package.repeatedMatchedPriorPiecePair survivor repetition).CurrentPiece :=
  rfl

@[simp] theorem repeatedRepresentatives_replacement
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated) :
    (package.repeatedRepresentatives survivor repetition).replacement =
      (package.repeatedMatchedPriorPiecePair survivor repetition).EarlierPiece :=
  rfl

theorem repeatedRepresentatives_increment_exact
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated) :
    (package.repeatedRepresentatives survivor repetition).increment =
      Int.ofNat (@Piece.edgeCount TwoBoundary twoBoundaryEnumeration
        (package.repeatedMatchedPriorPiecePair survivor repetition).CurrentPiece) -
      Int.ofNat (@Piece.edgeCount TwoBoundary twoBoundaryEnumeration
        (package.repeatedMatchedPriorPiecePair survivor repetition).EarlierPiece) :=
  rfl

/-- The F2-negative certificate is exact universal target equality for the
same ordered replacement/source pair used by `repeatedRepresentatives`. -/
theorem repeatedRepresentatives_targetUniversal
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated)
    (universal :
      (package.repeatedMatchedPriorPiecePair survivor repetition).UniversalTargetEquality)
    (outside : Context TwoBoundary) :
    PackedTarget (glue twoBoundaryEnumeration
      (package.repeatedRepresentatives survivor repetition).replacement outside) ↔
    PackedTarget (glue twoBoundaryEnumeration
      (package.repeatedRepresentatives survivor repetition).source outside) :=
  universal.equalInEveryContext outside

/-- A fixed context witness used only to make the two-valued response decoder
total when one Boolean truth value is unrealized.  It has no internal vertices
and owns no edges. -/
noncomputable def emptyTwoBoundaryContext : Context (ULift.{u} (Fin 2)) where
  Internal := ULift.{u} Empty
  internalVertices := inferInstance
  graph := ⊥
  decideAdj := by infer_instance
  noBoundaryEdge := by simp

noncomputable local instance emptyTwoBoundaryContextNonempty :
    Nonempty (Context (ULift.{u} (Fin 2))) :=
  ⟨emptyTwoBoundaryContext⟩

/-- Exact finite response table obtained from the already-proved universal F2
certificate.  Its code schedule is `Bool`; decoding proof-selects a realizing
context for each realized truth value and never enumerates contexts. -/
noncomputable def repeatedResponseTable
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated)
    (universal :
      (package.repeatedMatchedPriorPiecePair survivor repetition).UniversalTargetEquality) :
    FiniteSameInterfaceExchange.ResponseTable
      (package.repeatedRepresentatives survivor repetition) := by
  let representatives := package.repeatedRepresentatives survivor repetition
  let replacementTarget := fun outside : Context (ULift.{u} (Fin 2)) =>
    PackedTarget (glue twoBoundaryEnumeration
      representatives.replacement outside)
  let sourceTarget := fun outside : Context (ULift.{u} (Fin 2)) =>
    PackedTarget (glue twoBoundaryEnumeration
      representatives.source outside)
  letI : DecidablePred replacementTarget := Classical.decPred _
  letI : DecidablePred sourceTarget := Classical.decPred _
  exact FiniteSameInterfaceExchange.ResponseTable.ofUniversal
    (Context (ULift.{u} (Fin 2))) replacementTarget sourceTarget
    (package.repeatedRepresentatives_targetUniversal survivor repetition universal)

end P13WeightedColdRestrictedPrefixPackage

end Erdos64EG.Internal
