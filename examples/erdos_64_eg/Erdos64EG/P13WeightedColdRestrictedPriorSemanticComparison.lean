import Erdos64EG.P13WeightedColdRestrictedStructuralRepeatedPair
import StructuralExhaustion.Graph.FiniteTwoBoundaryPieceResponse

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

abbrev TwoBoundary := ULift.{u} (Fin 2)

@[implicit_reducible] noncomputable def twoBoundaryEnumeration :
    FinEnum TwoBoundary := inferInstance

/-- The ready two-piece comparison together with equality of the paper's
actual finite structural cut-state.  In particular this does not use the old
coarse code, whose connector length and terminal-successor degree are not the
state repeated by F5. -/
structure MatchedPriorPiecePair {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (stage prior : package.Stage) where
  pieces : package.PriorPiecePair stage prior
  structuralEqual : package.coldStructuralStateCode survivor prior =
    package.coldStructuralStateCode survivor stage

/-- Direct F5 handoff from one Core repetition.  Positive-stage membership,
strict order, and structural equality all come from that same repetition. -/
noncomputable def repeatedMatchedPriorPiecePair
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated) :
    package.MatchedPriorPiecePair survivor
      repetition.second repetition.first :=
  ⟨package.repeatedPriorPiecePair survivor repetition,
    package.repeated_equal_structural_code survivor repetition⟩

namespace MatchedPriorPiecePair

variable {package : P13WeightedColdRestrictedPrefixPackage ctx node21}
variable {ledger : package.PriorD6Ledger}
variable {survivor : package.LocalCorridorSurvivor ledger}
variable {stage prior : package.Stage}
variable (pair : package.MatchedPriorPiecePair survivor stage prior)

theorem boundaryDegree_eq
    (pair : package.MatchedPriorPiecePair survivor stage prior) :
  package.activeBoundaryDegree prior =
      package.activeBoundaryDegree stage :=
  congrArg (fun state : ColdStructuralStateCode => state.boundaryDegree)
    (MatchedPriorPiecePair.structuralEqual pair)

theorem activeHalfEdge_eq
    (pair : package.MatchedPriorPiecePair survivor stage prior) :
  package.activeHalfEdgeEndpointRole prior =
      package.activeHalfEdgeEndpointRole stage :=
  congrArg (fun state : ColdStructuralStateCode => state.activeHalfEdge)
    (MatchedPriorPiecePair.structuralEqual pair)

theorem windowOffset_eq
    (pair : package.MatchedPriorPiecePair survivor stage prior) :
    package.activeWindowOffset = package.activeWindowOffset :=
  congrArg (fun state : ColdStructuralStateCode => state.windowOffset)
    (MatchedPriorPiecePair.structuralEqual pair)

noncomputable abbrev EarlierPiece := pair.pieces.earlier.toBoundariedPiece
noncomputable abbrev CurrentPiece := pair.pieces.current.toBoundariedPiece

/-- Literal F2 witness.  The context is proof-selected from the negation of
universal equality; no context family is generated or scanned. -/
structure F2Distinction where
  outside : Context TwoBoundary
  differs : ¬(PackedTarget
      (glue twoBoundaryEnumeration pair.EarlierPiece outside) ↔
    PackedTarget
      (glue twoBoundaryEnumeration pair.CurrentPiece outside))

/-- Exact F2-negative certificate used by F3. -/
structure UniversalTargetEquality : Prop where
  equalInEveryContext : ∀ outside : Context TwoBoundary,
    PackedTarget
        (glue twoBoundaryEnumeration pair.EarlierPiece outside) ↔
      PackedTarget
        (glue twoBoundaryEnumeration pair.CurrentPiece outside)

inductive F2Outcome where
  | distinction (data : pair.F2Distinction)
  | universal (data : pair.UniversalTargetEquality)

/-- Quantifier-exact F2 split on the actual prior/current prefix pieces. -/
noncomputable def classifyF2 : pair.F2Outcome := by
  by_cases existsDistinction : ∃ outside : Context TwoBoundary,
      ¬(PackedTarget
          (glue twoBoundaryEnumeration pair.EarlierPiece outside) ↔
        PackedTarget
          (glue twoBoundaryEnumeration pair.CurrentPiece outside))
  · exact .distinction ⟨Classical.choose existsDistinction,
      Classical.choose_spec existsDistinction⟩
  · apply F2Outcome.universal
    refine ⟨?_⟩
    intro outside
    exact Classical.not_not.mp (by
      intro different
      exact existsDistinction ⟨outside, different⟩)

/-- A proof-carrying proposal for the paper's additional F3 requirement.
Universal target equality does not construct this datum.  It must contain the
actual atom decomposition, preserve the boundary-degree fibre, and certify a
strictly smaller admissible representative. -/
structure ProperRepresentativeProposal where
  atom : MinimumDegreeCycleReplacement.ProperAtom
    packedStaticInput twoBoundaryEnumeration ctx
  atomSource_eq : atom.source = pair.CurrentPiece
  replacement : Piece TwoBoundary
  replacement_eq : replacement = pair.EarlierPiece
  boundaryDegree_eq :
    MinimumDegreeCycleReplacement.BoundaryDegreeProfile
        twoBoundaryEnumeration replacement =
      MinimumDegreeCycleReplacement.BoundaryDegreeProfile
        twoBoundaryEnumeration atom.source
  internalTargetFree : ¬PackedTarget
    (Piece.pack twoBoundaryEnumeration replacement)
  internalBaseline : replacement.InternalBaseline
    twoBoundaryEnumeration packedStaticInput.minimumDegree
  locallySmaller : Piece.LexSmaller replacement atom.source

namespace ProperRepresentativeProposal

noncomputable def targetComplete
    (proposal : pair.ProperRepresentativeProposal)
    (universal : pair.UniversalTargetEquality) :
    MinimumDegreeCycleReplacement.TargetComplete packedStaticInput
      twoBoundaryEnumeration proposal.replacement
        proposal.atom.source := by
  refine ⟨proposal.boundaryDegree_eq, ?_⟩
  intro outside
  rw [proposal.replacement_eq, proposal.atomSource_eq]
  exact universal.equalInEveryContext outside

noncomputable def compression
    (proposal : pair.ProperRepresentativeProposal)
    (universal : pair.UniversalTargetEquality) :
    MinimumDegreeCycleReplacement.Compression packedStaticInput
      twoBoundaryEnumeration proposal.atom :=
  MinimumDegreeCycleReplacement.Compression.ofTargetComplete
    packedStaticInput twoBoundaryEnumeration proposal.replacement
      (proposal.targetComplete pair universal)
      proposal.internalTargetFree proposal.internalBaseline
      proposal.locallySmaller

end ProperRepresentativeProposal

structure F3 (universal : pair.UniversalTargetEquality) where
  proposal : pair.ProperRepresentativeProposal
  compression : MinimumDegreeCycleReplacement.Compression packedStaticInput
    twoBoundaryEnumeration proposal.atom
  compressionExact : compression = proposal.compression pair universal

structure F3Negative : Prop where
  noProperRepresentative : ¬Nonempty pair.ProperRepresentativeProposal

inductive F3Outcome (universal : pair.UniversalTargetEquality) where
  | compression (data : pair.F3 universal)
  | negative (data : pair.F3Negative)

/-- F3 is tested only after the exact F2-negative certificate.  Absence of a
proper representative is retained as the F3-negative input to F4/F5. -/
noncomputable def classifyF3 (universal : pair.UniversalTargetEquality) :
    pair.F3Outcome universal := by
  by_cases existsProposal : Nonempty pair.ProperRepresentativeProposal
  · let proposal := Classical.choice existsProposal
    exact .compression ⟨proposal, proposal.compression pair universal, rfl⟩
  · exact .negative ⟨existsProposal⟩

theorem f3_closes (universal : pair.UniversalTargetEquality)
    (data : pair.F3 universal) : False :=
  data.compression.impossible

end MatchedPriorPiecePair

end P13WeightedColdRestrictedPrefixPackage

end Erdos64EG.Internal
