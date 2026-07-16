import StructuralExhaustion.Core.FiniteObservedReconstruction
import StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger

namespace StructuralExhaustion.Graph.InducedPathComponentD4D7OrCoarseRepeat

open StructuralExhaustion
open InducedPathColdSkeleton
open InducedPathComponentD1D3Observation

universe u

variable {V : Type u} {object : FiniteObject V}

/-!
# D4--D7 reconstruction or coarse-repeat consumer

This module consumes an exact result of the cyclic D1--D3 ledger.  It does not
invent D4--D7 semantics or turn equality of coarse states into CT8 response
equivalence.  The repeated side exposes a CT10/refinement residual.  On the
bounded side a reusable complete-or-first-missing classifier scans only the
actual stored rows.  Since no graph-derived D4--D7 producer exists yet, the
current graph derivation honestly stops at the first row's typed marker.
-/

variable
  (input : InducedPathComponentD1D3Ledger.Input object)
  (anchorState : InducedPathComponentD1D3Ledger.State)
  (LengthOK : Nat → Prop)
  (lengthOKDecidable : DecidablePred LengthOK)

structure Source where
  node174 : InducedPathComponentD1D3Ledger.Result input anchorState
    LengthOK lengthOKDecidable
  node174Exact : node174 = InducedPathComponentD1D3Ledger.run input
    anchorState LengthOK lengthOKDecidable

noncomputable def computedSource :
    Source input anchorState LengthOK lengthOKDecidable where
  node174 := InducedPathComponentD1D3Ledger.run input anchorState LengthOK
    lengthOKDecidable
  node174Exact := rfl

structure CoarseRepeatResidual where
  repetition : InducedPathComponentD1D3Ledger.Repetition input anchorState
    LengthOK lengthOKDecidable
  firstAnchorDecision : Decidable
    (repetition.collision.first.1.1 = input.base.anchor)
  secondAnchorDecision : Decidable
    (repetition.collision.second.1.1 = input.base.anchor)

namespace CoarseRepeatResidual

variable {input anchorState LengthOK lengthOKDecidable}

theorem distinct (residual : CoarseRepeatResidual input anchorState LengthOK
    lengthOKDecidable) :
    residual.repetition.collision.first.1 ≠
      residual.repetition.collision.second.1 := residual.repetition.distinct

theorem sameCoarseState
    (residual : CoarseRepeatResidual input anchorState LengthOK
      lengthOKDecidable) :
    residual.repetition.collision.first.2 =
      residual.repetition.collision.second.2 := residual.repetition.sameState

theorem firstMissingD4D7
    (residual : CoarseRepeatResidual input anchorState LengthOK
      lengthOKDecidable) :
    Nonempty (TwoStubComponent.MissingD4D7Reconstruction
      (data residual.repetition.firstInput) residual.repetition.firstPath) :=
  residual.repetition.first_missing_d4_d7

theorem secondMissingD4D7
    (residual : CoarseRepeatResidual input anchorState LengthOK
      lengthOKDecidable) :
    Nonempty (TwoStubComponent.MissingD4D7Reconstruction
      (data residual.repetition.secondInput) residual.repetition.secondPath) :=
  residual.repetition.second_missing_d4_d7

end CoarseRepeatResidual

/-- Proposition marking that the authored graph clauses have derived complete
D4--D7 semantics for this connector.  It deliberately has no constructor in
the present graph layer.  This is a derivation-status proposition, not a claim
that mathematical semantics cannot exist. -/
inductive D4D7ClausesDerived
    (_stub : InducedPathComponentD1D3Ledger.Stub input) : Prop

def deriveReconstruction
    (stub : InducedPathComponentD1D3Ledger.Stub input) :
    Decidable (D4D7ClausesDerived input stub) :=
  isFalse fun derived => nomatch derived

def reconstructionSystem : Core.FiniteObservedReconstruction.System
    (InducedPathComponentD1D3Ledger.Stub input) where
  Reconstruction := D4D7ClausesDerived input
  derive := deriveReconstruction input

abbrev ReconstructedFamily :=
  (reconstructionSystem input).ReconstructedFamily
    (InducedPathComponentD1D3Ledger.stubs input)

/-- First exact observed row at which graph-derived semantics are unavailable.
The connector and missing marker are recovered from `row`. -/
structure FirstMissingReconstruction where
  scan : (reconstructionSystem input).FirstMissing
    (InducedPathComponentD1D3Ledger.stubs input)
  marker : Nonempty (TwoStubComponent.MissingD4D7Reconstruction
    (data (InducedPathComponentD1D3Ledger.connectorInput input scan.row))
    (canonicalPath
      (InducedPathComponentD1D3Ledger.connectorInput input scan.row)))

structure BoundedResidual where
  codesNodup :
    ((InducedPathComponentD1D3Ledger.rows input anchorState LengthOK
      lengthOKDecidable).map Prod.snd).Nodup
  lengthLe :
    (InducedPathComponentBoundarySchedule.incidentStubs input.base).length ≤
      Fintype.card InducedPathComponentD1D3Ledger.State

inductive Result where
  | coarseRepeat (residual : CoarseRepeatResidual input anchorState LengthOK
      lengthOKDecidable)
  | boundedReconstructed (bounded : BoundedResidual input anchorState LengthOK
      lengthOKDecidable) (family : ReconstructedFamily input)
  | boundedFirstMissing (bounded : BoundedResidual input anchorState LengthOK
      lengthOKDecidable) (residual : FirstMissingReconstruction input)

noncomputable def classifyBounded
    (bounded : BoundedResidual input anchorState LengthOK lengthOKDecidable) :
    Result input anchorState LengthOK lengthOKDecidable :=
  match (reconstructionSystem input).classify
      (InducedPathComponentD1D3Ledger.stubs input) with
  | .complete family => .boundedReconstructed bounded family
  | .firstMissing residual =>
      .boundedFirstMissing bounded {
        scan := residual
        marker := InducedPathComponentD1D3Ledger.observation_missing_d4_d7
          input LengthOK lengthOKDecidable residual.row
      }

noncomputable def run
    (source : Source input anchorState LengthOK lengthOKDecidable) :
    Result input anchorState LengthOK lengthOKDecidable := by
  classical
  cases source.node174 with
  | repeated repetition =>
      exact .coarseRepeat {
        repetition := repetition
        firstAnchorDecision := Classical.propDecidable _
        secondAnchorDecision := Classical.propDecidable _
      }
  | bounded codesNodup lengthLe =>
      let bounded : BoundedResidual input anchorState LengthOK
          lengthOKDecidable := ⟨codesNodup, lengthLe⟩
      exact classifyBounded input anchorState LengthOK lengthOKDecidable bounded

theorem source_exact
    (source : Source input anchorState LengthOK lengthOKDecidable) :
    source.node174 = InducedPathComponentD1D3Ledger.run input anchorState
      LengthOK lengthOKDecidable := source.node174Exact

theorem run_exhaustive
    (source : Source input anchorState LengthOK lengthOKDecidable) :
    (∃ residual, run input anchorState LengthOK lengthOKDecidable source =
        .coarseRepeat residual) ∨
      (∃ bounded family,
        run input anchorState LengthOK lengthOKDecidable source =
          .boundedReconstructed bounded family) ∨
      (∃ bounded residual,
        run input anchorState LengthOK lengthOKDecidable source =
          .boundedFirstMissing bounded residual) := by
  cases equation : run input anchorState LengthOK lengthOKDecidable source with
  | coarseRepeat residual => exact Or.inl ⟨residual, rfl⟩
  | boundedReconstructed bounded family =>
      exact Or.inr (Or.inl ⟨bounded, family, rfl⟩)
  | boundedFirstMissing bounded residual =>
      exact Or.inr (Or.inr ⟨bounded, residual, rfl⟩)

/-- The upper ledger is one classifier visit per actual stored row.  The
current missing derivation stops on its first visit. -/
noncomputable def visibleChecks : Nat :=
  (InducedPathComponentD1D3Ledger.stubs input).length

theorem visibleChecks_polynomial :
    visibleChecks input ≤
      InducedPathComponentD1D3Ledger.localScale input := by
  unfold visibleChecks InducedPathComponentD1D3Ledger.localScale
  omega

end StructuralExhaustion.Graph.InducedPathComponentD4D7OrCoarseRepeat
