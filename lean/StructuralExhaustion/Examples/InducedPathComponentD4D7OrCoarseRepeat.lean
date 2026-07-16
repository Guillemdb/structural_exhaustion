import StructuralExhaustion.Examples.InducedPathComponentD1D3Ledger
import StructuralExhaustion.Graph.InducedPathComponentD4D7OrCoarseRepeat
import StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10

namespace StructuralExhaustion.Examples.ComponentD4D7OrCoarseRepeat

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u uAmbient uBranch

variable {V : Type u} {object : FiniteObject V}
variable {P : Core.Problem.{uAmbient, uBranch}}

/-! Theorem-independent transfer of the exact node-175 branch consumer. -/

variable (source : ComponentD1D3Ledger.Source object)
variable (LengthOK : Nat → Prop)
variable (lengthOKDecidable : DecidablePred LengthOK)

noncomputable def input : InducedPathComponentD4D7OrCoarseRepeat.Source source.input
    (source.anchorState LengthOK lengthOKDecidable) LengthOK
    lengthOKDecidable where
  node174 := source.result LengthOK lengthOKDecidable
  node174Exact := rfl

noncomputable def result := InducedPathComponentD4D7OrCoarseRepeat.run source.input
  (source.anchorState LengthOK lengthOKDecidable) LengthOK
  lengthOKDecidable (input source LengthOK lengthOKDecidable)

theorem result_exhaustive :
    (∃ residual, result source LengthOK lengthOKDecidable =
        .coarseRepeat residual) ∨
      (∃ bounded family, result source LengthOK lengthOKDecidable =
        .boundedReconstructed bounded family) ∨
      (∃ bounded residual, result source LengthOK lengthOKDecidable =
        .boundedFirstMissing bounded residual) :=
  InducedPathComponentD4D7OrCoarseRepeat.run_exhaustive source.input
    (source.anchorState LengthOK lengthOKDecidable) LengthOK
    lengthOKDecidable (input source LengthOK lengthOKDecidable)

theorem observed_rows_only :
    InducedPathComponentD4D7OrCoarseRepeat.visibleChecks source.input =
      (InducedPathComponentD1D3Ledger.stubs source.input).length := rfl

/-! Concrete Core executions cover both classifier terminals. -/

def completeSystem : Core.FiniteObservedReconstruction.System Bool where
  Reconstruction := fun _ => True
  derive := fun _ => isTrue trivial

def firstMissingSystem : Core.FiniteObservedReconstruction.System Bool where
  Reconstruction := fun row => row = false
  derive := fun row => inferInstance

example : ∃ family,
    completeSystem.classify [false, true] = .complete family := by
  exact ⟨_, rfl⟩

example : ∃ residual,
    firstMissingSystem.classify [false, true] = .firstMissing residual := by
  exact ⟨_, rfl⟩

example :
    match firstMissingSystem.classify [false, true] with
    | .complete _ => False
    | .firstMissing residual =>
        residual.priorRows = [false] ∧ residual.row = true := by
  exact ⟨rfl, rfl⟩

/-! Branch-specific graph fixtures consume explicit exact predecessor
executions; no Erdős declaration is imported. -/

section BranchFixtures

variable (graphInput : InducedPathComponentD1D3Ledger.Input object)
variable (anchor : InducedPathComponentD1D3Ledger.State)
variable (LengthOK : Nat → Prop)
variable (lengthOKDecidable : DecidablePred LengthOK)

def repeatedSource
    (repetition : InducedPathComponentD1D3Ledger.Repetition graphInput anchor
      LengthOK lengthOKDecidable)
    (exactRun : InducedPathComponentD1D3Ledger.run graphInput anchor LengthOK
      lengthOKDecidable = .repeated repetition) :
    InducedPathComponentD4D7OrCoarseRepeat.Source graphInput anchor LengthOK
      lengthOKDecidable where
  node174 := .repeated repetition
  node174Exact := exactRun.symm

theorem repeated_fixture_executes
    (repetition : InducedPathComponentD1D3Ledger.Repetition graphInput anchor
      LengthOK lengthOKDecidable)
    (exactRun : InducedPathComponentD1D3Ledger.run graphInput anchor LengthOK
      lengthOKDecidable = .repeated repetition) :
    ∃ residual,
      InducedPathComponentD4D7OrCoarseRepeat.run graphInput anchor LengthOK
        lengthOKDecidable
          (repeatedSource graphInput anchor LengthOK lengthOKDecidable
            repetition exactRun) = .coarseRepeat residual := by
  exact ⟨_, rfl⟩

noncomputable def routedRepeatResidual
    (repetition : InducedPathComponentD1D3Ledger.Repetition graphInput anchor
      LengthOK lengthOKDecidable) :
    InducedPathComponentD4D7OrCoarseRepeat.CoarseRepeatResidual graphInput
      anchor LengthOK lengthOKDecidable where
  repetition := repetition
  firstAnchorDecision := Classical.propDecidable _
  secondAnchorDecision := Classical.propDecidable _

theorem repeated_fixture_routes_to_ct10
    (ctx : Core.BranchContext P)
    (repetition : InducedPathComponentD1D3Ledger.Repetition graphInput anchor
      LengthOK lengthOKDecidable) :
    (Routes.InducedPathComponentD4D7ToCT10.coarseExecution P ctx
      (routedRepeatResidual graphInput anchor LengthOK lengthOKDecidable
        repetition)).outcome.Valid :=
  Routes.InducedPathComponentD4D7ToCT10.coarse_valid ctx _

theorem repeated_fixture_ct10_promotes
    (ctx : Core.BranchContext P)
    (repetition : InducedPathComponentD1D3Ledger.Repetition graphInput anchor
      LengthOK lengthOKDecidable) :
    (Routes.InducedPathComponentD4D7ToCT10.coarseExecution P ctx
      (routedRepeatResidual graphInput anchor LengthOK lengthOKDecidable
        repetition)).terminal = .promoted :=
  Routes.InducedPathComponentD4D7ToCT10.coarse_terminal_promoted ctx _

def boundedSource
    (codesNodup : ((InducedPathComponentD1D3Ledger.rows graphInput anchor
      LengthOK lengthOKDecidable).map Prod.snd).Nodup)
    (lengthLe :
      (InducedPathComponentBoundarySchedule.incidentStubs graphInput.base).length ≤
        Fintype.card InducedPathComponentD1D3Ledger.State)
    (exactRun : InducedPathComponentD1D3Ledger.run graphInput anchor LengthOK
      lengthOKDecidable = .bounded codesNodup lengthLe) :
    InducedPathComponentD4D7OrCoarseRepeat.Source graphInput anchor LengthOK
      lengthOKDecidable where
  node174 := .bounded codesNodup lengthLe
  node174Exact := exactRun.symm

set_option maxHeartbeats 800000 in
theorem bounded_fixture_preserves_predecessor
    (codesNodup : ((InducedPathComponentD1D3Ledger.rows graphInput anchor
      LengthOK lengthOKDecidable).map Prod.snd).Nodup)
    (lengthLe :
      (InducedPathComponentBoundarySchedule.incidentStubs graphInput.base).length ≤
        Fintype.card InducedPathComponentD1D3Ledger.State)
    (exactRun : InducedPathComponentD1D3Ledger.run graphInput anchor LengthOK
      lengthOKDecidable = .bounded codesNodup lengthLe)
    (scanResidual :
      (InducedPathComponentD4D7OrCoarseRepeat.reconstructionSystem graphInput
        ).FirstMissing (InducedPathComponentD1D3Ledger.stubs graphInput))
    (scanExact :
      (InducedPathComponentD4D7OrCoarseRepeat.reconstructionSystem graphInput
        ).classify (InducedPathComponentD1D3Ledger.stubs graphInput) =
          .firstMissing scanResidual) :
    ∃ bounded missing,
      InducedPathComponentD4D7OrCoarseRepeat.run graphInput anchor LengthOK
        lengthOKDecidable
          (boundedSource graphInput anchor LengthOK lengthOKDecidable
            codesNodup lengthLe exactRun) =
            .boundedFirstMissing bounded missing ∧
      bounded.codesNodup = codesNodup ∧ bounded.lengthLe = lengthLe := by
  let bounded :
      InducedPathComponentD4D7OrCoarseRepeat.BoundedResidual graphInput
        anchor LengthOK lengthOKDecidable := ⟨codesNodup, lengthLe⟩
  let missing :
      InducedPathComponentD4D7OrCoarseRepeat.FirstMissingReconstruction
        graphInput := {
    scan := scanResidual
    marker := InducedPathComponentD1D3Ledger.observation_missing_d4_d7
      graphInput LengthOK lengthOKDecidable scanResidual.row
  }
  refine ⟨bounded, missing, ?_, rfl, rfl⟩
  unfold InducedPathComponentD4D7OrCoarseRepeat.run
  dsimp [boundedSource]
  unfold InducedPathComponentD4D7OrCoarseRepeat.classifyBounded
  rw [scanExact]

theorem bounded_first_missing_routes_to_ct10
    (ctx : Core.BranchContext P)
    (residual :
      InducedPathComponentD4D7OrCoarseRepeat.FirstMissingReconstruction
        graphInput) :
    Nonempty (CT10.ExecutionResult
      (Routes.InducedPathComponentD4D7ToCT10.missingCapability P residual)
      (Routes.InducedPathComponentD4D7ToCT10.missingInput P ctx residual)) :=
  ⟨Routes.InducedPathComponentD4D7ToCT10.missingExecution P ctx residual⟩

end BranchFixtures

end StructuralExhaustion.Examples.ComponentD4D7OrCoarseRepeat
