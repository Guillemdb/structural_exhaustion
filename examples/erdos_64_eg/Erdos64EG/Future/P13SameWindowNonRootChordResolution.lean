import Erdos64EG.Shared.CT1
import Erdos64EG.Future.P13SameWindowShortThirdIncidence
import StructuralExhaustion.Graph.DeletedEdgeReturnChordResolution

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Node [165]: resolve the selected on-return third incidence

The input contains an equality proving that the exact node-`[162]` execution
returned its `nonRootChord` constructor.  The graph-owned resolver scans only
that supplied short return support.  An accepted chord is checked through the
existing CT1 certificate runner and contradicts target avoidance.  The only
surviving output retains the exact strictly shorter deleted-edge return.
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
variable {window : P13ActualSelectedWindow ctx}
variable {fork : P13ActualAttachmentColdFork ctx previous window}
variable {quiet : P13SameWindowQuietOutput fork}

/-- Proof-carrying exact node-`[162]` non-root-chord branch. -/
structure P13SameWindowComputedNonRootChord
    (short : P13SameWindowComputedShort fork quiet) where
  member : short.setup.third.hit.value ∈
    short.setup.returnPath.path.support
  runExact : runP13SameWindowShortThirdIncidence short =
    .nonRootChord member

namespace P13SameWindowComputedNonRootChord

variable {short : P13SameWindowComputedShort fork quiet}

/-- Thin generic input retaining the exact predecessor run equality. -/
noncomputable def genericInput
    (branch : P13SameWindowComputedNonRootChord short) :
    DeletedEdgeReturnChordResolution.Input short.setup where
  member := branch.member
  runExact := branch.runExact

/-- Existing proof-carrying CT1 run for an accepted local chord. -/
noncomputable def targetRun
    (branch : P13SameWindowComputedNonRootChord short)
    (certificate : CycleWithLength ctx.G.object.graph PowerOfTwoLength) :=
  runCT1 ctx.G.object ctx.baseline certificate

theorem target_terminal
    (branch : P13SameWindowComputedNonRootChord short)
    (certificate : CycleWithLength ctx.G.object.graph PowerOfTwoLength) :
    (branch.targetRun certificate).result.terminal = .c1 :=
  (branch.targetRun certificate).terminal_eq

theorem target_impossible
    (branch : P13SameWindowComputedNonRootChord short)
    (certificate : CycleWithLength ctx.G.object.graph PowerOfTwoLength) : False := by
  have _terminal := branch.target_terminal certificate
  exact ctx.avoids ⟨certificate⟩

end P13SameWindowComputedNonRootChord

variable {short : P13SameWindowComputedShort fork quiet}

/-- Exact surviving node-`[165]` residual.  It retains both the rejected
literal chord length and the graph-owned replacement return. -/
structure P13SameWindowShorterReturn
    (branch : P13SameWindowComputedNonRootChord short) where
  lengthRejected : ¬PowerOfTwoLength (branch.genericInput.index + 1)
  shorter : DartReturn ctx.G.object.graph quiet.stub.dart
  shorterExact : shorter = branch.genericInput.shorterReturn
  strict : shorter.path.length < short.setup.returnPath.path.length
  runExact : DeletedEdgeReturnChordResolution.run branch.genericInput
      PowerOfTwoLength powerOfTwoLengthDecidable =
    .rejected lengthRejected shorter shorterExact strict

/-- Execute the graph-owned local resolver.  The CT1 branch closes; the
rejected branch returns the exact strictly shorter return. -/
noncomputable def runP13SameWindowNonRootChordResolution
    (branch : P13SameWindowComputedNonRootChord short) :
    P13SameWindowShorterReturn branch := by
  generalize equation : DeletedEdgeReturnChordResolution.run
    branch.genericInput PowerOfTwoLength powerOfTwoLengthDecidable = result
  cases result with
  | target certificate => exact False.elim (branch.target_impossible certificate)
  | rejected lengthRejected shorter shorterExact strict =>
      exact {
        lengthRejected := lengthRejected
        shorter := shorter
        shorterExact := shorterExact
        strict := strict
        runExact := equation
      }

theorem runP13SameWindowNonRootChordResolution_shorterExact
    (branch : P13SameWindowComputedNonRootChord short) :
    (runP13SameWindowNonRootChordResolution branch).shorter =
      branch.genericInput.shorterReturn :=
  (runP13SameWindowNonRootChordResolution branch).shorterExact

theorem runP13SameWindowNonRootChordResolution_strict
    (branch : P13SameWindowComputedNonRootChord short) :
    (runP13SameWindowNonRootChordResolution branch).shorter.path.length <
      short.setup.returnPath.path.length :=
  (runP13SameWindowNonRootChordResolution branch).strict

/-- Exactly one bounded support scan and one supplied-length decision. -/
theorem p13SameWindowNonRootChordResolution_visibleChecks_le
    (branch : P13SameWindowComputedNonRootChord short) :
    DeletedEdgeReturnChordResolution.visibleChecks branch.genericInput ≤
      p13ColdD1D3BaseThreshold + 1 :=
  DeletedEdgeReturnChordResolution.visibleChecks_le branch.genericInput
    short.return_support_bounded

end Erdos64EG.Internal
