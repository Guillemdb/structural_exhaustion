import Hypostructure.CT2.Search

/-!
# CT2 accumulated execution

The sole stage extension is Core's selected-piece decision.  Terminal tags,
typed traces, and check counts are derived by CT2 and cannot be supplied by an
application.
-/

namespace Hypostructure.CT2

universe uAmbient uBranch uMeasure uPrevious uPiece

/-- Semantic terminals of the explicit local-deletion profile. -/
inductive Terminal where
  | deletionC2
  | criticality
  deriving DecidableEq, Repr

/-- Audit nodes of the complete local-deletion path. -/
inductive NodeId where
  | entry
  | residualSelection
  | eligibilityDecision
  | deletionDecision
  | deletionC2Terminal
  | criticalityTerminal
  deriving DecidableEq, Repr

/-- Terminal-indexed CT2 traces. -/
inductive Trace : Terminal -> Type where
  | deletionC2 : Trace .deletionC2
  | criticality : Trace .criticality

namespace Trace

/-- Observable node sequence of a typed CT2 trace. -/
def nodes : {terminal : Terminal} -> Trace terminal -> List NodeId
  | .deletionC2, .deletionC2 =>
      [.entry, .residualSelection, .eligibilityDecision,
        .deletionDecision, .deletionC2Terminal]
  | .criticality, .criticality =>
      [.entry, .residualSelection, .eligibilityDecision,
        .criticalityTerminal]

/-- Canonical node sequence fixed by a semantic terminal. -/
def expectedNodes : Terminal -> List NodeId
  | .deletionC2 =>
      [.entry, .residualSelection, .eligibilityDecision,
        .deletionDecision, .deletionC2Terminal]
  | .criticality =>
      [.entry, .residualSelection, .eligibilityDecision,
        .criticalityTerminal]

theorem nodes_eq_expected : {terminal : Terminal} ->
    (trace : Trace terminal) -> trace.nodes = expectedNodes terminal
  | .deletionC2, .deletionC2 => rfl
  | .criticality, .criticality => rfl

end Trace

/-- Core's decision constructor determines the CT2 terminal. -/
def terminalOfRoute
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    {capability : Capability Target progress spec}
    (routed : RoutedDecision capability) : Terminal :=
  match routed.added with
  | .yesBranch _ => .deletionC2
  | .noBranch _ => .criticality

/-- Construct the unique typed trace selected by Core's route. -/
def traceOfRoute
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    {capability : Capability Target progress spec}
    (routed : RoutedDecision capability) :
    Trace (terminalOfRoute routed) := by
  cases branch : routed.added with
  | yesBranch _ =>
      simpa [terminalOfRoute, branch] using Trace.deletionC2
  | noBranch _ =>
      simpa [terminalOfRoute, branch] using Trace.criticality

/-- CT2's accumulated stage is exactly Core's decision extension. -/
abbrev Stage
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    (capability : Capability Target progress spec) :=
  RoutedDecision capability

/-- Framework-generated CT2 execution. -/
structure ExecutionResult
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    (capability : Capability Target progress spec) where
  private mk ::
  stage : Stage capability
  trace : Trace (terminalOfRoute stage)
  checks : Nat
  checks_eq : checks =
    (capability.localDeletionBudget).checks stage.previous

namespace ExecutionResult

/-- Terminal derived from the stored Core route. -/
def terminal
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    {capability : Capability Target progress spec}
    (result : ExecutionResult capability) : Terminal :=
  terminalOfRoute result.stage

/-- Exact observable trace of the generated execution. -/
def traceNodes
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    {capability : Capability Target progress spec}
    (result : ExecutionResult capability) : List NodeId :=
  result.trace.nodes

/-- The local profile performs exactly one primitive eligibility decision. -/
theorem checks_eq_one
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    {capability : Capability Target progress spec}
    (result : ExecutionResult capability) : result.checks = 1 := by
  simpa [Capability.localDeletionBudget,
    Core.PolynomialCheckBudget.constant] using result.checks_eq

/-- Every execution satisfies the framework-owned constant work budget. -/
theorem checks_le_polynomial
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    {capability : Capability Target progress spec}
    (result : ExecutionResult capability) :
    result.checks <= capability.localDeletionBudget.coefficient *
      (capability.localDeletionBudget.size result.stage.previous + 1) ^
        capability.localDeletionBudget.degree := by
  rw [result.checks_eq]
  exact capability.localDeletionBudget.bounded result.stage.previous

end ExecutionResult

/-- Execute CT2 on one literal predecessor ledger. -/
def run
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    (capability : Capability Target progress spec) (previous : Previous) :
    ExecutionResult capability :=
  let routed := route capability previous
  {
    stage := routed
    trace := traceOfRoute routed
    checks := 1
    checks_eq := rfl
  }

@[simp] theorem run_previous
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    (capability : Capability Target progress spec) (previous : Previous) :
    (run capability previous).stage.previous = previous :=
  rfl

/-- Mandatory deletion-C2 closure after an eligibility proof. -/
structure DeletionRun
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    (capability : Capability Target progress spec) (previous : Previous) where
  private mk ::
  witness : DeletionWitness capability previous
  trace : Trace .deletionC2
  checks : Nat
  checks_eq : checks = 1

namespace DeletionRun

def terminal
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    {capability : Capability Target progress spec} {previous : Previous}
    (_result : DeletionRun capability previous) : Terminal :=
  .deletionC2

def traceNodes
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    {capability : Capability Target progress spec} {previous : Previous}
    (result : DeletionRun capability previous) : List NodeId :=
  result.trace.nodes

end DeletionRun

/-- Build the unique closure run from semantic eligibility; no outcome is
chosen by the caller. -/
def closeSelected
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    (capability : Capability Target progress spec) (previous : Previous)
    (eligible : capability.Eligible previous) :
    DeletionRun capability previous where
  witness := capability.deletionWitness previous eligible
  trace := .deletionC2
  checks := 1
  checks_eq := rfl

end Hypostructure.CT2
