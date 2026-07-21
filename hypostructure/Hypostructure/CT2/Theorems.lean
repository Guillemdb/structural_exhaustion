import Hypostructure.CT2.Execution

/-!
# CT2 soundness, totality, and criticality
-/

namespace Hypostructure.CT2

universe uAmbient uBranch uMeasure uPrevious uPiece

/-- Semantic proposition advertised by each local-deletion terminal. -/
def OutcomeClaim
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    (capability : Capability Target progress spec) (previous : Previous) :
    Terminal -> Prop
  | .deletionC2 => False
  | .criticality => CriticalityState capability previous

/-- Core's routed decision proves exactly the claim of its derived terminal. -/
theorem routed_verified
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    {capability : Capability Target progress spec}
    (routed : RoutedDecision capability) :
    OutcomeClaim capability routed.previous (terminalOfRoute routed) := by
  cases branch : routed.added with
  | yesBranch eligible =>
      simpa [OutcomeClaim, terminalOfRoute, branch] using
        (capability.deletionWitness routed.previous eligible).contradiction
  | noBranch criticality =>
      simpa [OutcomeClaim, terminalOfRoute, branch] using criticality

namespace ExecutionResult

/-- Aggregate semantic soundness of a completed CT2 execution. -/
theorem verified
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    {capability : Capability Target progress spec}
    (result : ExecutionResult capability) :
    OutcomeClaim capability result.stage.previous result.terminal :=
  routed_verified result.stage

/-- Every generated trace is the canonical trace for its derived terminal. -/
theorem trace_exact
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    {capability : Capability Target progress spec}
    (result : ExecutionResult capability) :
    result.traceNodes = Trace.expectedNodes result.terminal :=
  result.trace.nodes_eq_expected

/-- An executable positive branch is closed immediately by minimality, so the
surviving accumulated result is the exact criticality residual. -/
theorem terminal_criticality
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    {capability : Capability Target progress spec}
    (result : ExecutionResult capability) : result.terminal = .criticality := by
  cases branch : result.stage.added with
  | yesBranch _ =>
      have impossible : False := by
        simpa [OutcomeClaim, ExecutionResult.terminal,
          terminalOfRoute, branch] using result.verified
      exact impossible.elim
  | noBranch _ =>
      simp [ExecutionResult.terminal, terminalOfRoute, branch]

/-- Retrieve the exact complementary state stored by Core's decision. -/
theorem criticality
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    {capability : Capability Target progress spec}
    (result : ExecutionResult capability) :
    CriticalityState capability result.stage.previous := by
  have sound := result.verified
  rw [result.terminal_criticality] at sound
  exact sound

/-- An admissible selected piece cannot be proper in the inherited minimal
counterexample. -/
theorem notProper_of_admissible
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    {capability : Capability Target progress spec}
    (result : ExecutionResult capability)
    (admissible : spec.Admissible
      (capability.contextAt result.stage.previous).state
      (capability.selectedPiece result.stage.previous)) :
    Not (spec.Proper (capability.selectedPiece result.stage.previous)) := by
  intro proper
  exact result.criticality ⟨proper, admissible⟩

/-- A proper selected piece must fail the declared deletion admissibility. -/
theorem notAdmissible_of_proper
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    {capability : Capability Target progress spec}
    (result : ExecutionResult capability)
    (proper : spec.Proper
      (capability.selectedPiece result.stage.previous)) :
    Not (spec.Admissible
      (capability.contextAt result.stage.previous).state
      (capability.selectedPiece result.stage.previous)) := by
  intro admissible
  exact result.criticality ⟨proper, admissible⟩

end ExecutionResult

namespace DeletionRun

/-- Exact semantic closure of an eligibility-triggered deletion run. -/
theorem verified
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    {capability : Capability Target progress spec} {previous : Previous}
    (result : DeletionRun capability previous) : False :=
  result.witness.contradiction

/-- The mandatory closure run has the exact deletion-C2 trace. -/
theorem trace_exact
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    {capability : Capability Target progress spec} {previous : Previous}
    (result : DeletionRun capability previous) :
    result.traceNodes = Trace.expectedNodes .deletionC2 :=
  result.trace.nodes_eq_expected

end DeletionRun

/-- The public reference executor is semantically sound. -/
theorem run_verified
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    (capability : Capability Target progress spec) (previous : Previous) :
    OutcomeClaim capability previous (run capability previous).terminal :=
  (run capability previous).verified

/-- CT2 is total, sound, exactly traced, and work-bounded. -/
theorem run_total
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    (capability : Capability Target progress spec) (previous : Previous) :
    Exists fun result : ExecutionResult capability =>
      result.stage.previous = previous ∧
      OutcomeClaim capability previous result.terminal ∧
      result.traceNodes = Trace.expectedNodes result.terminal ∧
      result.checks <= capability.localDeletionBudget.coefficient *
        (capability.localDeletionBudget.size previous + 1) ^
          capability.localDeletionBudget.degree := by
  let result := run capability previous
  exact ⟨result, rfl, result.verified, result.trace_exact,
    result.checks_le_polynomial⟩

/-- Reference execution is deterministic in relational form. -/
theorem run_deterministic
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    (capability : Capability Target progress spec) (previous : Previous)
    (first second : ExecutionResult capability)
    (firstIsRun : first = run capability previous)
    (secondIsRun : second = run capability previous) : first = second :=
  firstIsRun.trans secondIsRun.symm

/-- No terminal outside the two CT2 outcomes is representable. -/
theorem outcome_exhaustive
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    {capability : Capability Target progress spec}
    (result : ExecutionResult capability) :
    result.terminal = .deletionC2 ∨ result.terminal = .criticality := by
  cases branch : result.stage.added <;>
    simp [ExecutionResult.terminal, terminalOfRoute, branch]

end Hypostructure.CT2
