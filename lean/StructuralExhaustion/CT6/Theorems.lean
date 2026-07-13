import StructuralExhaustion.CT6.Execution

namespace StructuralExhaustion.CT6

variable {P : Core.Problem} (S : Spec P) (capability : Capability S)
variable (input : Input P)
namespace RawOutcome
def Valid {terminal} : RawOutcome S capability input terminal → Prop
  | .firstFailure residual =>
      S.Failure input residual.hit.value ∧
        (∀ candidate, candidate ∈ residual.hit.before →
          ¬ S.Failure input candidate)
  | .activeLedger residual => ∀ index, ¬ S.Failure input index
theorem verified {terminal} (outcome : RawOutcome S capability input terminal) :
    outcome.Valid := by
  cases outcome with
  | firstFailure residual => exact ⟨residual.hit.holds,
      residual.hit.beforeAbsent⟩
  | activeLedger residual => exact residual.noFailure
end RawOutcome
namespace ExecutionResult
theorem verified (result : ExecutionResult S capability input) :
    result.outcome.Valid := result.outcome.verified
theorem traceValid (result : ExecutionResult S capability input) :
    Graph.ValidTrace S capability input result.trace :=
  ⟨result.terminal, result.path, rfl⟩

/-- Extract the active-ledger residual carried by this exact execution result.
The terminal equality rules out the first-failure outcome. -/
def activeLedgerResidual_of_terminal_eq
    {S : Spec P} {capability : Capability S} {input : Input P}
    (result : ExecutionResult S capability input)
    (terminalEq : result.terminal = .activeLedger) :
    ActiveLedgerResidual S capability input := by
  cases result with
  | mk _terminal _path outcome =>
      cases outcome with
      | firstFailure _residual => simp at terminalEq
      | activeLedger residual => exact residual
end ExecutionResult
theorem run_verified : (run S capability input).outcome.Valid :=
  (run S capability input).verified
theorem run_trace_valid :
    Graph.ValidTrace S capability input (run S capability input).trace :=
  (run S capability input).traceValid
theorem run_total : ∃ result : ExecutionResult S capability input,
    result.outcome.Valid ∧ Graph.ValidTrace S capability input result.trace :=
  ⟨run S capability input, run_verified S capability input,
    run_trace_valid S capability input⟩
theorem run_deterministic (left right : ExecutionResult S capability input)
    (hl : left = run S capability input) (hr : right = run S capability input) :
    left = right := hl.trans hr.symm

theorem outcome_exhaustive (result : ExecutionResult S capability input) :
    result.terminal = .firstFailure ∨
      result.terminal = .activeLedger := by
  cases result with
  | mk _ _ outcome =>
      cases outcome with
      | firstFailure _ => exact Or.inl rfl
      | activeLedger _ => exact Or.inr rfl

/-- Build the complete active ledger once the application has ruled out every
monitored failure.  The ledger total is framework-computed; the application
supplies only the semantic no-failure premise. -/
def activeLedgerResidual_of_noFailure
    (noFailure : ∀ index, ¬ S.Failure input index) :
    ActiveLedgerResidual S capability input where
  noFailure := noFailure
  total := activeTotal S capability input
  computed := rfl

/-- If the application rules out every monitored failure, the actual CT6
reference run selects the active-ledger terminal. -/
theorem run_terminal_activeLedger_of_noFailure
    (noFailure : ∀ index, ¬ S.Failure input index) :
    (run S capability input).terminal = .activeLedger := by
  cases decision : analyzeActivity S capability input with
  | firstFailure residual =>
      exact (noFailure residual.hit.value residual.hit.holds).elim
  | active residual =>
      simp [run, runReference, decision]

/-- If the application rules out every monitored failure, the actual CT6
reference run has the unique active-ledger node trace. -/
theorem run_trace_activeLedger_of_noFailure
    (noFailure : ∀ index, ¬ S.Failure input index) :
    (run S capability input).trace =
      [.entry, .firstFailureSearch, .activeLedgerTerminal] := by
  cases decision : analyzeActivity S capability input with
  | firstFailure residual =>
      exact (noFailure residual.hit.value residual.hit.holds).elim
  | active residual =>
      simp only [run]
      unfold runReference
      rw [decision]
      rfl

/-- Extract the active-ledger residual carried by the actual reference run
once the application has ruled out every monitored failure. -/
def runActiveLedgerResidual_of_noFailure
    (noFailure : ∀ index, ¬ S.Failure input index) :
    ActiveLedgerResidual S capability input :=
  (run S capability input).activeLedgerResidual_of_terminal_eq
    (run_terminal_activeLedger_of_noFailure S capability input noFailure)

/-- Exact reference-run package for the forced active-ledger branch.

The residual accessor below is extracted from this very execution using
`terminal_eq`; it is not a separately reconstructed semantic certificate. -/
structure ActiveLedgerRun where
  terminal_eq : (run S capability input).terminal = .activeLedger
  trace_eq : (run S capability input).trace =
    [.entry, .firstFailureSearch, .activeLedgerTerminal]

namespace ActiveLedgerRun

/-- The reference execution certified by this package. -/
def execution (_bundle : ActiveLedgerRun S capability input) :
    ExecutionResult S capability input :=
  run S capability input

/-- The active-ledger residual carried by the certified reference execution. -/
def residual (bundle : ActiveLedgerRun S capability input) :
    ActiveLedgerResidual S capability input :=
  bundle.execution.activeLedgerResidual_of_terminal_eq bundle.terminal_eq

theorem noFailure (bundle : ActiveLedgerRun S capability input) :
    ∀ index, ¬ S.Failure input index :=
  bundle.residual.noFailure

end ActiveLedgerRun

/-- Run CT6 under the sole application premise that every monitored failure
is absent, retaining the exact residual, terminal, and audit trace together. -/
def runActiveLedgerOfNoFailure
    (noFailure : ∀ index, ¬ S.Failure input index) :
    ActiveLedgerRun S capability input where
  terminal_eq :=
    run_terminal_activeLedger_of_noFailure S capability input noFailure
  trace_eq :=
    run_trace_activeLedger_of_noFailure S capability input noFailure

end StructuralExhaustion.CT6
