import StructuralExhaustion.CT6.Automation

namespace StructuralExhaustion.Examples.CT6AutomationFirst

open StructuralExhaustion

@[implicit_reducible]
def bools : FinEnum Bool :=
  StructuralExhaustion.Core.Enumeration.bool

def problem : Core.Problem where
  Ambient := Bool
  Baseline := fun _ => True
  rank := fun G => if G then 1 else 0
  BranchState := fun _ => Unit

def spec : CT6.Spec problem where
  Index := Bool
  FailureData := Bool
  Failure := fun ctx index => ctx.G = true ∧ index = true
  failureData := fun _ index _ => index
  contribution := fun _ _ => 1

def capability : CT6.Capability spec where
  failureOrder := bools
  failureDecidable := by
    intro ctx index
    change Decidable (ctx.G = true ∧ index = true)
    cases ctx.G with
    | false => exact .isFalse (by simp)
    | true =>
        cases index with
        | false => exact .isFalse (by simp)
        | true => exact .isTrue ⟨rfl, rfl⟩

def input (G : Bool) : CT6.Input problem where
  G := G
  baseline := trivial
  state := ()

def failureResult := CT6.run spec capability (input true)
def activeResult := CT6.run spec capability (input false)

/-- The only application theorem needed to select CT6's active branch. -/
theorem noFailureAtActiveInput :
    ∀ index, ¬ spec.Failure (input false) index := by
  intro index failure
  exact Bool.noConfusion failure.1

/-- Kernel-checked use of the framework ledger constructor. -/
def activeLedgerFromNoFailure :
    CT6.ActiveLedgerResidual spec capability (input false) :=
  CT6.activeLedgerResidual_of_noFailure spec capability (input false)
    noFailureAtActiveInput

theorem failure_terminal : failureResult.terminal = .firstFailure := rfl
theorem active_terminal : activeResult.terminal = .activeLedger := rfl
theorem failure_trace : failureResult.trace =
    [.entry, .firstFailureSearch, .firstFailureTerminal] := rfl
theorem active_trace : activeResult.trace =
    [.entry, .firstFailureSearch, .activeLedgerTerminal] := rfl

/-- Generic extraction from the typed outcome of an exact execution result. -/
def activeLedgerFromResult :
    CT6.ActiveLedgerResidual spec capability (input false) :=
  activeResult.activeLedgerResidual_of_terminal_eq active_terminal

/-- Reference-run specialization from the application no-failure premise. -/
def activeLedgerFromActualRun :
    CT6.ActiveLedgerResidual spec capability (input false) :=
  CT6.runActiveLedgerResidual_of_noFailure spec capability (input false)
    noFailureAtActiveInput

/-- Exact active-branch bundle generated from the same sole premise. -/
def activeRun : CT6.ActiveLedgerRun spec capability (input false) :=
  CT6.runActiveLedgerOfNoFailure spec capability (input false)
    noFailureAtActiveInput

example : activeLedgerFromNoFailure.noFailure = noFailureAtActiveInput := rfl
example : ∀ index, ¬ spec.Failure (input false) index :=
  activeLedgerFromResult.noFailure
example : ∀ index, ¬ spec.Failure (input false) index :=
  activeLedgerFromActualRun.noFailure
example : activeRun.execution = activeResult := rfl
example : ∀ index, ¬ spec.Failure (input false) index :=
  activeRun.residual.noFailure
example : activeRun.execution.terminal = .activeLedger :=
  activeRun.terminal_eq
example : activeRun.execution.trace =
    [.entry, .firstFailureSearch, .activeLedgerTerminal] :=
  activeRun.trace_eq
example : activeLedgerFromNoFailure.total = CT6.activeTotal spec capability
    (input false) := rfl
example : activeResult.terminal = .activeLedger :=
  CT6.run_terminal_activeLedger_of_noFailure spec capability (input false)
    noFailureAtActiveInput
example : activeResult.trace =
    [.entry, .firstFailureSearch, .activeLedgerTerminal] :=
  CT6.run_trace_activeLedger_of_noFailure spec capability (input false)
    noFailureAtActiveInput

example : failureResult.outcome.Valid := failureResult.verified
example : activeResult.outcome.Valid := activeResult.verified
example : ∃ result : CT6.ExecutionResult spec capability (input false),
    result.outcome.Valid ∧
      CT6.Graph.ValidTrace spec capability (input false) result.trace := by
  ct6_total spec using capability at (input false)

example : CT6.capabilityContract.derivedOperations.contains
    "CT6.activeLedgerResidual_of_noFailure" = true := by native_decide
example : CT6.capabilityContract.derivedOperations.contains
    "CT6.ExecutionResult.activeLedgerResidual_of_terminal_eq" = true := by
  native_decide
example : CT6.capabilityContract.derivedOperations.contains
    "CT6.runActiveLedgerResidual_of_noFailure" = true := by native_decide
example : CT6.capabilityContract.derivedOperations.contains
    "CT6.run_terminal_activeLedger_of_noFailure" = true := by native_decide
example : CT6.capabilityContract.derivedOperations.contains
    "CT6.run_trace_activeLedger_of_noFailure" = true := by native_decide
example : CT6.capabilityContract.derivedOperations.contains
    "CT6.runActiveLedgerOfNoFailure" = true := by native_decide

end StructuralExhaustion.Examples.CT6AutomationFirst
