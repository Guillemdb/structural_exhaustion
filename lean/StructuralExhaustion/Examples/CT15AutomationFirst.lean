import StructuralExhaustion.CT15.Automation

namespace StructuralExhaustion.Examples.CT15AutomationFirst

open StructuralExhaustion

def problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ => True
  rank := fun _ => 0
  BranchState := fun _ => Unit

def branch : Core.BranchContext problem where
  G := ()
  baseline := trivial
  state := ()

@[implicit_reducible]
def bools : FinEnum Bool :=
  StructuralExhaustion.Core.Enumeration.bool

/-! ## First target-relative rank drop -/

def dropSpec : CT15.Spec problem where
  Coordinate := Bool
  TargetDependent := fun _ coordinate => coordinate = false
  charge := fun _ _ => 9
  capacity := fun _ => 100

def dependentAtFalse : (coordinate : Bool) → Decidable (coordinate = false)
  | false => .isTrue rfl
  | true => .isFalse (by intro equality; cases equality)

def dropCapability : CT15.Capability dropSpec where
  coordinates := bools
  targetDependentDecidable := fun _ coordinate => dependentAtFalse coordinate

def dropRank := CT15.computeRank dropSpec dropCapability branch
def dropResult := CT15.run dropSpec dropCapability branch

theorem drop_computed_rank : dropRank.value = 1 :=
  rfl

theorem drop_terminal : dropResult.terminal = .rankDrop :=
  rfl

theorem drop_is_first_coordinate :
    match dropResult.outcome with
    | .rankDrop residual =>
        residual.hit.value = false ∧ residual.hit.before = []
    | _ => False :=
  ⟨rfl, rfl⟩

theorem drop_trace : dropResult.trace =
    [.entry, .rankComputation, .rankSplit, .rankDropTerminal] :=
  rfl

theorem drop_sound : dropResult.outcome.Valid :=
  CT15.run_verified dropSpec dropCapability branch

/-! ## Full rank exceeds capacity and closes by C4 -/

def c4Spec : CT15.Spec problem where
  Coordinate := Bool
  TargetDependent := fun _ _ => False
  charge := fun _ coordinate => if coordinate then 3 else 2
  capacity := fun _ => 4

def c4Capability : CT15.Capability c4Spec where
  coordinates := bools
  targetDependentDecidable := fun _ _ => .isFalse id

def c4Rank := CT15.computeRank c4Spec c4Capability branch
def c4Result := CT15.run c4Spec c4Capability branch

theorem c4_computed_full_rank : c4Rank.value = 2 :=
  rfl

theorem c4_exact_entries :
    CT15.ledgerEntries c4Spec c4Capability branch =
      [(false, 2), (true, 3)] :=
  rfl

theorem c4_exact_total :
    CT15.ledgerTotal c4Spec c4Capability branch = 5 :=
  rfl

theorem c4_terminal : c4Result.terminal = .c4 :=
  rfl

theorem c4_trace : c4Result.trace =
    [.entry, .rankComputation, .rankSplit, .ledgerComputation,
      .ledgerComparison, .c4Terminal] :=
  rfl

example : c4Result.outcome.Valid := by
  ct15 c4Spec using c4Capability at branch

/-! ## Full rank fits capacity and emits the exact ledger residual -/

def ledgerSpec : CT15.Spec problem where
  Coordinate := Bool
  TargetDependent := fun _ _ => False
  charge := fun _ coordinate => if coordinate then 2 else 1
  capacity := fun _ => 3

def ledgerCapability : CT15.Capability ledgerSpec where
  coordinates := bools
  targetDependentDecidable := fun _ _ => .isFalse id

def ledgerRank := CT15.computeRank ledgerSpec ledgerCapability branch
def ledgerResult := CT15.run ledgerSpec ledgerCapability branch

theorem ledger_computed_full_rank : ledgerRank.value = 2 :=
  rfl

theorem ledger_exact_entries :
    CT15.ledgerEntries ledgerSpec ledgerCapability branch =
      [(false, 1), (true, 2)] :=
  rfl

theorem ledger_exact_total :
    CT15.ledgerTotal ledgerSpec ledgerCapability branch = 3 :=
  rfl

theorem ledger_terminal : ledgerResult.terminal = .fullRankLedger :=
  rfl

theorem ledger_trace : ledgerResult.trace =
    [.entry, .rankComputation, .rankSplit, .ledgerComputation,
      .ledgerComparison, .fullRankLedgerTerminal] :=
  rfl

theorem ledger_sound : ledgerResult.outcome.Valid :=
  CT15.run_verified ledgerSpec ledgerCapability branch

example : ∃ result : CT15.ExecutionResult
    ledgerSpec ledgerCapability branch,
    result.outcome.Valid ∧
      @CT15.Graph.ValidTrace problem ledgerSpec ledgerCapability
        branch result.trace := by
  ct15_total ledgerSpec using ledgerCapability at branch

example : ledgerResult = ledgerResult :=
  CT15.run_deterministic ledgerSpec ledgerCapability branch
    ledgerResult ledgerResult rfl rfl

example : ledgerResult.terminal = .rankDrop ∨
    ledgerResult.terminal = .c4 ∨
    ledgerResult.terminal = .fullRankLedger :=
  CT15.outcome_exhaustive ledgerSpec ledgerCapability branch ledgerResult

end StructuralExhaustion.Examples.CT15AutomationFirst
