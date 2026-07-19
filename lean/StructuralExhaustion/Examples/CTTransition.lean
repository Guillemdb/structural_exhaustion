import StructuralExhaustion.Routes.Accumulated

namespace StructuralExhaustion.Examples.CTTransition

open Core Core.Routing

/-! A non-graph fixture for the residual-preserving transition kernel.  It
uses the same sole public accumulated-ledger profile as applications. -/

abbrev ct2Entry : ExecutableInterface .ct2 where
  Context := Nat
  Trigger := fun _ => Nat
  Result := fun _ _ => Nat
  execute := fun context trigger => context + trigger

abbrev ct1ToCT2Adapter : Routes.Accumulated.Adapter Nat ct2Entry where
  targetContext := id
  trigger := fun source => source + 1

abbrev ct1ToCT2 :=
  Routes.Accumulated.transition (sourceTactic := .ct1)
    ct2Entry ct1ToCT2Adapter

abbrev root : ResidualStage .ct1 Nat := ResidualStage.exact 3

def firstStage :=
  Routes.Accumulated.advanceCurrent ct2Entry ct1ToCT2Adapter root

example : Routes.Accumulated.OutputLedger
    ct2Entry ct1ToCT2Adapter root :=
  firstStage

theorem firstOutcome_exact :
    firstStage.previous = root ∧
      firstStage.execution.result = 7 :=
  ⟨rfl, rfl⟩

/-! Two target profiles for the same typed `CT1 → CT2` family.  The first
profile above uses a natural-number trigger and result.  This profile uses a
unit trigger and Boolean result; its target mathematics reads only the
inherited context. -/

abbrev contextOnlyCT2Entry : ExecutableInterface .ct2 where
  Context := Nat
  Trigger := fun _ => Unit
  Result := fun _ _ => Bool
  execute := fun context _ => context == 7

abbrev contextOnlyAdapter :
    Routes.Accumulated.Adapter Nat contextOnlyCT2Entry where
  targetContext := fun source => source + 4
  trigger := fun _ => ()

abbrev contextOnlyCT1ToCT2 :=
  Routes.Accumulated.transition (sourceTactic := .ct1)
    contextOnlyCT2Entry contextOnlyAdapter

def contextOnlyStage :=
  Routes.Accumulated.advanceCurrent
    contextOnlyCT2Entry contextOnlyAdapter root

/-- Both profiles inhabit the same framework-owned typed CT pair. -/
theorem ct1ToCT2Profiles_share_typed_pair :
    ct1ToCT2.sourceTacticId = contextOnlyCT1ToCT2.sourceTacticId ∧
    ct1ToCT2.targetTacticId = contextOnlyCT1ToCT2.targetTacticId := by
  exact ⟨rfl, rfl⟩

/-- The profile types remain genuinely distinct behind the common transport. -/
theorem ct1ToCT2Profile_types :
    ct2Entry.Trigger 0 = Nat ∧
    ct2Entry.Result 0 0 = Nat ∧
    contextOnlyCT2Entry.Trigger 0 = Unit ∧
    contextOnlyCT2Entry.Result 0 () = Bool := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Every enabled context-only transition retains the literal predecessor
stage supplied to `run`. -/
@[simp] theorem contextOnly_exact_predecessor
    (stage : contextOnlyCT1ToCT2.EnabledStage root) :
    stage.previous = root :=
  stage.previous_eq

/-- At the fixture residual, inherited context `3 + 4` executes the Boolean
target profile while retaining the exact incoming stage. -/
theorem contextOnlyOutcome_exact :
    contextOnlyStage.previous = root ∧
      contextOnlyStage.execution.result = true :=
  ⟨rfl, rfl⟩

/-- A second CT consumes the complete first transition stage, not a rebuilt
copy of its numerical output. -/
abbrev ct3Entry : ExecutableInterface .ct3 where
  Context := Nat
  Trigger := fun _ => Unit
  Result := fun _ _ => Nat
  execute := fun context _ => context + 2

abbrev ct2ToCT3Adapter : Routes.Accumulated.Adapter Nat ct3Entry where
  targetContext := id
  trigger := fun _ => ()

abbrev ct2ToCT3Local :=
  Routes.Accumulated.transition (sourceTactic := .ct2)
    ct3Entry ct2ToCT3Adapter

/-- The reusable local CT2→CT3 family is lifted over the complete first-stage
ledger.  Only the current mathematical result is projected for CT3; the
transition output still retains the whole outer ledger. -/
theorem secondOutcome_retains_first
    (first : ct1ToCT2.EnabledStage root) :
    let second := Routes.Accumulated.advance ct3Entry ct2ToCT3Adapter
      (fun ledger => ledger.execution.result) first.ledgerStage
    second.previous = first.ledgerStage ∧
      second.execution.result = first.execution.result + 2 := by
  exact ⟨rfl, rfl⟩

/-! A semantic fact can be attached between the two CT executions without
unwrapping the first transition or rebuilding its target result. -/

def firstLedgerWithFact :
    ResidualStage .ct2
      (LedgerExtension (ct1ToCT2.EnabledStage root)
        (fun previous => previous.execution.result = 7)) :=
  firstStage.ledgerStage.extend rfl

@[simp] theorem firstLedgerWithFact_previous :
    firstLedgerWithFact.output.previous = firstStage :=
  rfl

@[simp] theorem firstLedgerWithFact_added :
    firstLedgerWithFact.output.added =
      (rfl : firstStage.execution.result = 7) :=
  rfl

/-- The second transition reads the actual CT2 target result through the
extended ledger's `previous` projection. -/
def secondStageWithFact :=
  Routes.Accumulated.advance ct3Entry ct2ToCT3Adapter
    (fun ledger => ledger.previous.execution.result) firstLedgerWithFact

@[simp] theorem secondStageWithFact_reads_actual_target :
    secondStageWithFact.execution.result =
      firstLedgerWithFact.output.previous.execution.result + 2 :=
  rfl

@[simp] theorem secondStageWithFact_retains_extension :
    secondStageWithFact.previous = firstLedgerWithFact :=
  rfl

/-! Pointwise CT execution is a dependent function, not an enumeration.  The
two fixture indices deliberately use different public context, trigger, and
result types. -/

abbrev pointwiseCT4Entry : Bool → ExecutableInterface .ct4
  | false => {
      Context := Nat
      Trigger := fun _context => Nat
      Result := fun _context _trigger => Nat
      execute := fun context trigger => context + trigger
    }
  | true => {
      Context := Bool
      Trigger := fun _context => Unit
      Result := fun _context _trigger => Bool
      execute := fun context _trigger => context
    }

abbrev pointwiseCT4Context :
    (index : Bool) → (pointwiseCT4Entry index).Context
  | false => by
      change Nat
      exact 5
  | true => by
      change Bool
      exact true

abbrev pointwiseCT4Trigger :
    (index : Bool) →
      (pointwiseCT4Entry index).Trigger (pointwiseCT4Context index)
  | false => by
      change Nat
      exact 2
  | true => by
      change Unit
      exact ()

abbrev pointwiseCT4Family : PointwiseExecutableFamily .ct4 where
  Index := Bool
  entry := pointwiseCT4Entry
  context := pointwiseCT4Context
  trigger := pointwiseCT4Trigger

abbrev pointwiseCT4Execution :=
  pointwiseCT4Family.executableInterface.execute () ()

@[simp] theorem pointwiseCT4Execution_false :
    (pointwiseCT4Execution false : Nat) = 7 :=
  rfl

@[simp] theorem pointwiseCT4Execution_true :
    (pointwiseCT4Execution true : Bool) = true :=
  rfl

/-! A family of specialized transition profiles likewise executes pointwise.
Unlike `PointwiseExecutableFamily`, this carrier retains every local typed
transition certificate as well as the common predecessor. -/

abbrev pointwiseCT5Entry (_index : Nat) : ExecutableInterface .ct5 where
  Context := Nat
  Trigger := fun _context => Nat
  Result := fun _context _trigger => Nat
  execute := fun context trigger => context + trigger

abbrev pointwiseCT4ToCT5Adapter (index : Nat) :
    Routes.Accumulated.Adapter Nat (pointwiseCT5Entry index) where
  targetContext := id
  trigger := fun _source => index

abbrev pointwiseCT4ToCT5Transition (index : Nat) :=
  Routes.Accumulated.transition (sourceTactic := .ct4)
    (pointwiseCT5Entry index) (pointwiseCT4ToCT5Adapter index)

abbrev pointwiseTransitionFamily :
    PointwiseTransitionFamily .ct4 .ct5 Nat where
  Index := Nat
  Source := fun _index => Nat
  target := pointwiseCT5Entry
  transition := pointwiseCT4ToCT5Transition
  current := fun index ledger => ledger + index
  seed := fun _index _source => ()
  discovered := fun _index _source => rfl

abbrev pointwiseTransitionSource : ResidualStage .ct4 Nat :=
  ResidualStage.exact 10

def pointwiseTransitionStage :=
  Routes.Accumulated.advanceSelectedPointwise
    pointwiseTransitionFamily pointwiseTransitionSource

example : Routes.Accumulated.SelectedPointwiseOutputLedger
    pointwiseTransitionFamily pointwiseTransitionSource :=
  pointwiseTransitionStage

@[simp] theorem pointwiseTransitionStage_three :
    (pointwiseTransitionStage.localStage 3).targetResult = 16 :=
  rfl

/-- The aggregate is one target-labelled ledger that retains the common
source once; no index enumeration or application wrapper is involved. -/
theorem pointwiseTransitionLedger_exact :
    pointwiseTransitionStage.ledgerStage.output = pointwiseTransitionStage :=
  rfl

/-! Ordinary total-residual families use the shorter framework constructor;
applications provide only their local adapters and current projections. -/

abbrev accumulatedPointwiseProfile :
    Routes.Accumulated.PointwiseAdapter .ct4 .ct5 Nat Nat where
  Source := fun _index => Nat
  target := pointwiseCT5Entry
  adapter := pointwiseCT4ToCT5Adapter
  current := fun index ledger => ledger + index

def accumulatedPointwiseStage :=
  Routes.Accumulated.advancePointwise accumulatedPointwiseProfile
    pointwiseTransitionSource

example : Routes.Accumulated.PointwiseOutputLedger
    accumulatedPointwiseProfile pointwiseTransitionSource :=
  accumulatedPointwiseStage

abbrev accumulatedPointwiseIndexThree :
    (Routes.Accumulated.pointwiseFamily
      accumulatedPointwiseProfile).Index := by
  change Nat
  exact 3

def accumulatedPointwiseResultThree : Nat :=
  (accumulatedPointwiseStage.localStage
    accumulatedPointwiseIndexThree).targetResult

@[simp] theorem accumulatedPointwiseStage_three :
    accumulatedPointwiseResultThree = 16 :=
  rfl

theorem accumulatedPointwiseLedger_exact :
    accumulatedPointwiseStage.ledgerStage.output =
      accumulatedPointwiseStage :=
  rfl

end StructuralExhaustion.Examples.CTTransition
