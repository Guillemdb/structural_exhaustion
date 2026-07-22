import Hypostructure.Core.Residual.NumericCap

/-!
# Focused numeric-cap split fixture

The fixture uses a neutral natural-number predecessor.  It exercises the
within and exceeded branches without any graph- or PDE-specific object.
-/

namespace Hypostructure.Fixtures.NumericCap

open Hypostructure.Core
open Hypostructure.Core.Residual

structure Input where
  load : Nat
  cap : Nat

abbrev rootFocus : Focus.Profile Input :=
  Focus.always Input

def loadQuery : Focus.ActiveQuery rootFocus fun _previous _active => Nat :=
  Focus.ActiveQuery.ofFunction fun previous _active => previous.load

def capQuery : Focus.ActiveQuery rootFocus fun _previous _active => Nat :=
  Focus.ActiveQuery.ofFunction fun previous _active => previous.cap

def capContract : NumericCap.Contract rootFocus where
  load := loadQuery
  cap := capQuery
  size := fun previous => previous.load + previous.cap

def withinInput : Input where
  load := 7
  cap := 10

def exceededInput : Input where
  load := 12
  cap := 10

def withinStage := capContract.run withinInput

def exceededStage := capContract.run exceededInput

def withinActive : rootFocus.Active withinInput :=
  trivial

def exceededActive : rootFocus.Active exceededInput :=
  trivial

theorem within_stage_retains_predecessor :
    withinStage.previous = withinInput :=
  capContract.run_previous withinInput

theorem exceeded_stage_retains_predecessor :
    exceededStage.previous = exceededInput :=
  capContract.run_previous exceededInput

theorem within_stage_work_budget_exact :
    (capContract.runCounted withinInput).checks =
      capContract.workBudget.checks withinInput :=
  capContract.runCounted_checks_of_active withinInput withinActive

theorem exceeded_stage_work_budget_exact :
    (capContract.runCounted exceededInput).checks =
      capContract.workBudget.checks exceededInput :=
  capContract.runCounted_checks_of_active exceededInput exceededActive

theorem within_run_work_bounded :
    (capContract.runCounted withinInput).checks <=
      capContract.workBudget.coefficient *
        (capContract.workBudget.size withinInput + 1) ^
          capContract.workBudget.degree :=
  capContract.runCounted_checks_bounded withinInput

theorem exceeded_run_work_bounded :
    (capContract.runCounted exceededInput).checks <=
      capContract.workBudget.coefficient *
        (capContract.workBudget.size exceededInput + 1) ^
          capContract.workBudget.degree :=
  capContract.runCounted_checks_bounded exceededInput

#print axioms within_stage_work_budget_exact
#print axioms exceeded_stage_work_budget_exact

end Hypostructure.Fixtures.NumericCap
