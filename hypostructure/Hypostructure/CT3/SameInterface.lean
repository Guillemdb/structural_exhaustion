import Hypostructure.CT3.ScheduleWitness
import Hypostructure.Core.Response.SameInterface

/-!
# CT3 same-interface package bridge

This module owns the generic bridge from scheduled good CT3 terminals to
same-interface replacement packages.  Domains provide only the interpretation
of a good terminal witness as a verified package; CT3/Core own the residual
querying, item schedule, and ledger registration.
-/

namespace Hypostructure.CT3.SameInterface

open Hypostructure.Core
open Hypostructure.Core.Residual
open Hypostructure.Core.Response

universe uPrevious uItem uGood uResidual

/-- Contract for turning CT3 good-terminal witnesses into verified
same-interface packages. -/
structure PackageContract {Previous : Sort uPrevious}
    {focus : Focus.Profile Previous}
    (schedule : Schedule.FocusedContract.{uPrevious, uItem} focus) where
  evidence :
    (previous : Previous) -> (active : focus.Active previous) ->
      ScheduleWitness.EvidenceContract.{uItem, uGood, uResidual}
        (schedule.scheduleAt previous active)
  packageOfGood :
    (previous : Previous) -> (active : focus.Active previous) ->
      (item : schedule.Item) ->
      (good : (schedule.scheduleAt previous active).GoodTerminal item) ->
      (evidence previous active).GoodWitness item ->
        SameInterface.VerifiedPackage

namespace PackageContract

variable {Previous : Sort uPrevious} {focus : Focus.Profile Previous}
variable {schedule : Schedule.FocusedContract.{uPrevious, uItem} focus}
variable (contract : PackageContract schedule)

/-- Extract the good witness for one scheduled item on the all-good branch. -/
noncomputable def goodWitnessAt
    (stage : schedule.Stage) (active : schedule.allGoodFocus.Active stage)
    (item : schedule.Item)
    (member : item ∈ (schedule.items.read stage.previous active.parent).values) :
    (contract.evidence stage.previous active.parent).GoodWitness item :=
  (contract.evidence stage.previous active.parent).goodWitnessOfGood
    ((schedule.allGoodQuery.read stage active) item member)

/-- Read all good-terminal witnesses on the all-good branch. -/
noncomputable def allGoodWitnessQuery :
    Focus.ActiveQuery schedule.allGoodFocus fun stage active =>
      (item : schedule.Item) ->
        item ∈ (schedule.items.read stage.previous active.parent).values ->
          (contract.evidence stage.previous active.parent).GoodWitness item :=
  Focus.ActiveQuery.ofFunction fun stage active item member =>
    contract.goodWitnessAt stage active item member

/-- Core same-interface registration contract generated from the CT3
all-good branch.  The package for each item is read from the CT3 all-good
residual and installed as one framework-owned ledger extension. -/
noncomputable def verifiedSameInterfaceContract :
    SameInterface.VerifiedContract schedule.allGoodFocus where
  Item := schedule.Item
  items := Focus.ActiveQuery.ofFunction fun stage active =>
    (schedule.items.read stage.previous active.parent).values
  package := Focus.ActiveQuery.ofFunction fun stage active item member =>
    let good := (schedule.allGoodQuery.read stage active) item member
    let witness : (contract.evidence stage.previous active.parent).GoodWitness
        item :=
      contract.goodWitnessAt stage active item member
    contract.packageOfGood stage.previous active.parent item good witness

/-- Abstract Core same-interface registration contract generated from the CT3
all-good branch. -/
noncomputable def sameInterfaceContract :
    SameInterface.Contract schedule.allGoodFocus :=
  (contract.verifiedSameInterfaceContract).toContract

/-- Execute the same-interface package registration generated from CT3
good-terminal witnesses. -/
noncomputable def register (stage : schedule.Stage) :
    (contract.sameInterfaceContract).Stage :=
  (contract.sameInterfaceContract).run stage

/-- Execute CT3 schedule classification from the predecessor, then register
same-interface packages on the framework-selected all-good branch.  This is
the high-level CT3-owned composition used by downstream applications that
should not manually thread the intermediate schedule stage. -/
noncomputable def registerClassified (previous : Previous) :
    (contract.sameInterfaceContract).Stage :=
  contract.register (schedule.runStage previous)

@[simp] theorem registerClassified_previous (previous : Previous) :
    (contract.registerClassified previous).previous =
      schedule.runStage previous :=
  (contract.sameInterfaceContract).run_previous (schedule.runStage previous)

@[simp] theorem registerClassified_source_previous (previous : Previous) :
    (contract.registerClassified previous).previous.previous = previous := by
  rw [contract.registerClassified_previous previous]
  exact schedule.runStage_previous previous

end PackageContract

end Hypostructure.CT3.SameInterface
