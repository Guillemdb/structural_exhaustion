import Hypostructure.CT3.Schedule

/-!
# CT3 scheduled witness extraction

The schedule classifier identifies terminal families.  This module exposes
generic witness packages for good terminals and residual terminals.  Domain
code supplies only the item-indexed evidence interpretation; CT3 owns the
case split over terminal families.
-/

namespace Hypostructure.CT3.ScheduleWitness

open Hypostructure.Core.Finite

universe u vGood vResidual

/-- Problem-supplied interpretation of terminal evidence for scheduled CT3
items.  The fields are abstract payloads, not graph replacements. -/
structure EvidenceContract {Item : Type u}
    (schedule : Schedule.Contract Item) where
  GoodWitness : Item -> Type vGood
  ResidualWitness : Item -> Type vResidual
  good_of_compression :
    (item : Item) -> schedule.terminal item = Terminal.compression ->
      GoodWitness item
  good_of_knownRow :
    (item : Item) -> schedule.terminal item = Terminal.knownRow ->
      GoodWitness item
  residual_of_distinguishing :
    (item : Item) -> schedule.terminal item = Terminal.distinguishing ->
      ResidualWitness item
  residual_of_novelRow :
    (item : Item) -> schedule.terminal item = Terminal.novelRow ->
      ResidualWitness item

namespace EvidenceContract

variable {Item : Type u} {schedule : Schedule.Contract Item}
variable (contract : EvidenceContract schedule)

/-- Extract existence of the common witness from either good CT3 terminal. -/
theorem goodWitness_nonempty {item : Item}
    (good : schedule.GoodTerminal item) :
    Nonempty (contract.GoodWitness item) := by
  rcases good with compression | known
  · exact ⟨contract.good_of_compression item compression⟩
  · exact ⟨contract.good_of_knownRow item known⟩

/-- Framework-owned selected witness from either good CT3 terminal.  The
terminal proof lives in `Prop`, so choosing a payload is necessarily
noncomputable for arbitrary witness carriers; CT3 owns that choice so graph
and PDE applications do not. -/
noncomputable def goodWitnessOfGood {item : Item}
    (good : schedule.GoodTerminal item) :
    contract.GoodWitness item :=
  Classical.choice (contract.goodWitness_nonempty good)

/-- Extract existence of the common residual witness from either CT3
residual terminal. -/
theorem residualWitness_nonempty {item : Item}
    (residual : schedule.ResidualTerminal item) :
    Nonempty (contract.ResidualWitness item) := by
  rcases residual with distinguishing | novel
  · exact ⟨contract.residual_of_distinguishing item distinguishing⟩
  · exact ⟨contract.residual_of_novelRow item novel⟩

/-- Framework-owned selected witness from either CT3 residual terminal. -/
noncomputable def residualWitnessOfResidual {item : Item}
    (residual : schedule.ResidualTerminal item) :
    contract.ResidualWitness item :=
  Classical.choice (contract.residualWitness_nonempty residual)

/-- Schedule-wide actual good-terminal witnesses. -/
noncomputable def allGoodWitnessFunction (allGood : schedule.AllGood) :
    (item : Item) -> item ∈ schedule.items.values ->
      contract.GoodWitness item :=
  fun item member => contract.goodWitnessOfGood (allGood item member)

/-- Schedule-wide good-terminal witnesses. -/
def allGoodWitnesses (_allGood : schedule.AllGood) : Prop :=
  ∀ item ∈ schedule.items.values,
    Nonempty (contract.GoodWitness item)

theorem allGoodWitnesses_of_allGood (allGood : schedule.AllGood) :
    contract.allGoodWitnesses allGood := by
  intro item member
  exact contract.goodWitness_nonempty (allGood item member)

/-- First residual witness selected by the schedule classifier. -/
def FirstResidualWitness : Prop :=
  ∃ item ∈ schedule.items.values,
    Nonempty (contract.ResidualWitness item)

theorem firstResidualWitness_of_hasResidual
    (hasResidual : schedule.HasResidual) :
    contract.FirstResidualWitness := by
  rcases hasResidual with ⟨item, member, residual⟩
  exact ⟨item, member, contract.residualWitness_nonempty residual⟩

/-- Residual witness at the exact first residual hit selected by CT3. -/
noncomputable def residualWitnessAtFirstHit
    (hit : _root_.Hypostructure.Core.Finite.Search.IndexedHit
      schedule.items schedule.ResidualTerminal) :
    contract.ResidualWitness hit.value :=
  contract.residualWitnessOfResidual hit.sound

/-- Residual witness at the exact first residual hit selected by CT3. -/
theorem residualWitnessOfFirstHit
    (hit : _root_.Hypostructure.Core.Finite.Search.IndexedHit
      schedule.items schedule.ResidualTerminal) :
    Nonempty (contract.ResidualWitness hit.value) :=
  ⟨contract.residualWitnessAtFirstHit hit⟩

/-- First residual witness selected by the schedule classifier, retaining the
exact item chosen by the framework search. -/
theorem firstResidualWitness_of_firstHit
    (hit : _root_.Hypostructure.Core.Finite.Search.IndexedHit
      schedule.items schedule.ResidualTerminal) :
    ∃ item ∈ schedule.items.values,
      Nonempty (contract.ResidualWitness item) :=
  ⟨hit.value, hit.member, contract.residualWitnessOfFirstHit hit⟩

end EvidenceContract

end Hypostructure.CT3.ScheduleWitness
