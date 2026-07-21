import Hypostructure.CT10.State
import Hypostructure.Core.Finite.Accounting

/-!
# CT10 canonical searches

All scans delegate to Core finite search.  The direct scan is run first.  Row
observation scans the residual-owned datum schedule, and the outer class scan
therefore selects the first missing class in the residual-owned class order.
-/

namespace Hypostructure.CT10

universe uPrevious uDatum uClass uPromotion

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uDatum, uClass, uPromotion} Previous}

/-- Counted canonical direct-class scan. -/
def countedDirectScan (capability : Capability spec) (previous : Previous) :=
  Core.Finite.Accounting.countedRun (capability.classesAt previous)
    (spec.Direct previous) (capability.directDecidable previous)

/-- Canonical direct-class search. -/
def directScan (capability : Capability spec) (previous : Previous) :=
  (countedDirectScan capability previous).value

/-- Exact primitive direct-predicate checks. -/
def directChecks (capability : Capability spec) (previous : Previous) : Nat :=
  (countedDirectScan capability previous).checks

/-- Counted observation scan for one class. -/
def countedRowScan (capability : Capability spec) (previous : Previous)
    (cls : spec.Class previous) :=
  Core.Finite.Accounting.countedRun (capability.dataAt previous)
    (InClass spec previous cls) fun datum =>
      (capability.classesAt previous).decEq
        (spec.classOf previous datum) cls

/-- Canonical observation scan for one class. -/
def rowScan (capability : Capability spec) (previous : Previous)
    (cls : spec.Class previous) :=
  (countedRowScan capability previous cls).value

/-- Exact primitive class-equality checks in one row observation. -/
def rowChecks (capability : Capability spec) (previous : Previous)
    (cls : spec.Class previous) : Nat :=
  (countedRowScan capability previous cls).checks

/-- A successful row scan is exactly an observation from incoming data. -/
theorem observed_of_rowHit (capability : Capability spec)
    (previous : Previous) (cls : spec.Class previous)
    (hasHit : (rowScan capability previous cls).HasHit) :
    Observed capability previous cls := by
  let hit := (rowScan capability previous cls).hitOfHasHit hasHit
  exact ⟨hit.value, hit.member, hit.sound⟩

/-- Any incoming datum in a class forces the canonical row scan to hit. -/
theorem rowHit_of_observed (capability : Capability spec)
    (previous : Previous) (cls : spec.Class previous)
    (observed : Observed capability previous cls) :
    (rowScan capability previous cls).HasHit := by
  apply Core.Finite.Search.complete
  exact observed

/-- Row observation is decided only by the Core row scan. -/
def observedDecidable (capability : Capability spec) (previous : Previous)
    (cls : spec.Class previous) : Decidable (Observed capability previous cls) :=
  if hasHit : (rowScan capability previous cls).HasHit then
    .isTrue (observed_of_rowHit capability previous cls hasHit)
  else
    .isFalse fun observed =>
      hasHit (rowHit_of_observed capability previous cls observed)

/-- Missingness is the exact complement of the Core-owned row observation. -/
def missingDecidable (capability : Capability spec) (previous : Previous)
    (cls : spec.Class previous) : Decidable (Missing capability previous cls) :=
  @instDecidableNot (Observed capability previous cls)
    (observedDecidable capability previous cls)

/-- Counted first-missing-class scan.  Its outer count records visited rows;
the primitive datum checks are accounted separately below. -/
def countedMissingScan (capability : Capability spec) (previous : Previous) :=
  Core.Finite.Accounting.countedRun (capability.classesAt previous)
    (Missing capability previous) (missingDecidable capability previous)

/-- Canonical first-missing-class search. -/
def missingScan (capability : Capability spec) (previous : Previous) :=
  (countedMissingScan capability previous).value

/-- Classes whose rows are actually visited by first-missing search. -/
def visitedClasses (capability : Capability spec) (previous : Previous) :
    List (spec.Class previous) :=
  match (missingScan capability previous).hit? with
  | some hit =>
      (capability.classesAt previous).values.take (hit.index.1 + 1)
  | none => (capability.classesAt previous).values

/-- Exact primitive datum inspections performed by first-missing search. -/
def missingRowChecks (capability : Capability spec)
    (previous : Previous) : Nat :=
  ((visitedClasses capability previous).map
    (rowChecks capability previous)).sum

/-- Core-owned route for direct-class search. -/
def routeDirect (capability : Capability spec) (previous : Previous) :=
  Core.Finite.Search.route (directScan capability previous)

/-- Core-owned route for first-missing search. -/
def routeMissing (capability : Capability spec) (previous : Previous) :=
  Core.Finite.Search.route (missingScan capability previous)

@[simp] theorem routeDirect_previous (capability : Capability spec)
    (previous : Previous) :
    (routeDirect capability previous).previous = directScan capability previous :=
  rfl

@[simp] theorem routeMissing_previous (capability : Capability spec)
    (previous : Previous) :
    (routeMissing capability previous).previous = missingScan capability previous :=
  rfl

theorem directChecks_le_classes (capability : Capability spec)
    (previous : Previous) :
    directChecks capability previous <= (capability.classesAt previous).card :=
  Core.Finite.Accounting.executionChecks_le_card
    (directScan capability previous)

theorem rowChecks_le_data (capability : Capability spec)
    (previous : Previous) (cls : spec.Class previous) :
    rowChecks capability previous cls <= (capability.dataAt previous).card :=
  Core.Finite.Accounting.executionChecks_le_card
    (rowScan capability previous cls)

private theorem sum_map_le_length_mul {alpha : Type uClass}
    (values : List alpha) (cost : alpha -> Nat) (bound : Nat)
    (bounded : forall value, value ∈ values -> cost value <= bound) :
    (values.map cost).sum <= values.length * bound := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        cost head + (tail.map cost).sum <=
            bound + tail.length * bound :=
          Nat.add_le_add (bounded head (by simp))
            (ih fun value member => bounded value (by simp [member]))
        _ = (tail.length + 1) * bound := by
          simp [Nat.add_mul, Nat.add_comm]

/-- First-missing row work is bounded by all declared rows times all data. -/
theorem missingRowChecks_le_product (capability : Capability spec)
    (previous : Previous) :
    missingRowChecks capability previous <=
      (capability.classesAt previous).card *
        (capability.dataAt previous).card := by
  apply Nat.le_trans
  · apply sum_map_le_length_mul
    intro cls member
    exact rowChecks_le_data capability previous cls
  · apply Nat.mul_le_mul_right (capability.dataAt previous).card
    unfold visitedClasses
    cases found : (missingScan capability previous).hit? with
    | none => rfl
    | some hit =>
        simp only [List.length_take, Core.Finite.Enumeration.card]
        exact Nat.min_le_right _ _

end Hypostructure.CT10
