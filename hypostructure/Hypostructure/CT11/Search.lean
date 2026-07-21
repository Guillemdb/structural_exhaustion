import Hypostructure.CT11.State
import Hypostructure.Core.Finite.Accounting
import Hypostructure.Core.Residual.Decision

/-!
# CT11 canonical searches and routing

Core performs both ordered first-hit scans.  The second scan's exhaustive
branch is impossible because the predecessor ledger supplies a strict-negative
sum certificate for the same queried schedule.
-/

namespace Hypostructure.CT11

universe uPrevious uCell

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uCell} Previous}

/-- Primitive decision that one scheduled cell is inadmissible. -/
def inadmissibleDecidable (capability : Capability spec)
    (previous : Previous) (cell : spec.Cell previous) :
    Decidable (Not (spec.Admissible previous cell)) :=
  match capability.admissibleDecidable previous cell with
  | .isTrue admissible => .isFalse fun inadmissible => inadmissible admissible
  | .isFalse inadmissible => .isTrue inadmissible

/-- Counted canonical first-inadmissible scan. -/
def countedAdmissibilityScan (capability : Capability spec)
    (previous : Previous) :
    Core.Counted (Core.Finite.Search.Execution
      (capability.cellsAt previous)
      (fun cell => Not (spec.Admissible previous cell))) :=
  Core.Finite.Accounting.countedRun (capability.cellsAt previous)
    (fun cell => Not (spec.Admissible previous cell))
    (inadmissibleDecidable capability previous)

/-- Proof-carrying canonical first-inadmissible scan. -/
def admissibilityScan (capability : Capability spec)
    (previous : Previous) :
    Core.Finite.Search.Execution (capability.cellsAt previous)
      (fun cell => Not (spec.Admissible previous cell)) :=
  (countedAdmissibilityScan capability previous).value

/-- Core-owned admissibility-gap versus admissible-decomposition route. -/
abbrev RoutedAdmissibility (capability : Capability spec)
    (previous : Previous) :=
  Core.Residual.Decision.Stage
    (fun execution : Core.Finite.Search.Execution
        (capability.cellsAt previous)
        (fun cell => Not (spec.Admissible previous cell)) =>
      execution.HasHit)
    (fun _execution : Core.Finite.Search.Execution
        (capability.cellsAt previous)
        (fun cell => Not (spec.Admissible previous cell)) =>
      AdmissibilityComplete capability previous)

/-- Route the exact residual-owned admissibility scan through Core. -/
def routeAdmissibility (capability : Capability spec)
    (previous : Previous) : RoutedAdmissibility capability previous :=
  Core.Finite.Search.route (admissibilityScan capability previous)

/-- Counted canonical first-negative-budget scan. -/
def countedNegativeScan (capability : Capability spec)
    (previous : Previous) :
    Core.Counted (Core.Finite.Search.Execution
      (capability.cellsAt previous)
      (fun cell => spec.localBudget previous cell < 0)) :=
  Core.Finite.Accounting.countedRun (capability.cellsAt previous)
    (fun cell => spec.localBudget previous cell < 0)
    (fun _cell => inferInstance)

/-- Proof-carrying canonical first-negative-budget scan. -/
def negativeScan (capability : Capability spec) (previous : Previous) :
    Core.Finite.Search.Execution (capability.cellsAt previous)
      (fun cell => spec.localBudget previous cell < 0) :=
  (countedNegativeScan capability previous).value

/-- Core-owned localized-deficit versus all-nonnegative route. -/
abbrev RoutedNegative (capability : Capability spec)
    (previous : Previous) :=
  Core.Residual.Decision.Stage
    (fun execution : Core.Finite.Search.Execution
        (capability.cellsAt previous)
        (fun cell => spec.localBudget previous cell < 0) =>
      execution.HasHit)
    (fun _execution : Core.Finite.Search.Execution
        (capability.cellsAt previous)
        (fun cell => spec.localBudget previous cell < 0) =>
      NoNegativeCell capability previous)

/-- Route the exact residual-owned budget scan through Core. -/
def routeNegative (capability : Capability spec)
    (previous : Previous) : RoutedNegative capability previous :=
  Core.Finite.Search.route (negativeScan capability previous)

/-- Exhaustive nonnegativity contradicts the registered strict-negative sum. -/
theorem noNegativeCell_false (capability : Capability spec)
    (previous : Previous) (noNegative : NoNegativeCell capability previous) :
    False := by
  have pointwise : forall cell,
      cell ∈ (capability.cellsAt previous).values ->
        0 <= spec.localBudget previous cell := by
    intro cell member
    obtain ⟨index, indexed⟩ :=
      ((capability.cellsAt previous).mem_iff_exists_index cell).mp member
    apply le_of_not_gt
    intro negative
    exact noNegative index (by simpa [indexed] using negative)
  have totalNonnegative : 0 <=
      ((capability.cellsAt previous).values.map
        (spec.localBudget previous)).sum := by
    apply List.sum_nonneg
    intro value member
    simp only [List.mem_map] at member
    obtain ⟨cell, cellMember, rfl⟩ := member
    exact pointwise cell cellMember
  exact (not_lt_of_ge totalNonnegative)
    (capability.negativeTotalAt previous)

end Hypostructure.CT11
