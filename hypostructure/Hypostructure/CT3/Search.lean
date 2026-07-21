import Hypostructure.CT3.State

/-!
# CT3 finite reference scans

The three searches are ordinary Core first-hit scans over schedules retrieved
from the same predecessor: candidates, row-coordinate defects, and exact-row
matches.  CT3 supplies only the predicates and their primitive deciders.
-/

namespace Hypostructure.CT3

universe uPrevious uRepresentative uContext uCoordinate uValue uCandidate uRow

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue,
    uCandidate, uRow} Previous}

/-- Decide exact finite neutrality using Core's distinction classifier. -/
def scheduleNeutralityDecidable (capability : Capability spec)
    (previous : Previous) (replacement : spec.Representative) :
    Decidable (ScheduleNeutrality capability previous replacement) := by
  letI : DecidableEq spec.system.Value := capability.valueDecEq
  let table := responseTableAt capability previous replacement
  match (inferInstance : Decidable
      (Core.Response.FiniteTable.Distinguishes table)) with
  | .isTrue distinguishes =>
      exact .isFalse fun neutral => by
        obtain ⟨index, differs⟩ := distinguishes
        exact differs (neutral.equalAt index)
  | .isFalse absent =>
      exact .isTrue (table.neutralityOfNotDistinguishes absent)

/-- Decide all three candidate conditions independently of route selection. -/
def compressesDecidable (capability : Capability spec) (previous : Previous)
    (candidate : spec.Candidate) :
    Decidable (Compresses capability previous candidate) :=
  match capability.admissibleDecidable previous (capability.sourceAt previous)
      candidate with
  | .isFalse absent => .isFalse fun valid => absent valid.1
  | .isTrue admissible =>
      match capability.smallerDecidable previous (capability.sourceAt previous)
          candidate with
      | .isFalse absent => .isFalse fun valid => absent valid.2.1
      | .isTrue smaller =>
          match scheduleNeutralityDecidable capability previous
              (spec.candidatePiece candidate) with
          | .isFalse absent => .isFalse fun valid => absent valid.2.2
          | .isTrue neutral => .isTrue ⟨admissible, smaller, neutral⟩

/-- Canonical first valid candidate scan. -/
def compressionScan (capability : Capability spec) (previous : Previous) :
    Core.Finite.Search.Execution (capability.candidatesAt previous)
      (Compresses capability previous) :=
  Core.Finite.Search.run (capability.candidatesAt previous)
    (Compresses capability previous) (compressesDecidable capability previous)

/-- Primitive table-defect decision. -/
def tableDefectDecidable (capability : Capability spec) (previous : Previous)
    (entry : spec.Row × spec.system.Coordinate) :
    Decidable (TableDefect (spec := spec) previous entry) := by
  letI : DecidableEq spec.system.Value := capability.valueDecEq
  unfold TableDefect
  infer_instance

/-- Canonical first stored-bit defect scan. -/
def tableValidationScan (capability : Capability spec) (previous : Previous) :
    Core.Finite.Search.Execution (tablePairsAt capability previous)
      (TableDefect (spec := spec) previous) :=
  Core.Finite.Search.run (tablePairsAt capability previous)
    (TableDefect (spec := spec) previous)
    (tableDefectDecidable capability previous)

/-- Decide equality between the queried source vector and one stored row. -/
def rowMatchesDecidable (capability : Capability spec) (previous : Previous)
    (row : spec.Row) : Decidable (RowMatches capability previous row) := by
  letI : DecidableEq spec.system.Value := capability.valueDecEq
  unfold RowMatches
  infer_instance

/-- Canonical first exact-row lookup. -/
def rowLookupScan (capability : Capability spec) (previous : Previous) :
    Core.Finite.Search.Execution (capability.rowsAt previous)
      (RowMatches capability previous) :=
  Core.Finite.Search.run (capability.rowsAt previous)
    (RowMatches capability previous) (rowMatchesDecidable capability previous)

end Hypostructure.CT3
