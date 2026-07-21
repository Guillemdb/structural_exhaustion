import Hypostructure.CT11.Capability
import Hypostructure.Core.Finite.Search

/-!
# CT11 generated residual states

The two public residual kinds are generated from Core search certificates.
Their constructors are private, so callers cannot preselect a cell or author
an admissible decomposition independently of the canonical scans.
-/

namespace Hypostructure.CT11

universe uPrevious uCell

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uCell} Previous}

/-- Canonical first inadmissible cell and its clean prefix. -/
abbrev AdmissibilityGapResidual (capability : Capability spec)
    (previous : Previous) :=
  Core.Finite.Search.IndexedHit (capability.cellsAt previous)
    (fun cell => Not (spec.Admissible previous cell))

/-- Exhaustive absence of an inadmissible cell in the exact incoming order. -/
abbrev AdmissibilityComplete (capability : Capability spec)
    (previous : Previous) :=
  Core.Finite.Search.Avoids (capability.cellsAt previous)
    (fun cell => Not (spec.Admissible previous cell))

/-- Framework-generated proof that every scheduled cell is admissible. -/
structure AdmissibleDecomposition (capability : Capability spec)
    (previous : Previous) : Prop where
  private mk ::
  admissible : forall cell,
    cell ∈ (capability.cellsAt previous).values ->
      spec.Admissible previous cell

/-- Convert Core's exhaustive admissibility scan into its semantic state. -/
def buildAdmissibleDecomposition (capability : Capability spec)
    (previous : Previous)
    (complete : AdmissibilityComplete capability previous) :
    AdmissibleDecomposition capability previous :=
  .mk (by
    intro cell member
    match capability.admissibleDecidable previous cell with
    | .isTrue admissible => exact admissible
    | .isFalse inadmissible =>
        obtain ⟨index, indexed⟩ :=
          ((capability.cellsAt previous).mem_iff_exists_index cell).mp member
        exact (complete index (by simpa [indexed] using inadmissible)).elim)

/-- Exhaustive absence of a locally negative budget entry. -/
abbrev NoNegativeCell (capability : Capability spec)
    (previous : Previous) :=
  Core.Finite.Search.Avoids (capability.cellsAt previous)
    (fun cell => spec.localBudget previous cell < 0)

/-- Canonical first locally negative cell after admissibility has closed. -/
structure LocalizedDeficitResidual (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  admissible : AdmissibleDecomposition capability previous
  hit : Core.Finite.Search.IndexedHit (capability.cellsAt previous)
    (fun cell => spec.localBudget previous cell < 0)

/-- Build the localized residual solely from the two framework scans. -/
def buildLocalizedDeficit (capability : Capability spec)
    (previous : Previous)
    (admissible : AdmissibleDecomposition capability previous)
    (hit : Core.Finite.Search.IndexedHit (capability.cellsAt previous)
      (fun cell => spec.localBudget previous cell < 0)) :
    LocalizedDeficitResidual capability previous :=
  .mk admissible hit

end Hypostructure.CT11
