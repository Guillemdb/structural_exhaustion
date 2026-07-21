import Hypostructure.CT3.Capability

/-!
# CT3 proof states

All certificates are specializations of Core exact tables and finite-search
certificates.  CT3 introduces no application-owned carrier or replacement
collection.
-/

namespace Hypostructure.CT3

universe uPrevious uRepresentative uContext uCoordinate uValue uCandidate uRow

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue,
    uCandidate, uRow} Previous}

/-- Core's exact table comparing the queried source with one replacement. -/
def responseTableAt (capability : Capability spec) (previous : Previous)
    (replacement : spec.Representative) :=
  Core.Response.FiniteTable.Table.build spec.system
    (spec.representatives (capability.sourceAt previous) replacement)
    (capability.exactScheduleAt previous)

/-- Exact equality at every coordinate owned by the predecessor residual. -/
abbrev ScheduleNeutrality (capability : Capability spec) (previous : Previous)
    (replacement : spec.Representative) :=
  Core.Response.FiniteTable.Neutrality
    (responseTableAt capability previous replacement)

/-- A scheduled candidate is admissible, strictly smaller, and exactly neutral
on every residual-owned coordinate. -/
def Compresses (capability : Capability spec) (previous : Previous)
    (candidate : spec.Candidate) : Prop :=
  spec.Admissible previous (capability.sourceAt previous) candidate ∧
    spec.StrictlySmaller previous (capability.sourceAt previous) candidate ∧
      ScheduleNeutrality capability previous (spec.candidatePiece candidate)

/-- Framework-produced first valid compression candidate. -/
abbrev CompressionCertificate (capability : Capability spec)
    (previous : Previous) :=
  Core.Finite.Search.IndexedHit (capability.candidatesAt previous)
    (Compresses capability previous)

/-- Exhaustive compression failure on the exact queried candidate schedule. -/
abbrev UncompressibleState (capability : Capability spec)
    (previous : Previous) :=
  Core.Finite.Search.Avoids (capability.candidatesAt previous)
    (Compresses capability previous)

/-- Framework-owned row/coordinate product used for table validation. -/
def tablePairsAt (capability : Capability spec) (previous : Previous) :
    Core.Finite.Enumeration (spec.Row × spec.system.Coordinate) :=
  (capability.rowsAt previous).product (capability.coordinatesAt previous)

/-- A stored table bit disagrees with the exact representative response. -/
def TableDefect (_previous : Previous)
    (entry : spec.Row × spec.system.Coordinate) :
    Prop :=
  spec.system.coordinateResponse (spec.rowPiece entry.1) entry.2 ≠
    spec.rowResponse entry.1 entry.2

/-- First table defect in row-major, coordinate-minor order. -/
abbrev DistinguishingCoordinate (capability : Capability spec)
    (previous : Previous) :=
  Core.Finite.Search.IndexedHit (tablePairsAt capability previous)
    (TableDefect (spec := spec) previous)

/-- Exhaustive exactness of every stored bit in the queried row schedule. -/
abbrev ExactTableState (capability : Capability spec)
    (previous : Previous) :=
  Core.Finite.Search.Avoids (tablePairsAt capability previous)
    (TableDefect (spec := spec) previous)

/-- The queried source vector equals one stored row on every queried
coordinate. -/
def RowMatches (capability : Capability spec) (previous : Previous)
    (row : spec.Row) : Prop :=
  forall index : Fin (capability.coordinatesAt previous).card,
    spec.system.coordinateResponse (capability.sourceAt previous)
        ((capability.coordinatesAt previous).get index) =
      spec.rowResponse row ((capability.coordinatesAt previous).get index)

/-- First row matching the queried source vector. -/
abbrev KnownRowCertificate (capability : Capability spec)
    (previous : Previous) :=
  Core.Finite.Search.IndexedHit (capability.rowsAt previous)
    (RowMatches capability previous)

/-- Exhaustive absence of the source vector from the queried row schedule. -/
abbrev NovelRowState (capability : Capability spec) (previous : Previous) :=
  Core.Finite.Search.Avoids (capability.rowsAt previous)
    (RowMatches capability previous)

namespace CompressionCertificate

/-- Candidate selected by the canonical first-hit search. -/
def candidate {capability : Capability spec} {previous : Previous}
    (certificate : CompressionCertificate capability previous) : spec.Candidate :=
  certificate.value

/-- The selected candidate belongs to the exact incoming schedule. -/
theorem scheduled {capability : Capability spec} {previous : Previous}
    (certificate : CompressionCertificate capability previous) :
    certificate.candidate ∈ (capability.candidatesAt previous).values :=
  Core.Finite.Search.IndexedHit.member certificate

/-- Complete structural and finite-neutrality evidence for the candidate. -/
theorem valid {capability : Capability spec} {previous : Previous}
    (certificate : CompressionCertificate capability previous) :
    Compresses capability previous certificate.candidate :=
  certificate.sound

/-- Finite neutrality plus registered symbolic coverage yields target
equivalence in every semantic context. -/
def targetComplete {capability : Capability spec} {previous : Previous}
    (certificate : CompressionCertificate capability previous) :
    Core.Response.TargetCompleteEquivalence spec.semantics
      (spec.representatives (capability.sourceAt previous)
        (spec.candidatePiece certificate.candidate)) :=
  certificate.valid.2.2.targetComplete
    (capability.candidateCoverage previous certificate.candidate
      certificate.scheduled)
    spec.semantics

end CompressionCertificate

namespace DistinguishingCoordinate

/-- Defective row selected by the exact product scan. -/
def row {capability : Capability spec} {previous : Previous}
    (certificate : DistinguishingCoordinate capability previous) : spec.Row :=
  certificate.value.1

/-- Defective coordinate selected by the exact product scan. -/
def coordinate {capability : Capability spec} {previous : Previous}
    (certificate : DistinguishingCoordinate capability previous) :
    spec.system.Coordinate :=
  certificate.value.2

theorem row_member {capability : Capability spec} {previous : Previous}
    (certificate : DistinguishingCoordinate capability previous) :
    certificate.row ∈ (capability.rowsAt previous).values := by
  have member := certificate.member
  exact (Core.Finite.Enumeration.mem_product_values
    (capability.rowsAt previous) (capability.coordinatesAt previous)
      certificate.value).mp member |>.1

theorem coordinate_member {capability : Capability spec} {previous : Previous}
    (certificate : DistinguishingCoordinate capability previous) :
    certificate.coordinate ∈ (capability.coordinatesAt previous).values := by
  have member := certificate.member
  exact (Core.Finite.Enumeration.mem_product_values
    (capability.rowsAt previous) (capability.coordinatesAt previous)
      certificate.value).mp member |>.2

/-- The selected stored bit is genuinely wrong. -/
theorem differs {capability : Capability spec} {previous : Previous}
    (certificate : DistinguishingCoordinate capability previous) :
    spec.system.coordinateResponse (spec.rowPiece certificate.row)
        certificate.coordinate ≠
      spec.rowResponse certificate.row certificate.coordinate :=
  certificate.sound

end DistinguishingCoordinate

namespace ExactTableState

/-- Every scheduled row bit agrees with its representative's exact response. -/
theorem equalAt {capability : Capability spec} {previous : Previous}
    (table : ExactTableState capability previous)
    {row : spec.Row} (rowMember : row ∈ (capability.rowsAt previous).values)
    {coordinate : spec.system.Coordinate}
    (coordinateMember : coordinate ∈ (capability.coordinatesAt previous).values) :
    spec.system.coordinateResponse (spec.rowPiece row) coordinate =
      spec.rowResponse row coordinate := by
  by_contra differs
  have pairMember : (row, coordinate) ∈
      (tablePairsAt capability previous).values := by
    exact (Core.Finite.Enumeration.mem_product_values
      (capability.rowsAt previous) (capability.coordinatesAt previous)
        (row, coordinate)).mpr ⟨rowMember, coordinateMember⟩
  obtain ⟨index, indexed⟩ :=
    ((tablePairsAt capability previous).mem_iff_exists_index
      (row, coordinate)).mp pairMember
  exact table index (by
    simpa [TableDefect, indexed] using differs)

end ExactTableState

namespace KnownRowCertificate

/-- Row selected by canonical exact-row lookup. -/
def row {capability : Capability spec} {previous : Previous}
    (certificate : KnownRowCertificate capability previous) : spec.Row :=
  certificate.value

theorem scheduled {capability : Capability spec} {previous : Previous}
    (certificate : KnownRowCertificate capability previous) :
    certificate.row ∈ (capability.rowsAt previous).values :=
  Core.Finite.Search.IndexedHit.member certificate

theorem rowMatches {capability : Capability spec} {previous : Previous}
    (certificate : KnownRowCertificate capability previous) :
    RowMatches capability previous certificate.row :=
  certificate.sound

/-- A validated known row is finitely neutral with its represented piece. -/
def neutrality {capability : Capability spec} {previous : Previous}
    (table : ExactTableState capability previous)
    (certificate : KnownRowCertificate capability previous) :
    ScheduleNeutrality capability previous (spec.rowPiece certificate.row) where
  equalAt := by
    intro index
    let coordinate := (capability.coordinatesAt previous).get index
    have coordinateMember : coordinate ∈
        (capability.coordinatesAt previous).values :=
      (capability.coordinatesAt previous).get_mem index
    have sourceExact :=
      (responseTableAt capability previous
        (spec.rowPiece certificate.row)).sourceExact index
    have replacementExact :=
      (responseTableAt capability previous
        (spec.rowPiece certificate.row)).replacementExact index
    calc
      (responseTableAt capability previous
          (spec.rowPiece certificate.row)).sourceVector index =
          spec.system.coordinateResponse (capability.sourceAt previous)
            coordinate := sourceExact
      _ = spec.rowResponse certificate.row coordinate :=
        certificate.rowMatches index
      _ = spec.system.coordinateResponse (spec.rowPiece certificate.row)
            coordinate :=
        (table.equalAt certificate.scheduled coordinateMember).symm
      _ = (responseTableAt capability previous
          (spec.rowPiece certificate.row)).replacementVector index :=
        replacementExact.symm

/-- Exact row validation and lookup yield target equivalence in every semantic
context. -/
def targetComplete {capability : Capability spec} {previous : Previous}
    (table : ExactTableState capability previous)
    (certificate : KnownRowCertificate capability previous) :
    Core.Response.TargetCompleteEquivalence spec.semantics
      (spec.representatives (capability.sourceAt previous)
        (spec.rowPiece certificate.row)) :=
  (certificate.neutrality table).targetComplete
    (capability.rowCoverage previous certificate.row certificate.scheduled)
    spec.semantics

end KnownRowCertificate

namespace NovelRowState

/-- No member of the exact queried row schedule matches the source vector. -/
theorem noMatch {capability : Capability spec} {previous : Previous}
    (state : NovelRowState capability previous) (row : spec.Row)
    (member : row ∈ (capability.rowsAt previous).values) :
    Not (RowMatches capability previous row) := by
  obtain ⟨index, indexed⟩ :=
    ((capability.rowsAt previous).mem_iff_exists_index row).mp member
  exact fun exactMatch => state index (by simpa [indexed] using exactMatch)

end NovelRowState

end Hypostructure.CT3
