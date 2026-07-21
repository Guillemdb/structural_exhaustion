import Hypostructure.CT15.State
import Hypostructure.Core.Finite.Accounting

/-!
# CT15 reference searches and decisions

Core performs the canonical first-hit scan and both binary routes.  CT15 adds
only its rank and capacity semantics to those generic executors.
-/

namespace Hypostructure.CT15

universe uPrevious uCoordinate

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uCoordinate} Previous}

theorem rankContribution_independent (capability : Capability spec)
    (previous : Previous) (coordinate : spec.Coordinate previous)
    (independent : Not (spec.TargetDependent previous coordinate)) :
    rankContribution capability previous coordinate = 1 := by
  unfold rankContribution
  cases decision : capability.targetDependentDecidable previous coordinate with
  | isTrue dependent => exact (independent dependent).elim
  | isFalse _ => rfl

/-- Every primitive coordinate contributes at most one rank unit. -/
theorem rankContribution_le_one (capability : Capability spec)
    (previous : Previous) (coordinate : spec.Coordinate previous) :
    rankContribution capability previous coordinate <= 1 := by
  unfold rankContribution
  cases capability.targetDependentDecidable previous coordinate <;> simp

/-- Computed target-relative rank cannot exceed the exact queried family. -/
theorem computedRank_le_targetRank (capability : Capability spec)
    (previous : Previous) :
    computedRank capability previous <= targetRank capability previous := by
  unfold computedRank targetRank
  let coordinates := (capability.coordinatesAt previous).values
  change (coordinates.map (rankContribution capability previous)).sum <=
    coordinates.length
  induction coordinates with
  | nil => simp
  | cons coordinate rest inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have contributionBound :=
        rankContribution_le_one capability previous coordinate
      omega

/-- Exhaustive scheduled independence forces literal full rank. -/
theorem computedRank_eq_targetRank (capability : Capability spec)
    (previous : Previous)
    (independent : forall coordinate,
      coordinate ∈ (capability.coordinatesAt previous).values ->
        Not (spec.TargetDependent previous coordinate)) :
    computedRank capability previous = targetRank capability previous := by
  unfold computedRank targetRank
  let coordinates := (capability.coordinatesAt previous).values
  change (coordinates.map (rankContribution capability previous)).sum =
    coordinates.length
  have allIndependent : forall coordinate, coordinate ∈ coordinates ->
      Not (spec.TargetDependent previous coordinate) := by
    simpa [coordinates] using independent
  have mapped :
      coordinates.map (rankContribution capability previous) =
        coordinates.map (fun _coordinate => 1) :=
    List.map_congr_left fun coordinate member =>
      rankContribution_independent capability previous coordinate
        (allIndependent coordinate member)
  rw [mapped]
  simp

/-- Canonical counted first-drop scan over the exact queried schedule. -/
def countedDropScan (capability : Capability spec) (previous : Previous) :
    Core.Counted (Core.Finite.Search.Execution
      (capability.coordinatesAt previous) (spec.TargetDependent previous)) :=
  Core.Finite.Accounting.countedRun (capability.coordinatesAt previous)
    (spec.TargetDependent previous)
    (capability.targetDependentDecidable previous)

/-- Proof-carrying first-drop scan. -/
def dropScan (capability : Capability spec) (previous : Previous) :
    Core.Finite.Search.Execution (capability.coordinatesAt previous)
      (spec.TargetDependent previous) :=
  (countedDropScan capability previous).value

/-- Core-owned first-drop decision route. -/
abbrev RoutedDrop (capability : Capability spec) (previous : Previous) :=
  Core.Residual.Decision.Stage
    (fun execution : Core.Finite.Search.Execution
        (capability.coordinatesAt previous) (spec.TargetDependent previous) =>
      execution.HasHit)
    (fun _execution : Core.Finite.Search.Execution
        (capability.coordinatesAt previous) (spec.TargetDependent previous) =>
      ExhaustiveIndependence capability previous)

/-- Route the exact first-drop scan through Core. -/
def routeDrop (capability : Capability spec) (previous : Previous) :
    RoutedDrop capability previous :=
  Core.Finite.Search.route (dropScan capability previous)

/-- Turn Core's exhaustive miss into the generated full-rank state. -/
def fullRankOfIndependence (capability : Capability spec)
    (previous : Previous) (rank : RankState capability previous)
    (independence : ExhaustiveIndependence capability previous) :
    FullRankState capability previous rank := by
  have noDependent : forall coordinate,
      coordinate ∈ (capability.coordinatesAt previous).values ->
        Not (spec.TargetDependent previous coordinate) := by
    intro coordinate member
    obtain ⟨index, indexed⟩ :=
      ((capability.coordinatesAt previous).mem_iff_exists_index coordinate).mp
        member
    exact fun dependent => independence index (by simpa [indexed] using dependent)
  exact {
    independence := independence
    full := rank.computed.trans
      (computedRank_eq_targetRank capability previous noDependent)
  }

/-- Core-owned arithmetic capacity route on the generated ledger. -/
abbrev CapacityRoute (capability : Capability spec) (previous : Previous)
    {rank : RankState capability previous}
    {full : FullRankState capability previous rank}
    (_ledger : ChargeLedger capability previous full) :=
  Core.Residual.Decision.Stage
    (fun current : ChargeLedger capability previous full =>
      C4Certificate capability previous current)
    (fun current : ChargeLedger capability previous full =>
      FullRankLedgerResidual capability previous current)

/-- Register the exact overload-versus-capacity comparison. -/
def capacityDecisionNode (capability : Capability spec) (previous : Previous)
    {rank : RankState capability previous}
    {full : FullRankState capability previous rank} :
    Core.Residual.Decision.Node
      (ChargeLedger capability previous full)
      (fun ledger => C4Certificate capability previous ledger)
      (fun ledger => FullRankLedgerResidual capability previous ledger) :=
  Core.Residual.Decision.Node.create
    (fun ledger => Nat.decLt (spec.capacity previous) ledger.total)
    (by
      intro ledger notExceeded
      omega)

/-- Compare the exact generated ledger through Core's binary executor. -/
def compareLedger (capability : Capability spec) (previous : Previous)
    {rank : RankState capability previous}
    {full : FullRankState capability previous rank}
    (ledger : ChargeLedger capability previous full) :
    CapacityRoute capability previous ledger :=
  (capacityDecisionNode capability previous).run ledger

end Hypostructure.CT15
