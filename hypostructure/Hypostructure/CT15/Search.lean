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

/-- Route the exact counted first-drop scan through Core while retaining the
visible count produced by that same canonical execution. -/
def countedRouteDrop (capability : Capability spec) (previous : Previous) :
    Core.Counted (RoutedDrop capability previous) :=
  let scan := countedDropScan capability previous
  ⟨Core.Finite.Search.route scan.value, scan.checks⟩

/-- Route the exact first-drop scan through Core.  The semantic compatibility
entry point delegates to the counted route instead of rerunning the scan. -/
def routeDrop (capability : Capability spec) (previous : Previous) :
    RoutedDrop capability previous :=
  (countedRouteDrop capability previous).value

@[simp] theorem countedRouteDrop_checks (capability : Capability spec)
    (previous : Previous) :
    (countedRouteDrop capability previous).checks =
      (countedDropScan capability previous).checks :=
  rfl

@[simp] theorem countedRouteDrop_previous (capability : Capability spec)
    (previous : Previous) :
    (countedRouteDrop capability previous).value.previous =
      (countedDropScan capability previous).value :=
  rfl

/-- Two first-hit certificates for one duplicate-free schedule have the same
index. -/
private theorem indexedHit_index_eq {Coordinate : Type uCoordinate}
    {schedule : Core.Finite.Enumeration Coordinate}
    {predicate : Coordinate -> Prop}
    (left right : Core.Finite.Search.IndexedHit schedule predicate) :
    left.index = right.index := by
  apply Fin.ext
  by_contra unequal
  rcases lt_or_gt_of_ne unequal with leftBefore | rightBefore
  · have leftInPrefix :
        left.value ∈ schedule.values.take right.index.1 := by
      letI : DecidableEq Coordinate := schedule.decEq
      change schedule.values.get left.index ∈
        schedule.values.take right.index.1
      rw [List.mem_take_iff_idxOf_lt (List.get_mem _ _)]
      rw [List.get_idxOf schedule.nodup]
      exact leftBefore
    exact (right.first left.value leftInPrefix) left.sound
  · have rightInPrefix :
        right.value ∈ schedule.values.take left.index.1 := by
      letI : DecidableEq Coordinate := schedule.decEq
      change schedule.values.get right.index ∈
        schedule.values.take left.index.1
      rw [List.mem_take_iff_idxOf_lt (List.get_mem _ _)]
      rw [List.get_idxOf schedule.nodup]
      exact rightBefore
    exact (left.first right.value rightInPrefix) right.sound

/-- A hit branch pays exactly the visible prefix of the same canonical
counted execution. -/
theorem countedDropScan_checks_eq_hit
    (capability : Capability spec) (previous : Previous)
    (hasDrop : (countedDropScan capability previous).value.HasHit) :
    (countedDropScan capability previous).checks =
      (Core.Finite.Search.Execution.hitOfHasHit
        (countedDropScan capability previous).value hasDrop).index.1 + 1 := by
  simp only [countedDropScan, Core.Finite.Accounting.countedRun] at hasDrop ⊢
  cases found : (Core.Finite.Search.run
      (capability.coordinatesAt previous) (spec.TargetDependent previous)
      (capability.targetDependentDecidable previous)).hit? with
  | none => simp [Core.Finite.Search.Execution.HasHit, found] at hasDrop
  | some hit =>
      have selectedIndex :
          (Core.Finite.Search.Execution.hitOfHasHit
            (Core.Finite.Search.run
              (capability.coordinatesAt previous)
              (spec.TargetDependent previous)
              (capability.targetDependentDecidable previous))
            hasDrop).index = hit.index :=
        indexedHit_index_eq _ _
      simpa [selectedIndex] using
        (Core.Finite.Accounting.executionChecks_of_hit
          (Core.Finite.Search.run
            (capability.coordinatesAt previous) (spec.TargetDependent previous)
            (capability.targetDependentDecidable previous)) hit found)

/-- Every valid first-drop certificate has the unique index selected by the
canonical counted scan, so the stored scan count is its exact visible prefix. -/
theorem countedDropScan_checks_eq_certificate
    (capability : Capability spec) (previous : Previous)
    (certificate : RankDropCertificate capability previous) :
    (countedDropScan capability previous).checks =
      certificate.index.1 + 1 := by
  have hasDrop : (countedDropScan capability previous).value.HasHit := by
    change (Core.Finite.Search.run
      (capability.coordinatesAt previous) (spec.TargetDependent previous)
      (capability.targetDependentDecidable previous)).HasHit
    exact Core.Finite.Search.complete
      (capability.coordinatesAt previous) (spec.TargetDependent previous)
      (capability.targetDependentDecidable previous)
      ⟨certificate.value, certificate.member, certificate.sound⟩
  have scanChecks :=
    countedDropScan_checks_eq_hit capability previous hasDrop
  have sameIndex :
      ((countedDropScan capability previous).value.hitOfHasHit
        hasDrop).index = certificate.index :=
    indexedHit_index_eq _ _
  simpa [sameIndex] using scanChecks

/-- Exhaustive independence forces the retained canonical scan to inspect the
entire predecessor-owned schedule. -/
theorem countedDropScan_checks_eq_card_of_independence
    (capability : Capability spec) (previous : Previous)
    (independence : ExhaustiveIndependence capability previous) :
    (countedDropScan capability previous).checks =
      (capability.coordinatesAt previous).card := by
  have absent : (countedDropScan capability previous).value.hit? = none := by
    apply (Core.Finite.Search.hit?_eq_none_iff
      (capability.coordinatesAt previous) (spec.TargetDependent previous)
      (capability.targetDependentDecidable previous)).mpr
    intro coordinate member dependent
    obtain ⟨index, indexed⟩ :=
      ((capability.coordinatesAt previous).mem_iff_exists_index coordinate).mp
        member
    exact independence index (by simpa [indexed] using dependent)
  change Core.Finite.Accounting.executionChecks
    (countedDropScan capability previous).value =
      (capability.coordinatesAt previous).card
  exact Core.Finite.Accounting.executionChecks_of_miss
    (countedDropScan capability previous).value absent

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

/-- Count the one arithmetic capacity decision while retaining the exact
routed comparison used to select the terminal. -/
def countedCompareLedger (capability : Capability spec) (previous : Previous)
    {rank : RankState capability previous}
    {full : FullRankState capability previous rank}
    (ledger : ChargeLedger capability previous full) :
    Core.Counted (CapacityRoute capability previous ledger) :=
  ⟨compareLedger capability previous ledger, 1⟩

@[simp] theorem countedCompareLedger_checks
    (capability : Capability spec) (previous : Previous)
    {rank : RankState capability previous}
    {full : FullRankState capability previous rank}
    (ledger : ChargeLedger capability previous full) :
    (countedCompareLedger capability previous ledger).checks = 1 :=
  rfl

@[simp] theorem countedCompareLedger_previous
    (capability : Capability spec) (previous : Previous)
    {rank : RankState capability previous}
    {full : FullRankState capability previous rank}
    (ledger : ChargeLedger capability previous full) :
    (countedCompareLedger capability previous ledger).value.previous =
      ledger :=
  rfl

end Hypostructure.CT15
