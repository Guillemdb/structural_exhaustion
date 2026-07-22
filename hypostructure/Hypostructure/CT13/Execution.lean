import Hypostructure.CT13.Search

/-!
# CT13 accumulated execution

The reference machine owns every computation and decision.  A completed run
adds one private routed value to the literal predecessor ledger; intermediate
search stages are not exposed as application-authored handoffs.
-/

namespace Hypostructure.CT13

universe uPrevious uPayer uObstruction uResource

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uPayer, uObstruction, uResource} Previous}

/-- Exhaustive CT13 terminals. -/
inductive Terminal where
  | tierOne
  | overlap
  | deficit
  | reconciled
  deriving DecidableEq, Repr

/-- Audit nodes in canonical CT13 execution order. -/
inductive NodeId where
  | entry
  | payerSchedule
  | tierOneSearch
  | obstructionSchedule
  | fallbackSelection
  | tierTwoSchedule
  | overlapSearch
  | reconciliationLedger
  | comparison
  | tierOneTerminal
  | overlapTerminal
  | deficitTerminal
  | reconciledTerminal
  deriving DecidableEq, Repr

/-- Framework-generated terminal evidence. -/
inductive Outcome (capability : Capability spec) (previous : Previous) :
    Terminal -> Type _ where
  | tierOne (residual : TierOneResidual capability previous) :
      Outcome capability previous .tierOne
  | overlap (residual : OverlapResidual capability previous) :
      Outcome capability previous .overlap
  | deficit (residual : DeficitResidual capability previous) :
      Outcome capability previous .deficit
  | reconciled
      (certificate : ReconciliationCertificate capability previous) :
      Outcome capability previous .reconciled

namespace Outcome

/-- Observable canonical fallback, absent only on the tier-one terminal. -/
def selectedFallback? {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal ->
      Option (spec.Obstruction previous)
  | .tierOne, .tierOne _residual => none
  | .overlap, .overlap residual => some residual.fallback.selected
  | .deficit, .deficit residual => some residual.ledger.fallback.selected
  | .reconciled, .reconciled certificate =>
      some certificate.ledger.fallback.selected

/-- Observable first overlap index, present only on the overlap terminal. -/
def overlapIndex? {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal -> Option Nat
  | .overlap, .overlap residual => some residual.hit.index.1
  | .tierOne, .tierOne _ => none
  | .deficit, .deficit _ => none
  | .reconciled, .reconciled _ => none

/-- Observable first overlapping payer pair. -/
def overlapPair? {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal ->
      Option (spec.Payer previous × spec.Payer previous)
  | .overlap, .overlap residual => some residual.hit.value
  | .tierOne, .tierOne _ => none
  | .deficit, .deficit _ => none
  | .reconciled, .reconciled _ => none

end Outcome

/-- Terminal-indexed canonical CT13 trace. -/
inductive Trace : Terminal -> Type where
  | tierOne : Trace .tierOne
  | overlap : Trace .overlap
  | deficit : Trace .deficit
  | reconciled : Trace .reconciled

namespace Trace

/-- Observable node order of a typed trace. -/
def nodes : {terminal : Terminal} -> Trace terminal -> List NodeId
  | .tierOne, .tierOne =>
      [.entry, .payerSchedule, .tierOneSearch, .tierOneTerminal]
  | .overlap, .overlap =>
      [.entry, .payerSchedule, .tierOneSearch, .obstructionSchedule,
        .fallbackSelection, .tierTwoSchedule, .overlapSearch,
        .overlapTerminal]
  | .deficit, .deficit =>
      [.entry, .payerSchedule, .tierOneSearch, .obstructionSchedule,
        .fallbackSelection, .tierTwoSchedule, .overlapSearch,
        .reconciliationLedger, .comparison, .deficitTerminal]
  | .reconciled, .reconciled =>
      [.entry, .payerSchedule, .tierOneSearch, .obstructionSchedule,
        .fallbackSelection, .tierTwoSchedule, .overlapSearch,
        .reconciliationLedger, .comparison, .reconciledTerminal]

/-- Canonical node sequence fixed by a terminal. -/
def expectedNodes : Terminal -> List NodeId
  | .tierOne =>
      [.entry, .payerSchedule, .tierOneSearch, .tierOneTerminal]
  | .overlap =>
      [.entry, .payerSchedule, .tierOneSearch, .obstructionSchedule,
        .fallbackSelection, .tierTwoSchedule, .overlapSearch,
        .overlapTerminal]
  | .deficit =>
      [.entry, .payerSchedule, .tierOneSearch, .obstructionSchedule,
        .fallbackSelection, .tierTwoSchedule, .overlapSearch,
        .reconciliationLedger, .comparison, .deficitTerminal]
  | .reconciled =>
      [.entry, .payerSchedule, .tierOneSearch, .obstructionSchedule,
        .fallbackSelection, .tierTwoSchedule, .overlapSearch,
        .reconciliationLedger, .comparison, .reconciledTerminal]

theorem nodes_eq_expected : {terminal : Terminal} ->
    (trace : Trace terminal) -> trace.nodes = expectedNodes terminal
  | .tierOne, .tierOne => rfl
  | .overlap, .overlap => rfl
  | .deficit, .deficit => rfl
  | .reconciled, .reconciled => rfl

end Trace

/-- Private framework route selected by the deterministic reference machine. -/
structure Routed (capability : Capability spec) (previous : Previous) where
  private mk ::
  terminal : Terminal
  outcome : Outcome capability previous terminal

/-- Unique typed trace selected by generated outcome evidence. -/
def traceOfOutcome {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal) :
    Trace terminal := by
  cases outcome with
  | tierOne _ => exact .tierOne
  | overlap _ => exact .overlap
  | deficit _ => exact .deficit
  | reconciled _ => exact .reconciled

/-- Unique typed trace selected by a private routed result. -/
def traceOfRouted {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous) : Trace routed.terminal :=
  traceOfOutcome routed.outcome

/-- Exact primitive checks performed on each terminal branch. -/
def outcomeChecks {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal -> Nat
  | .tierOne, .tierOne residual => residual.index.1 + 1
  | .overlap, .overlap residual =>
      (capability.payersAt previous).card +
        (capability.obstructionsAt previous).comparisonCount +
          residual.hit.index.1 + 1
  | .deficit, .deficit residual =>
      let tierTwo := selectedTierTwo capability previous
        residual.ledger.fallback
      (capability.payersAt previous).card +
        (capability.obstructionsAt previous).comparisonCount +
          tierTwo.card * tierTwo.card + tierTwo.card + 1
  | .reconciled, .reconciled certificate =>
      let tierTwo := selectedTierTwo capability previous
        certificate.ledger.fallback
      (capability.payersAt previous).card +
        (capability.obstructionsAt previous).comparisonCount +
          tierTwo.card * tierTwo.card + tierTwo.card + 1

/-- Branch-exact work is bounded by the complete inherited schedule envelope. -/
theorem outcomeChecks_le_limit {capability : Capability spec}
    {previous : Previous} {terminal : Terminal}
    (outcome : Outcome capability previous terminal) :
    outcomeChecks outcome <=
      localCheckBound (capability.payersAt previous)
        (capability.obstructionsAt previous)
        (capability.tierTwo.read previous) := by
  cases outcome with
  | tierOne residual =>
      have inspected : residual.index.1 + 1 <=
          (capability.payersAt previous).card :=
        Nat.succ_le_iff.mpr residual.index.isLt
      simp only [outcomeChecks, localCheckBound]
      omega
  | overlap residual =>
      have inspected : residual.hit.index.1 + 1 <=
          (reconciliationPairs capability previous residual.fallback).card :=
        Nat.succ_le_iff.mpr residual.hit.index.isLt
      have tierLe := selectedTierTwo_card_le_sum capability previous
        residual.fallback
      have squareLe :
          (selectedTierTwo capability previous residual.fallback).card *
              (selectedTierTwo capability previous residual.fallback).card <=
            capability.tierTwoCardSumAt previous *
              capability.tierTwoCardSumAt previous :=
        Nat.mul_le_mul tierLe tierLe
      have pairInspected : residual.hit.index.1 + 1 <=
          (selectedTierTwo capability previous residual.fallback).card *
            (selectedTierTwo capability previous residual.fallback).card := by
        change residual.hit.index.1 + 1 <=
          ((selectedTierTwo capability previous residual.fallback).product
            (selectedTierTwo capability previous residual.fallback)).card at inspected
        rw [Core.Finite.Enumeration.card_product] at inspected
        exact inspected
      simp only [outcomeChecks, localCheckBound]
      change _ <= (capability.payersAt previous).card +
        (capability.obstructionsAt previous).comparisonCount +
          capability.tierTwoCardSumAt previous *
            capability.tierTwoCardSumAt previous +
          capability.tierTwoCardSumAt previous + 1
      omega
  | deficit residual =>
      have tierLe := selectedTierTwo_card_le_sum capability previous
        residual.ledger.fallback
      have squareLe :
          (selectedTierTwo capability previous residual.ledger.fallback).card *
              (selectedTierTwo capability previous residual.ledger.fallback).card <=
            capability.tierTwoCardSumAt previous *
              capability.tierTwoCardSumAt previous :=
        Nat.mul_le_mul tierLe tierLe
      simp only [outcomeChecks, localCheckBound]
      change _ <= (capability.payersAt previous).card +
        (capability.obstructionsAt previous).comparisonCount +
          capability.tierTwoCardSumAt previous *
            capability.tierTwoCardSumAt previous +
          capability.tierTwoCardSumAt previous + 1
      omega
  | reconciled certificate =>
      have tierLe := selectedTierTwo_card_le_sum capability previous
        certificate.ledger.fallback
      have squareLe :
          (selectedTierTwo capability previous certificate.ledger.fallback).card *
              (selectedTierTwo capability previous certificate.ledger.fallback).card <=
            capability.tierTwoCardSumAt previous *
              capability.tierTwoCardSumAt previous :=
        Nat.mul_le_mul tierLe tierLe
      simp only [outcomeChecks, localCheckBound]
      change _ <= (capability.payersAt previous).card +
        (capability.obstructionsAt previous).comparisonCount +
          capability.tierTwoCardSumAt previous *
            capability.tierTwoCardSumAt previous +
          capability.tierTwoCardSumAt previous + 1
      omega

namespace Routed

/-- Exact trace derived from the generated terminal evidence. -/
def trace {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous) : Trace routed.terminal :=
  traceOfRouted routed

/-- Observable canonical trace nodes of an output-only routed value. -/
def traceNodes {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous) : List NodeId :=
  routed.trace.nodes

/-- Exact primitive work attached to the generated semantic outcome. -/
def checks {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous) : Nat :=
  outcomeChecks routed.outcome

/-- Recover tier-one evidence only after the generated terminal identifies
that branch. -/
def tierOneEvidence {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous)
    (isTierOne : routed.terminal = .tierOne) :
    TierOneResidual capability previous := by
  rcases routed with ⟨terminal, outcome⟩
  cases outcome with
  | tierOne residual => exact residual
  | overlap _ => cases isTierOne
  | deficit _ => cases isTierOne
  | reconciled _ => cases isTierOne

/-- Recover overlap evidence only from the generated overlap terminal. -/
def overlapEvidence {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous)
    (isOverlap : routed.terminal = .overlap) :
    OverlapResidual capability previous := by
  rcases routed with ⟨terminal, outcome⟩
  cases outcome with
  | tierOne _ => cases isOverlap
  | overlap residual => exact residual
  | deficit _ => cases isOverlap
  | reconciled _ => cases isOverlap

/-- Recover the exact generated deficit ledger only from its terminal. -/
def deficitEvidence {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous)
    (isDeficit : routed.terminal = .deficit) :
    DeficitResidual capability previous := by
  rcases routed with ⟨terminal, outcome⟩
  cases outcome with
  | tierOne _ => cases isDeficit
  | overlap _ => cases isDeficit
  | deficit residual => exact residual
  | reconciled _ => cases isDeficit

/-- Recover the exact generated reconciliation certificate only from its
terminal. -/
def reconciliationEvidence {capability : Capability spec}
    {previous : Previous} (routed : Routed capability previous)
    (isReconciled : routed.terminal = .reconciled) :
    ReconciliationCertificate capability previous := by
  rcases routed with ⟨terminal, outcome⟩
  cases outcome with
  | tierOne _ => cases isReconciled
  | overlap _ => cases isReconciled
  | deficit _ => cases isReconciled
  | reconciled certificate => exact certificate

/-- Tier-one generation pays exactly the first eligible prefix. -/
theorem checks_eq_tierOne {capability : Capability spec}
    {previous : Previous} (routed : Routed capability previous)
    (isTierOne : routed.terminal = .tierOne) :
    routed.checks = (routed.tierOneEvidence isTierOne).index.1 + 1 := by
  rcases routed with ⟨terminal, outcome⟩
  cases outcome with
  | tierOne _ => rfl
  | overlap _ => cases isTierOne
  | deficit _ => cases isTierOne
  | reconciled _ => cases isTierOne

/-- Overlap generation pays the exhaustive primary scan, one canonical
fallback pass, and exactly the overlap prefix. -/
theorem checks_eq_overlap {capability : Capability spec}
    {previous : Previous} (routed : Routed capability previous)
    (isOverlap : routed.terminal = .overlap) :
    routed.checks = (capability.payersAt previous).card +
      (capability.obstructionsAt previous).comparisonCount +
        (routed.overlapEvidence isOverlap).hit.index.1 + 1 := by
  rcases routed with ⟨terminal, outcome⟩
  cases outcome with
  | tierOne _ => cases isOverlap
  | overlap _ => rfl
  | deficit _ => cases isOverlap
  | reconciled _ => cases isOverlap

/-- Deficit generation pays each canonical component exactly once. -/
theorem checks_eq_deficit {capability : Capability spec}
    {previous : Previous} (routed : Routed capability previous)
    (isDeficit : routed.terminal = .deficit) :
    let residual := routed.deficitEvidence isDeficit
    let tierTwo := selectedTierTwo capability previous
      residual.ledger.fallback
    routed.checks = (capability.payersAt previous).card +
      (capability.obstructionsAt previous).comparisonCount +
        tierTwo.card * tierTwo.card + tierTwo.card + 1 := by
  rcases routed with ⟨terminal, outcome⟩
  cases outcome with
  | tierOne _ => cases isDeficit
  | overlap _ => cases isDeficit
  | deficit _ => rfl
  | reconciled _ => cases isDeficit

/-- Reconciled generation pays the same complete canonical schedule as the
deficit branch. -/
theorem checks_eq_reconciled {capability : Capability spec}
    {previous : Previous} (routed : Routed capability previous)
    (isReconciled : routed.terminal = .reconciled) :
    let certificate := routed.reconciliationEvidence isReconciled
    let tierTwo := selectedTierTwo capability previous
      certificate.ledger.fallback
    routed.checks = (capability.payersAt previous).card +
      (capability.obstructionsAt previous).comparisonCount +
        tierTwo.card * tierTwo.card + tierTwo.card + 1 := by
  rcases routed with ⟨terminal, outcome⟩
  cases outcome with
  | tierOne _ => cases isReconciled
  | overlap _ => cases isReconciled
  | deficit _ => cases isReconciled
  | reconciled _ => rfl

/-- Output-only routed work remains inside the complete inherited schedule. -/
theorem checks_le_limit {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous) :
    routed.checks <=
      localCheckBound (capability.payersAt previous)
        (capability.obstructionsAt previous)
        (capability.tierTwo.read previous) :=
  outcomeChecks_le_limit routed.outcome

/-- Output-only routed work satisfies the capability polynomial envelope. -/
theorem checks_le_polynomial {capability : Capability spec}
    {previous : Previous} (routed : Routed capability previous) :
    routed.checks <= capability.workCoefficient *
      (capability.inputSize previous + 1) ^ capability.workDegree :=
  routed.checks_le_limit.trans (capability.workBound previous)

end Routed

/-- Private executor package connecting the count accumulated from retained
operations to the terminal-indexed public accounting view. -/
private structure CountedReferenceResult (capability : Capability spec)
    (previous : Previous) where
  counted : Core.Counted (Routed capability previous)
  checks_eq : counted.checks = counted.value.checks

/-- Execute the canonical CT13 machine without extending the predecessor.
Every counted operation is let-bound once, and each later route consumes the
value of that same retained operation. -/
private def executeReference (capability : Capability spec)
    (previous : Previous) : CountedReferenceResult capability previous :=
  let primaryScan := countedTierOneScan capability previous
  let primaryRoute := Core.Finite.Search.route primaryScan.value
  match primaryRoute.added with
  | .yesBranch hasTierOne =>
      let residual := primaryScan.value.hitOfHasHit hasTierOne
      {
        counted := ⟨.mk .tierOne (.tierOne residual), primaryScan.checks⟩
        checks_eq := by
          have exactPrimary := countedTierOneScan_checks_eq_hit
            capability previous hasTierOne
          simpa [Routed.checks, outcomeChecks, residual] using exactPrimary
      }
  | .noBranch absence =>
      let fallbackResult := countedComputeFallback capability previous absence
      let fallback := fallbackResult.value
      let overlapScanResult := countedOverlapScan capability previous fallback
      let overlapRoute := Core.Finite.Search.route overlapScanResult.value
      match overlapRoute.added with
      | .yesBranch hasOverlap =>
          let residual := overlapResidual capability previous fallback
            (overlapScanResult.value.hitOfHasHit hasOverlap)
          {
            counted := ⟨.mk .overlap (.overlap residual),
              primaryScan.checks + fallbackResult.checks +
                overlapScanResult.checks⟩
            checks_eq := by
              have primaryChecks :=
                countedTierOneScan_checks_eq_card_of_absence
                  capability previous absence
              have fallbackChecks := countedComputeFallback_checks
                capability previous absence
              have overlapChecks := countedOverlapScan_checks_eq_hit
                capability previous fallback hasOverlap
              have residualHitChecks : overlapScanResult.checks =
                  residual.hit.index.1 + 1 := by
                simpa [residual, overlapResidual] using overlapChecks
              change primaryScan.checks + fallbackResult.checks +
                overlapScanResult.checks =
                  (capability.payersAt previous).card +
                    (capability.obstructionsAt previous).comparisonCount +
                      residual.hit.index.1 + 1
              rw [primaryChecks, fallbackChecks, residualHitChecks]
              omega
          }
      | .noBranch overlapFree =>
          let ledgerResult := countedBuildReconciliationLedger capability
            previous fallback overlapFree
          let ledger := ledgerResult.value
          let comparisonResult := countedCompare capability previous ledger
          match comparisonResult.value.added with
          | .yesBranch deficit =>
              let residual := deficitResidual capability previous ledger (by
                have exactDeficit := deficit
                rw [show comparisonResult.value.previous = ledger from rfl]
                  at exactDeficit
                exact exactDeficit)
              {
                counted := ⟨.mk .deficit (.deficit residual),
                  primaryScan.checks + fallbackResult.checks +
                    overlapScanResult.checks + ledgerResult.checks +
                      comparisonResult.checks⟩
                checks_eq := by
                  have primaryChecks :=
                    countedTierOneScan_checks_eq_card_of_absence
                      capability previous absence
                  have fallbackChecks := countedComputeFallback_checks
                    capability previous absence
                  have overlapChecks :=
                    countedOverlapScan_checks_eq_card_of_clean capability
                      previous fallback overlapFree
                  have pairChecks : overlapScanResult.checks =
                      (selectedTierTwo capability previous fallback).card *
                        (selectedTierTwo capability previous fallback).card := by
                    rw [overlapChecks]
                    simpa [reconciliationPairs] using
                      (Core.Finite.Enumeration.card_product
                        (selectedTierTwo capability previous fallback)
                        (selectedTierTwo capability previous fallback))
                  have ledgerChecks :=
                    countedBuildReconciliationLedger_checks capability
                      previous fallback overlapFree
                  have comparisonChecks := countedCompare_checks capability
                    previous ledger
                  change primaryScan.checks + fallbackResult.checks +
                    overlapScanResult.checks + ledgerResult.checks +
                      comparisonResult.checks =
                    (capability.payersAt previous).card +
                      (capability.obstructionsAt previous).comparisonCount +
                        (selectedTierTwo capability previous fallback).card *
                          (selectedTierTwo capability previous fallback).card +
                        (selectedTierTwo capability previous fallback).card + 1
                  rw [primaryChecks, fallbackChecks, pairChecks, ledgerChecks,
                    comparisonChecks]
              }
          | .noBranch covers =>
              let certificate := reconciliationCertificate capability previous
                ledger (by
                  have exactCovers := covers
                  rw [show comparisonResult.value.previous = ledger from rfl]
                    at exactCovers
                  exact exactCovers)
              {
                counted := ⟨.mk .reconciled (.reconciled certificate),
                  primaryScan.checks + fallbackResult.checks +
                    overlapScanResult.checks + ledgerResult.checks +
                      comparisonResult.checks⟩
                checks_eq := by
                  have primaryChecks :=
                    countedTierOneScan_checks_eq_card_of_absence
                      capability previous absence
                  have fallbackChecks := countedComputeFallback_checks
                    capability previous absence
                  have overlapChecks :=
                    countedOverlapScan_checks_eq_card_of_clean capability
                      previous fallback overlapFree
                  have pairChecks : overlapScanResult.checks =
                      (selectedTierTwo capability previous fallback).card *
                        (selectedTierTwo capability previous fallback).card := by
                    rw [overlapChecks]
                    simpa [reconciliationPairs] using
                      (Core.Finite.Enumeration.card_product
                        (selectedTierTwo capability previous fallback)
                        (selectedTierTwo capability previous fallback))
                  have ledgerChecks :=
                    countedBuildReconciliationLedger_checks capability
                      previous fallback overlapFree
                  have comparisonChecks := countedCompare_checks capability
                    previous ledger
                  change primaryScan.checks + fallbackResult.checks +
                    overlapScanResult.checks + ledgerResult.checks +
                      comparisonResult.checks =
                    (capability.payersAt previous).card +
                      (capability.obstructionsAt previous).comparisonCount +
                        (selectedTierTwo capability previous fallback).card *
                          (selectedTierTwo capability previous fallback).card +
                        (selectedTierTwo capability previous fallback).card + 1
                  rw [primaryChecks, fallbackChecks, pairChecks, ledgerChecks,
                    comparisonChecks]
              }

/-- Counted projection of the single private canonical execution. -/
private def countedRouteReference (capability : Capability spec)
    (previous : Previous) : Core.Counted (Routed capability previous) :=
  (executeReference capability previous).counted

/-- Generate one sealed CT13 output without extending the literal
predecessor.  Callers provide only the capability and predecessor. -/
def generateCounted (capability : Capability spec) (previous : Previous) :
    Core.Counted (Routed capability previous) :=
  countedRouteReference capability previous

/-- Semantic reference route projected from the counted generator. -/
def routeReference (capability : Capability spec) (previous : Previous) :
    Routed capability previous :=
  (generateCounted capability previous).value

@[simp] theorem generateCounted_value (capability : Capability spec)
    (previous : Previous) :
    (generateCounted capability previous).value =
      routeReference capability previous :=
  rfl

/-- The published count is exactly the count attached to the generated
semantic output by the retained canonical execution. -/
@[simp] theorem generateCounted_checks (capability : Capability spec)
    (previous : Previous) :
    (generateCounted capability previous).checks =
      (generateCounted capability previous).value.checks :=
  (executeReference capability previous).checks_eq

/-- Exact predecessor-indexed budget for composing CT13 inside another
framework executor. -/
def generationBudget (capability : Capability spec) :
    Core.PolynomialCheckBudget Previous where
  size := capability.inputSize
  checks := fun previous => (generateCounted capability previous).checks
  coefficient := capability.workCoefficient
  degree := capability.workDegree
  bounded := fun previous => by
    rw [generateCounted_checks]
    exact (generateCounted capability previous).value.checks_le_polynomial

@[simp] theorem generateCounted_checks_eq_budget
    (capability : Capability spec) (previous : Previous) :
    (generateCounted capability previous).checks =
      (generationBudget capability).checks previous :=
  rfl

/-- Generated work remains within the complete CT13 local schedule. -/
theorem generateCounted_checks_le_limit (capability : Capability spec)
    (previous : Previous) :
    (generateCounted capability previous).checks <=
      localCheckBound (capability.payersAt previous)
        (capability.obstructionsAt previous)
        (capability.tierTwo.read previous) := by
  rw [generateCounted_checks]
  exact (generateCounted capability previous).value.checks_le_limit

/-- The counted generator satisfies its exact predecessor-indexed polynomial
budget. -/
theorem generateCounted_checks_le_polynomial
    (capability : Capability spec) (previous : Previous) :
    (generateCounted capability previous).checks <=
      (generationBudget capability).coefficient *
        ((generationBudget capability).size previous + 1) ^
          (generationBudget capability).degree :=
  (generationBudget capability).bounded previous

/-- Exact tier-one equation for the output-only generator. -/
theorem generateCounted_checks_eq_tierOne (capability : Capability spec)
    (previous : Previous)
    (isTierOne : (generateCounted capability previous).value.terminal =
      .tierOne) :
    (generateCounted capability previous).checks =
      ((generateCounted capability previous).value.tierOneEvidence
        isTierOne).index.1 + 1 :=
  (generateCounted_checks capability previous).trans
    ((generateCounted capability previous).value.checks_eq_tierOne isTierOne)

/-- Exact overlap equation for the output-only generator. -/
theorem generateCounted_checks_eq_overlap (capability : Capability spec)
    (previous : Previous)
    (isOverlap : (generateCounted capability previous).value.terminal =
      .overlap) :
    (generateCounted capability previous).checks =
      (capability.payersAt previous).card +
        (capability.obstructionsAt previous).comparisonCount +
          ((generateCounted capability previous).value.overlapEvidence
            isOverlap).hit.index.1 + 1 :=
  (generateCounted_checks capability previous).trans
    ((generateCounted capability previous).value.checks_eq_overlap isOverlap)

/-- Exact deficit equation for the output-only generator. -/
theorem generateCounted_checks_eq_deficit (capability : Capability spec)
    (previous : Previous)
    (isDeficit : (generateCounted capability previous).value.terminal =
      .deficit) :
    let residual :=
      (generateCounted capability previous).value.deficitEvidence isDeficit
    let tierTwo := selectedTierTwo capability previous
      residual.ledger.fallback
    (generateCounted capability previous).checks =
      (capability.payersAt previous).card +
        (capability.obstructionsAt previous).comparisonCount +
          tierTwo.card * tierTwo.card + tierTwo.card + 1 :=
  (generateCounted_checks capability previous).trans
    ((generateCounted capability previous).value.checks_eq_deficit isDeficit)

/-- Exact reconciled equation for the output-only generator. -/
theorem generateCounted_checks_eq_reconciled
    (capability : Capability spec) (previous : Previous)
    (isReconciled : (generateCounted capability previous).value.terminal =
      .reconciled) :
    let certificate :=
      (generateCounted capability previous).value.reconciliationEvidence
        isReconciled
    let tierTwo := selectedTierTwo capability previous
      certificate.ledger.fallback
    (generateCounted capability previous).checks =
      (capability.payersAt previous).card +
        (capability.obstructionsAt previous).comparisonCount +
          tierTwo.card * tierTwo.card + tierTwo.card + 1 :=
  (generateCounted_checks capability previous).trans
    ((generateCounted capability previous).value.checks_eq_reconciled
      isReconciled)

/-- One CT13 execution is one extension of the literal incoming ledger. -/
abbrev Stage
    (spec : Spec.{uPrevious, uPayer, uObstruction, uResource} Previous)
    (capability : Capability spec) :=
  Core.Residual.Ledger.Extension Previous fun previous =>
    Routed capability previous

/-- Closed public CT13 execution. -/
structure ExecutionResult
    (spec : Spec.{uPrevious, uPayer, uObstruction, uResource} Previous)
    (capability : Capability spec) where
  private mk ::
  stage : Stage spec capability
  trace : Trace stage.added.terminal
  checks : Nat
  checks_eq : checks = outcomeChecks stage.added.outcome

namespace ExecutionResult

def terminal {capability : Capability spec}
    (result : ExecutionResult spec capability) : Terminal :=
  result.stage.added.terminal

def outcome {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    Outcome capability result.stage.previous result.terminal :=
  result.stage.added.outcome

def traceNodes {capability : Capability spec}
    (result : ExecutionResult spec capability) : List NodeId :=
  result.trace.nodes

/-- Observable canonical fallback, absent only on the tier-one terminal. -/
def selectedFallback? {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    Option (spec.Obstruction result.stage.previous) :=
  result.outcome.selectedFallback?

/-- Observable first overlap index, present only on the overlap terminal. -/
def overlapIndex? {capability : Capability spec}
    (result : ExecutionResult spec capability) : Option Nat :=
  result.outcome.overlapIndex?

/-- Observable first overlapping payer pair, present only on the overlap
terminal. -/
def overlapPair? {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    Option (spec.Payer result.stage.previous ×
      spec.Payer result.stage.previous) :=
  result.outcome.overlapPair?

theorem checks_le_limit {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <=
      localCheckBound (capability.payersAt result.stage.previous)
        (capability.obstructionsAt result.stage.previous)
        (capability.tierTwo.read result.stage.previous) := by
  rw [result.checks_eq]
  exact outcomeChecks_le_limit result.stage.added.outcome

theorem checks_le_polynomial {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <= capability.workCoefficient *
      (capability.inputSize result.stage.previous + 1) ^
        capability.workDegree :=
  result.checks_le_limit.trans (capability.workBound result.stage.previous)

end ExecutionResult

/-- Execute CT13 on one literal predecessor ledger. -/
def run
    (spec : Spec.{uPrevious, uPayer, uObstruction, uResource} Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  let generated := generateCounted capability previous
  {
    stage := Core.Residual.Ledger.extend previous generated.value
    trace := generated.value.trace
    checks := generated.checks
    checks_eq := by
      change generated.checks = generated.value.checks
      exact generateCounted_checks capability previous
  }

@[simp] theorem run_routed_eq_generated
    (spec : Spec.{uPrevious, uPayer, uObstruction, uResource} Previous)
    (capability : Capability spec) (previous : Previous) :
    (run spec capability previous).stage.added =
      (generateCounted capability previous).value :=
  rfl

@[simp] theorem run_checks_eq_generated
    (spec : Spec.{uPrevious, uPayer, uObstruction, uResource} Previous)
    (capability : Capability spec) (previous : Previous) :
    (run spec capability previous).checks =
      (generateCounted capability previous).checks :=
  rfl

@[simp] theorem run_checks_eq_generationBudget
    (spec : Spec.{uPrevious, uPayer, uObstruction, uResource} Previous)
    (capability : Capability spec) (previous : Previous) :
    (run spec capability previous).checks =
      (generationBudget capability).checks previous :=
  rfl

@[simp] theorem run_previous
    (spec : Spec.{uPrevious, uPayer, uObstruction, uResource} Previous)
    (capability : Capability spec) (previous : Previous) :
    (run spec capability previous).stage.previous = previous :=
  rfl

end Hypostructure.CT13
