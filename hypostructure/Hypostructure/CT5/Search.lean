import Hypostructure.CT5.State
import Hypostructure.Core.Finite.Accounting

/-!
# CT5 finite scans and Core-owned decisions

Support and deficit scans use Core first-hit execution.  The required and
capacity comparisons use Core binary residual decisions with fixed priority.
-/

namespace Hypostructure.CT5

universe uPrevious uSite uWitness uResource

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uSite, uWitness, uResource} Previous}

/-- Counted canonical support scan at one site. -/
def countedSupportScan (capability : Capability spec) (previous : Previous)
    (site : spec.Site previous) :
    Core.Counted (Core.Finite.Search.Execution
      (capability.witnessesAt previous site)
      (spec.Supports previous site)) :=
  Core.Finite.Accounting.countedRun
    (capability.witnessesAt previous site)
    (spec.Supports previous site)
    (capability.supportsDecidable previous site)

/-- Exact primitive support checks in the residual-owned dependent prepass. -/
def supportPassChecks (capability : Capability spec)
    (previous : Previous) : Nat :=
  (capability.sitesAt previous).values.map (fun site =>
    Core.Finite.Accounting.executionChecks
      (supportScan capability previous site)) |>.sum

/-- The exact support prepass is bounded by the sum of incoming fibre sizes. -/
theorem supportPassChecks_le_witnessCount (capability : Capability spec)
    (previous : Previous) :
    supportPassChecks capability previous <= capability.witnessCount previous := by
  unfold supportPassChecks Capability.witnessCount
  rw [Core.Finite.DependentEnumeration.card_flatten]
  change ((capability.sitesAt previous).values.map (fun site =>
      Core.Finite.Accounting.executionChecks
        (supportScan capability previous site))).sum <=
    ((capability.sitesAt previous).values.map (fun site =>
      (capability.witnessesAt previous site).card)).sum
  induction (capability.sitesAt previous).values with
  | nil => simp
  | cons site sites inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (Core.Finite.Accounting.executionChecks_le_card
          (supportScan capability previous site))
        inductionHypothesis

/-- Primitive decision for one local deficit, derived from the canonical
support scan rather than an application-authored no-witness proof. -/
def deficitAtDecidable (capability : Capability spec) (previous : Previous)
    (site : spec.Site previous) :
    Decidable (DeficitAt capability previous site) :=
  match capability.activeDecidable previous site with
  | .isFalse inactive => .isFalse fun deficit => inactive deficit.1
  | .isTrue active =>
      let scan := supportScan capability previous site
      match scan.instDecidableHasHit with
      | .isTrue hasSupport => .isFalse fun deficit =>
          let certificate := scan.hitOfHasHit hasSupport
          deficit.2 certificate.index certificate.holds
      | .isFalse noSupport =>
          .isTrue <| And.intro active (scan.avoids_of_not_hasHit noSupport)

/-- Counted canonical first-deficit scan over the exact site schedule. -/
def countedDeficitScan (capability : Capability spec) (previous : Previous) :
    Core.Counted (Core.Finite.Search.Execution
      (capability.sitesAt previous) (DeficitAt capability previous)) :=
  Core.Finite.Accounting.countedRun (capability.sitesAt previous)
    (DeficitAt capability previous)
    (deficitAtDecidable capability previous)

/-- Canonical first-deficit scan. -/
def deficitScan (capability : Capability spec) (previous : Previous) :
    Core.Finite.Search.Execution (capability.sitesAt previous)
      (DeficitAt capability previous) :=
  (countedDeficitScan capability previous).value

/-- Core-owned first-deficit route. -/
abbrev DeficitRoute (capability : Capability spec) (previous : Previous) :=
  Core.Residual.Decision.Stage
    (fun execution : Core.Finite.Search.Execution
        (capability.sitesAt previous) (DeficitAt capability previous) =>
      execution.HasHit)
    (fun _execution : Core.Finite.Search.Execution
        (capability.sitesAt previous) (DeficitAt capability previous) =>
      DeficitFreeState capability previous)

/-- Route the exact deficit scan through Core. -/
def routeDeficit (capability : Capability spec) (previous : Previous) :
    DeficitRoute capability previous :=
  Core.Finite.Search.route (deficitScan capability previous)

/-- Every active scheduled site on a deficit-free branch has a canonical
first support in its exact incoming witness fibre. -/
def supportOfDeficitFree (capability : Capability spec) (previous : Previous)
    (state : DeficitFreeState capability previous)
    (site : spec.Site previous)
    (member : site ∈ (capability.sitesAt previous).values)
    (active : spec.Active previous site) :
    SupportCertificate capability previous site := by
  let scan := supportScan capability previous site
  have hasSupport : scan.HasHit := by
    by_contra absent
    have noSupport := scan.avoids_of_not_hasHit absent
    obtain ⟨index, indexed⟩ :=
      ((capability.sitesAt previous).mem_iff_exists_index site).mp member
    exact state index (by
      unfold DeficitAt
      rw [indexed]
      exact And.intro active noSupport)
  exact scan.hitOfHasHit hasSupport

/-- First comparison: can capacity meet the registered requirement? -/
def requiredDecisionNode (capability : Capability spec)
    (previous : Previous) :
    Core.Residual.Decision.Node
      (LocalLedgerState capability previous)
      (fun _ledger => spec.required previous <= spec.capacity previous)
      (fun _ledger => Not (spec.required previous <= spec.capacity previous)) :=
  Core.Residual.Decision.Node.complement
    (fun _ledger : LocalLedgerState capability previous =>
      spec.required previous <= spec.capacity previous)
    (fun _ledger => capability.resourceLEDecidable _ _)

/-- Core route for the required-versus-capacity comparison. -/
def routeRequired (capability : Capability spec) (previous : Previous)
    (ledger : LocalLedgerState capability previous) :=
  (requiredDecisionNode capability previous).run ledger

/-- Second comparison, reached only when the required amount is affordable. -/
def capacityDecisionNode (capability : Capability spec)
    (previous : Previous) :
    Core.Residual.Decision.Node
      (LocalLedgerState capability previous)
      (fun ledger => ledger.total <= spec.capacity previous)
      (fun ledger => Not (ledger.total <= spec.capacity previous)) :=
  Core.Residual.Decision.Node.complement
    (fun ledger : LocalLedgerState capability previous =>
      ledger.total <= spec.capacity previous)
    (fun _ledger => capability.resourceLEDecidable _ _)

/-- Core route for total-versus-capacity. -/
def routeCapacity (capability : Capability spec) (previous : Previous)
    (ledger : LocalLedgerState capability previous) :=
  (capacityDecisionNode capability previous).run ledger

end Hypostructure.CT5
