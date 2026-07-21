import Hypostructure.CT5.Execution

/-!
# CT5 soundness, totality, and terminal semantics
-/

namespace Hypostructure.CT5

universe uPrevious uSite uWitness uResource

namespace LocalDeficitResidual

theorem scheduled {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uSite, uWitness, uResource} Previous}
    {capability : Capability spec} {previous : Previous}
    (residual : LocalDeficitResidual capability previous) :
    residual.value ∈ (capability.sitesAt previous).values :=
  residual.member

theorem active {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uSite, uWitness, uResource} Previous}
    {capability : Capability spec} {previous : Previous}
    (residual : LocalDeficitResidual capability previous) :
    spec.Active previous residual.value :=
  residual.sound.1

theorem noSupportingWitness {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uSite, uWitness, uResource} Previous}
    {capability : Capability spec} {previous : Previous}
    (residual : LocalDeficitResidual capability previous) :
    NoSupportingWitness capability previous residual.value :=
  residual.sound.2

/-- The selected deficit is first in the exact residual-owned site order. -/
theorem first {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uSite, uWitness, uResource} Previous}
    {capability : Capability spec} {previous : Previous}
    (residual : LocalDeficitResidual capability previous) :
    forall site,
      site ∈ (capability.sitesAt previous).values.take residual.index.1 ->
        Not (DeficitAt capability previous site) :=
  Core.Finite.Search.IndexedHit.first residual

end LocalDeficitResidual

namespace DeficitFreeState

/-- Every active member of the exact incoming site schedule contributes
through a genuine first supporting witness. -/
theorem contribution_supported {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uSite, uWitness, uResource} Previous}
    {capability : Capability spec} {previous : Previous}
    (state : DeficitFreeState capability previous)
    (site : spec.Site previous)
    (member : site ∈ (capability.sitesAt previous).values)
    (active : spec.Active previous site) :
    Exists fun certificate : SupportCertificate capability previous site =>
      contributionAt capability previous site =
          spec.contribution previous site certificate.value /\
        spec.Supports previous site certificate.value := by
  cases activeDecision : capability.activeDecidable previous site with
  | isFalse inactive => exact (inactive active).elim
  | isTrue _activeProof =>
      cases supportDecision : (supportScan capability previous site).hit? with
      | none =>
          have noSupport : NoSupportingWitness capability previous site :=
            (supportScan capability previous site).exhaustive supportDecision
          obtain ⟨index, indexed⟩ :=
            ((capability.sitesAt previous).mem_iff_exists_index site).mp member
          exact (state index (by
            unfold DeficitAt
            rw [indexed]
            exact And.intro active noSupport)).elim
      | some certificate =>
          exact ⟨certificate, by
            constructor
            · simp [contributionAt, activeDecision, supportDecision]
            · exact certificate.sound⟩

end DeficitFreeState

namespace LocalLedgerState

/-- The retained total is exactly the budget sum of the generated entries. -/
theorem total_exact {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uSite, uWitness, uResource} Previous}
    {capability : Capability spec} {previous : Previous}
    (ledger : LocalLedgerState capability previous) :
    ledger.total = spec.budget.sum
      (contributionLedger capability previous) := by
  rw [ledger.total_eq, ledger.entries_eq]

/-- One generated entry occurs for each scheduled site. -/
theorem entries_length {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uSite, uWitness, uResource} Previous}
    {capability : Capability spec} {previous : Previous}
    (ledger : LocalLedgerState capability previous) :
    ledger.entries.length = (capability.sitesAt previous).card := by
  rw [ledger.entries_eq]
  simp [contributionLedger, Core.Finite.Enumeration.card]

end LocalLedgerState

/-- Mathematical claim advertised by each terminal. -/
def OutcomeClaim {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uSite, uWitness, uResource} Previous)
    (capability : Capability spec) (previous : Previous) : Terminal -> Prop
  | .deficit => Nonempty (LocalDeficitResidual capability previous)
  | .c4 => Not (spec.required previous <= spec.capacity previous)
  | .chargeLedger => Nonempty (ChargeLedgerResidual capability previous)
  | .aggregate => Nonempty (AggregateResidual capability previous)

namespace Outcome

theorem verified {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uSite, uWitness, uResource} Previous}
    {capability : Capability spec} {previous : Previous} {terminal : Terminal}
    (outcome : Outcome capability previous terminal) :
    OutcomeClaim spec capability previous terminal := by
  cases outcome with
  | deficit residual => exact ⟨residual⟩
  | c4 certificate => exact certificate.capacityFailure
  | chargeLedger residual => exact ⟨residual⟩
  | aggregate residual => exact ⟨residual⟩

end Outcome

namespace ExecutionResult

theorem verified {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uSite, uWitness, uResource} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    OutcomeClaim spec capability result.stage.previous result.terminal :=
  result.outcome.verified

theorem trace_exact {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uSite, uWitness, uResource} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.traceNodes = Trace.expectedNodes result.terminal :=
  result.trace.nodes_eq_expected

end ExecutionResult

theorem run_verified {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uSite, uWitness, uResource} Previous)
    (capability : Capability spec) (previous : Previous) :
    OutcomeClaim spec capability previous (run spec capability previous).terminal :=
  (run spec capability previous).verified

/-- CT5 is total, sound, exactly traced, and linearly work-bounded. -/
theorem run_total {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uSite, uWitness, uResource} Previous)
    (capability : Capability spec) (previous : Previous) :
    Exists fun result : ExecutionResult spec capability =>
      result.stage.previous = previous /\
      OutcomeClaim spec capability previous result.terminal /\
      result.traceNodes = Trace.expectedNodes result.terminal /\
      result.checks <= (capability.linearWorkBudget).coefficient *
        ((capability.linearWorkBudget).size previous + 1) ^
          (capability.linearWorkBudget).degree := by
  let result := run spec capability previous
  exact ⟨result, rfl, result.verified, result.trace_exact,
    result.checks_le_polynomial⟩

theorem run_deterministic {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uSite, uWitness, uResource} Previous)
    (capability : Capability spec) (previous : Previous)
    (first second : ExecutionResult spec capability)
    (firstIsRun : first = run spec capability previous)
    (secondIsRun : second = run spec capability previous) : first = second :=
  firstIsRun.trans secondIsRun.symm

theorem outcome_exhaustive {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uSite, uWitness, uResource} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.terminal = .deficit \/ result.terminal = .c4 \/
      result.terminal = .chargeLedger \/ result.terminal = .aggregate := by
  cases result.terminal <;> simp

end Hypostructure.CT5
