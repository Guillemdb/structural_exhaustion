import Hypostructure.CT14.Search

/-!
# CT14 accumulated execution

The reference machine computes every intermediate value and lets Core route
all three decisions.  Its only public ledger update is one extension of the
literal predecessor containing a private routed value.
-/

namespace Hypostructure.CT14

universe uPrevious uMember uLabel

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uMember, uLabel} Previous}

/-- Exhaustive CT14 terminals. -/
inductive Terminal where
  | unboundedMember
  | missingLabel
  | aggregate
  | capacity
  deriving DecidableEq, Repr

/-- Audit nodes in the canonical CT14 flow. -/
inductive NodeId where
  | entry
  | memberSchedule
  | lowerMassComputation
  | capacityScan
  | labelScan
  | aggregateLedger
  | aggregateComparison
  | unboundedMemberTerminal
  | missingLabelTerminal
  | aggregateTerminal
  | capacityTerminal
  deriving DecidableEq, Repr

/-- Framework-generated branch evidence indexed by its terminal. -/
inductive Outcome (capability : Capability spec) (previous : Previous) :
    Terminal -> Type _ where
  | unboundedMember
      (lower : LowerMassLedger capability previous)
      (residual : UnboundedMemberResidual capability previous) :
      Outcome capability previous .unboundedMember
  | missingLabel
      (lower : LowerMassLedger capability previous)
      (bounded : CapacityComplete capability previous)
      (residual : MissingLabelResidual capability previous) :
      Outcome capability previous .missingLabel
  | aggregate
      (ledger : AggregateLedger capability previous)
      (certificate : AggregateCertificate capability previous ledger) :
      Outcome capability previous .aggregate
  | capacity
      (ledger : AggregateLedger capability previous)
      (residual : CapacityResidual capability previous ledger) :
      Outcome capability previous .capacity

/-- Terminal-indexed CT14 trace. -/
inductive Trace : Terminal -> Type where
  | unboundedMember : Trace .unboundedMember
  | missingLabel : Trace .missingLabel
  | aggregate : Trace .aggregate
  | capacity : Trace .capacity

namespace Trace

/-- Observable scan and decision order of a typed trace. -/
def nodes : {terminal : Terminal} -> Trace terminal -> List NodeId
  | .unboundedMember, .unboundedMember =>
      [.entry, .memberSchedule, .lowerMassComputation, .capacityScan,
        .unboundedMemberTerminal]
  | .missingLabel, .missingLabel =>
      [.entry, .memberSchedule, .lowerMassComputation, .capacityScan,
        .labelScan, .missingLabelTerminal]
  | .aggregate, .aggregate =>
      [.entry, .memberSchedule, .lowerMassComputation, .capacityScan,
        .labelScan, .aggregateLedger, .aggregateComparison,
        .aggregateTerminal]
  | .capacity, .capacity =>
      [.entry, .memberSchedule, .lowerMassComputation, .capacityScan,
        .labelScan, .aggregateLedger, .aggregateComparison,
        .capacityTerminal]

/-- Canonical node sequence fixed by a terminal. -/
def expectedNodes : Terminal -> List NodeId
  | .unboundedMember =>
      [.entry, .memberSchedule, .lowerMassComputation, .capacityScan,
        .unboundedMemberTerminal]
  | .missingLabel =>
      [.entry, .memberSchedule, .lowerMassComputation, .capacityScan,
        .labelScan, .missingLabelTerminal]
  | .aggregate =>
      [.entry, .memberSchedule, .lowerMassComputation, .capacityScan,
        .labelScan, .aggregateLedger, .aggregateComparison,
        .aggregateTerminal]
  | .capacity =>
      [.entry, .memberSchedule, .lowerMassComputation, .capacityScan,
        .labelScan, .aggregateLedger, .aggregateComparison,
        .capacityTerminal]

theorem nodes_eq_expected : {terminal : Terminal} ->
    (trace : Trace terminal) -> trace.nodes = expectedNodes terminal
  | .unboundedMember, .unboundedMember => rfl
  | .missingLabel, .missingLabel => rfl
  | .aggregate, .aggregate => rfl
  | .capacity, .capacity => rfl

end Trace

/-- Private framework route selected by the deterministic reference machine. -/
structure Routed (capability : Capability spec) (previous : Previous) where
  private mk ::
  terminal : Terminal
  outcome : Outcome capability previous terminal

/-- Execute all CT14 computations and Core decisions. -/
def routeReference (capability : Capability spec) (previous : Previous) :
    Routed capability previous :=
  let lower := computeLowerMass capability previous
  let capacityRoute := routeCapacity capability previous
  match capacityRoute.added with
  | .yesBranch hasMissingCapacity =>
      .mk .unboundedMember (.unboundedMember lower
        (capacityRoute.previous.hitOfHasHit hasMissingCapacity))
  | .noBranch bounded =>
      let labelRoute := routeLabel capability previous
      match labelRoute.added with
      | .yesBranch hasMissingLabel =>
          .mk .missingLabel (.missingLabel lower bounded
            (labelRoute.previous.hitOfHasHit hasMissingLabel))
      | .noBranch labeled =>
          let ledger := buildAggregateLedger capability previous
            lower bounded labeled
          let comparison := compare capability previous ledger
          match comparison.added with
          | .yesBranch exceeds =>
              .mk .aggregate (.aggregate ledger (by
                have exactExceeds := exceeds
                rw [show comparison.previous = ledger from rfl] at exactExceeds
                exact exactExceeds))
          | .noBranch within =>
              .mk .capacity (.capacity ledger (by
                have exactWithin := within
                rw [show comparison.previous = ledger from rfl] at exactWithin
                exact exactWithin))

/-- Unique typed trace selected by generated outcome evidence. -/
def traceOfOutcome {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal) :
    Trace terminal := by
  cases outcome with
  | unboundedMember _ _ => exact .unboundedMember
  | missingLabel _ _ _ => exact .missingLabel
  | aggregate _ _ => exact .aggregate
  | capacity _ _ => exact .capacity

/-- Unique typed trace selected by a private routed result. -/
def traceOfRouted {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous) : Trace routed.terminal :=
  traceOfOutcome routed.outcome

/-- Exact primitive inspections charged by each generated outcome.

Lower mass always inspects all `n` members.  Capacity then inspects its first
hit prefix or all `n`; labels are inspected only after capacity completeness.
A complete pair of scans pays one final arithmetic comparison.
-/
def outcomeChecks {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal -> Nat
  | .unboundedMember, .unboundedMember _ residual =>
      (capability.membersAt previous).card + residual.index.1 + 1
  | .missingLabel, .missingLabel _ _ residual =>
      2 * (capability.membersAt previous).card + residual.index.1 + 1
  | .aggregate, .aggregate _ _ =>
      localCheckBound (capability.membersAt previous)
  | .capacity, .capacity _ _ =>
      localCheckBound (capability.membersAt previous)

/-- Branch-exact work is bounded by the complete prescribed schedule. -/
theorem outcomeChecks_le_limit {capability : Capability spec}
    {previous : Previous} {terminal : Terminal}
    (outcome : Outcome capability previous terminal) :
    outcomeChecks outcome <=
      localCheckBound (capability.membersAt previous) := by
  cases outcome with
  | unboundedMember _ residual =>
      have inspected : residual.index.1 + 1 <=
          (capability.membersAt previous).card :=
        Nat.succ_le_iff.mpr residual.index.isLt
      simp only [outcomeChecks, localCheckBound]
      omega
  | missingLabel _ _ residual =>
      have inspected : residual.index.1 + 1 <=
          (capability.membersAt previous).card :=
        Nat.succ_le_iff.mpr residual.index.isLt
      simp only [outcomeChecks, localCheckBound]
      omega
  | aggregate _ _ => rfl
  | capacity _ _ => rfl

/-- One CT14 execution is one extension of the literal incoming ledger. -/
abbrev Stage (spec : Spec.{uPrevious, uMember, uLabel} Previous)
    (capability : Capability spec) :=
  Core.Residual.Ledger.Extension Previous fun previous =>
    Routed capability previous

/-- Closed public CT14 execution. -/
structure ExecutionResult (spec : Spec.{uPrevious, uMember, uLabel} Previous)
    (capability : Capability spec) where
  private mk ::
  stage : Stage spec capability
  trace : Trace stage.added.terminal
  checks : Nat
  checks_eq : checks = outcomeChecks stage.added.outcome

namespace ExecutionResult

/-- Terminal derived from the retained private route. -/
def terminal {capability : Capability spec}
    (result : ExecutionResult spec capability) : Terminal :=
  result.stage.added.terminal

/-- Exact terminal-indexed generated output. -/
def outcome {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    Outcome capability result.stage.previous result.terminal :=
  result.stage.added.outcome

/-- Observable exact trace. -/
def traceNodes {capability : Capability spec}
    (result : ExecutionResult spec capability) : List NodeId :=
  result.trace.nodes

/-- Actual branch work is bounded by the complete CT14 schedule. -/
theorem checks_le_limit {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <=
      localCheckBound (capability.membersAt result.stage.previous) := by
  rw [result.checks_eq]
  exact outcomeChecks_le_limit result.stage.added.outcome

/-- Every execution satisfies the capability's polynomial work envelope. -/
theorem checks_le_polynomial {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <= capability.workCoefficient *
      (capability.inputSize result.stage.previous + 1) ^
        capability.workDegree :=
  result.checks_le_limit.trans (capability.workBound result.stage.previous)

end ExecutionResult

/-- Execute CT14 on one literal predecessor ledger. -/
def run (spec : Spec.{uPrevious, uMember, uLabel} Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  let routed := routeReference capability previous
  {
    stage := Core.Residual.Ledger.extend previous routed
    trace := traceOfRouted routed
    checks := outcomeChecks routed.outcome
    checks_eq := rfl
  }

@[simp] theorem run_previous
    (spec : Spec.{uPrevious, uMember, uLabel} Previous)
    (capability : Capability spec) (previous : Previous) :
    (run spec capability previous).stage.previous = previous :=
  rfl

end Hypostructure.CT14
