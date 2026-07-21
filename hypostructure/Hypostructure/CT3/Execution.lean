import Hypostructure.CT3.Search

/-!
# CT3 accumulated execution

Core finite search and Core residual decisions choose every branch.  CT3 stores
the resulting terminal-indexed evidence as one dependent extension of the
literal incoming ledger.  The public result constructor is private.
-/

namespace Hypostructure.CT3

universe uPrevious uRepresentative uContext uCoordinate uValue uCandidate uRow

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue,
    uCandidate, uRow} Previous}

/-- The four exhaustive CT3 terminals. -/
inductive Terminal where
  | compression
  | distinguishing
  | knownRow
  | novelRow
  deriving DecidableEq, Repr

/-- Audit nodes in the complete CT3 reference flow. -/
inductive NodeId where
  | entry
  | vectorComputation
  | compressionSearch
  | tableValidation
  | rowLookup
  | compressionTerminal
  | distinguishingTerminal
  | knownRowTerminal
  | novelRowTerminal
  deriving DecidableEq, Repr

/-- Terminal-indexed evidence selected by the framework-owned scans. -/
inductive Outcome (capability : Capability spec) (previous : Previous) :
    Terminal -> Type _ where
  | compression (certificate : CompressionCertificate capability previous) :
      Outcome capability previous .compression
  | distinguishing (uncompressible : UncompressibleState capability previous)
      (certificate : DistinguishingCoordinate capability previous) :
      Outcome capability previous .distinguishing
  | knownRow (uncompressible : UncompressibleState capability previous)
      (table : ExactTableState capability previous)
      (certificate : KnownRowCertificate capability previous) :
      Outcome capability previous .knownRow
  | novelRow (uncompressible : UncompressibleState capability previous)
      (table : ExactTableState capability previous)
      (novel : NovelRowState capability previous) :
      Outcome capability previous .novelRow

/-- A typed trace; a terminal cannot be paired with another branch's path. -/
inductive Trace : Terminal -> Type where
  | compression : Trace .compression
  | distinguishing : Trace .distinguishing
  | knownRow : Trace .knownRow
  | novelRow : Trace .novelRow

namespace Trace

/-- Observable node sequence of a typed trace. -/
def nodes : {terminal : Terminal} -> Trace terminal -> List NodeId
  | .compression, .compression =>
      [.entry, .vectorComputation, .compressionSearch, .compressionTerminal]
  | .distinguishing, .distinguishing =>
      [.entry, .vectorComputation, .compressionSearch, .tableValidation,
        .distinguishingTerminal]
  | .knownRow, .knownRow =>
      [.entry, .vectorComputation, .compressionSearch, .tableValidation,
        .rowLookup, .knownRowTerminal]
  | .novelRow, .novelRow =>
      [.entry, .vectorComputation, .compressionSearch, .tableValidation,
        .rowLookup, .novelRowTerminal]

/-- Reference trace associated with each semantic terminal. -/
def expectedNodes : Terminal -> List NodeId
  | .compression =>
      [.entry, .vectorComputation, .compressionSearch, .compressionTerminal]
  | .distinguishing =>
      [.entry, .vectorComputation, .compressionSearch, .tableValidation,
        .distinguishingTerminal]
  | .knownRow =>
      [.entry, .vectorComputation, .compressionSearch, .tableValidation,
        .rowLookup, .knownRowTerminal]
  | .novelRow =>
      [.entry, .vectorComputation, .compressionSearch, .tableValidation,
        .rowLookup, .novelRowTerminal]

theorem nodes_eq_expected : {terminal : Terminal} ->
    (trace : Trace terminal) -> trace.nodes = expectedNodes terminal
  | .compression, .compression => rfl
  | .distinguishing, .distinguishing => rfl
  | .knownRow, .knownRow => rfl
  | .novelRow, .novelRow => rfl

end Trace

/-- CT3-routed evidence.  Its constructor is private, so callers cannot select
a terminal or pair it with unrelated evidence. -/
structure Routed (capability : Capability spec) (previous : Previous) where
  private mk ::
  terminal : Terminal
  outcome : Outcome capability previous terminal

/-- Core routes all three scans and CT3 retains the exact generated evidence. -/
def routeReference (capability : Capability spec) (previous : Previous) :
    Routed capability previous :=
  let compression := Core.Finite.Search.route
    (compressionScan capability previous)
  match compression.added with
  | .yesBranch hasCompression =>
      .mk .compression (.compression
        (compression.previous.hitOfHasHit hasCompression))
  | .noBranch uncompressible =>
      let validation := Core.Finite.Search.route
        (tableValidationScan capability previous)
      match validation.added with
      | .yesBranch hasDefect =>
          .mk .distinguishing (.distinguishing uncompressible
            (validation.previous.hitOfHasHit hasDefect))
      | .noBranch table =>
          let lookup := Core.Finite.Search.route
            (rowLookupScan capability previous)
          match lookup.added with
          | .yesBranch hasRow =>
              .mk .knownRow (.knownRow uncompressible table
                (lookup.previous.hitOfHasHit hasRow))
          | .noBranch novel =>
              .mk .novelRow (.novelRow uncompressible table novel)

/-- Unique typed trace selected from terminal-indexed outcome evidence. -/
def traceOfOutcome {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal) :
    Trace terminal := by
  cases outcome with
  | compression _ => exact .compression
  | distinguishing _ _ => exact .distinguishing
  | knownRow _ _ _ => exact .knownRow
  | novelRow _ _ _ => exact .novelRow

/-- Unique typed trace selected from the framework-owned terminal. -/
def traceOfRouted {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous) : Trace routed.terminal :=
  traceOfOutcome routed.outcome

/-- Exact primitive checks charged by the reference schedule.

Each inspected candidate pays two structural checks plus a complete response
vector comparison.  Table validation pays one check per inspected pair, and
row lookup pays one complete vector comparison per inspected row. -/
def outcomeChecks {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal -> Nat
  | .compression, .compression certificate =>
      (certificate.index.1 + 1) *
        (2 + (capability.coordinatesAt previous).card)
  | .distinguishing, .distinguishing _ certificate =>
      (capability.candidatesAt previous).card *
          (2 + (capability.coordinatesAt previous).card) +
        (certificate.index.1 + 1)
  | .knownRow, .knownRow _ _ certificate =>
      (capability.candidatesAt previous).card *
          (2 + (capability.coordinatesAt previous).card) +
        (capability.rowsAt previous).card *
          (capability.coordinatesAt previous).card +
        (certificate.index.1 + 1) *
          (capability.coordinatesAt previous).card
  | .novelRow, .novelRow _ _ _ =>
      localCheckBound (capability.coordinatesAt previous)
        (capability.candidatesAt previous) (capability.rowsAt previous)

/-- Exact charged work for any terminal is bounded by the full prescribed
schedule. -/
theorem outcomeChecks_le_limit {capability : Capability spec}
    {previous : Previous} {terminal : Terminal}
    (outcome : Outcome capability previous terminal) :
    outcomeChecks outcome <= localCheckBound
      (capability.coordinatesAt previous)
      (capability.candidatesAt previous)
      (capability.rowsAt previous) := by
  cases outcome with
  | compression certificate =>
      have inspected : certificate.index.1 + 1 <=
          (capability.candidatesAt previous).card :=
        Nat.succ_le_iff.mpr certificate.index.isLt
      have candidateBound := Nat.mul_le_mul_right
        (2 + (capability.coordinatesAt previous).card) inspected
      exact candidateBound.trans (by
        simp only [localCheckBound]
        rw [Nat.add_assoc]
        exact Nat.le_add_right
          ((capability.candidatesAt previous).card *
            (2 + (capability.coordinatesAt previous).card))
          ((capability.rowsAt previous).card *
              (capability.coordinatesAt previous).card +
            (capability.rowsAt previous).card *
              (capability.coordinatesAt previous).card))
  | distinguishing _ certificate =>
      have inspected : certificate.index.1 + 1 <=
          (tablePairsAt capability previous).card :=
        Nat.succ_le_iff.mpr certificate.index.isLt
      have pairCard : (tablePairsAt capability previous).card =
          (capability.rowsAt previous).card *
            (capability.coordinatesAt previous).card :=
        Core.Finite.Enumeration.card_product _ _
      have validationBound : certificate.index.1 + 1 <=
          (capability.rowsAt previous).card *
            (capability.coordinatesAt previous).card := by
        calc
          certificate.index.1 + 1 <=
              (tablePairsAt capability previous).card := inspected
          _ = (capability.rowsAt previous).card *
              (capability.coordinatesAt previous).card := pairCard
      simp only [outcomeChecks, localCheckBound]
      exact (Nat.add_le_add_left validationBound _).trans
        (Nat.le_add_right _ _)
  | knownRow _ _ certificate =>
      have inspected : certificate.index.1 + 1 <=
          (capability.rowsAt previous).card :=
        Nat.succ_le_iff.mpr certificate.index.isLt
      have lookupBound := Nat.mul_le_mul_right
        (capability.coordinatesAt previous).card inspected
      simp only [outcomeChecks, localCheckBound]
      exact Nat.add_le_add_left lookupBound _
  | novelRow _ _ _ =>
      rfl

/-- The accumulated CT3 stage contains the literal predecessor and one routed
framework output. -/
abbrev Stage (spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate,
    uValue, uCandidate, uRow} Previous) (capability : Capability spec) :=
  Core.Residual.Ledger.Extension Previous fun previous =>
    Routed capability previous

/-- Closed CT3 execution result. -/
structure ExecutionResult
    (spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue,
      uCandidate, uRow} Previous)
    (capability : Capability spec) where
  private mk ::
  stage : Stage spec capability
  trace : Trace stage.added.terminal
  checks : Nat
  checks_eq : checks = outcomeChecks stage.added.outcome

namespace ExecutionResult

/-- Terminal derived from the retained routed evidence. -/
def terminal {capability : Capability spec}
    (result : ExecutionResult spec capability) : Terminal :=
  result.stage.added.terminal

/-- Terminal-indexed semantic evidence retained in the ledger extension. -/
def outcome {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    Outcome capability result.stage.previous result.terminal :=
  result.stage.added.outcome

/-- Observable exact trace. -/
def traceNodes {capability : Capability spec}
    (result : ExecutionResult spec capability) : List NodeId :=
  result.trace.nodes

/-- Actual charged checks never exceed the prescribed complete local
schedule. -/
theorem checks_le_limit {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <= localCheckBound
      (capability.coordinatesAt result.stage.previous)
      (capability.candidatesAt result.stage.previous)
      (capability.rowsAt result.stage.previous) := by
  rw [result.checks_eq]
  exact outcomeChecks_le_limit result.stage.added.outcome

/-- Every execution satisfies the capability's polynomial work bound. -/
theorem checks_le_polynomial {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <= capability.workCoefficient *
      (capability.inputSize result.stage.previous + 1) ^
        capability.workDegree :=
  result.checks_le_limit.trans (capability.workBound result.stage.previous)

end ExecutionResult

/-- Execute CT3 on one literal incoming ledger. -/
def run (spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue,
    uCandidate, uRow} Previous) (capability : Capability spec)
    (previous : Previous) : ExecutionResult spec capability :=
  let routed := routeReference capability previous
  {
    stage := Core.Residual.Ledger.extend previous routed
    trace := traceOfRouted routed
    checks := outcomeChecks routed.outcome
    checks_eq := rfl
  }

@[simp] theorem run_previous
    (spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue,
      uCandidate, uRow} Previous)
    (capability : Capability spec) (previous : Previous) :
    (run spec capability previous).stage.previous = previous :=
  rfl

end Hypostructure.CT3
