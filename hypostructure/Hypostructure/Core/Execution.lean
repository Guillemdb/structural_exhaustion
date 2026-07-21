import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Provision
import Hypostructure.Core.Residual.Query

/-!
# Generic executable substrate

A CT-specific module supplies a deterministic reference machine and proofs
about that machine.  Core alone packages its value as a public typed result
and installs it in the accumulated predecessor ledger.
-/

namespace Hypostructure.Core.Execution

universe uPrevious uInput uOutcome uTrace uResidual

/-- Domain-neutral shape of one executable CT entry. -/
structure Spec (Previous : Type uPrevious) where
  Input : Previous -> Type uInput
  Outcome : (previous : Previous) -> Input previous -> Type uOutcome
  Trace : (previous : Previous) -> (input : Input previous) ->
    Outcome previous input -> Type uTrace
  Sound : (previous : Previous) -> (input : Input previous) ->
    (outcome : Outcome previous input) -> Trace previous input outcome -> Prop
  Exhaustive : (previous : Previous) -> (input : Input previous) ->
    Outcome previous input -> Prop

/-- The exact dependent input used by work-budget accounting. -/
abbrev PackedInput {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uInput, uOutcome, uTrace} Previous) :=
  Sigma spec.Input

/-- Raw value returned by a registered deterministic reference machine. -/
structure ReferenceResult {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uInput, uOutcome, uTrace} Previous)
    (previous : Previous) (input : spec.Input previous) where
  outcome : spec.Outcome previous input
  trace : spec.Trace previous input outcome

/-- Complete reusable implementation contract for one `Spec`.

CT modules construct this from their primitive capabilities.  The application
does not provide a completed `ReferenceResult`; it provides the primitive
mathematics from which the CT module defines `reference`. -/
structure Capability {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uInput, uOutcome, uTrace} Previous) where
  reference : (previous : Previous) -> (input : spec.Input previous) ->
    Counted (ReferenceResult spec previous input)
  sound : (previous : Previous) -> (input : spec.Input previous) ->
    spec.Sound previous input
      (reference previous input).value.outcome
      (reference previous input).value.trace
  exhaustive : (previous : Previous) -> (input : spec.Input previous) ->
    spec.Exhaustive previous input (reference previous input).value.outcome
  work : PolynomialCheckBudget (PackedInput spec)
  checks_eq : (previous : Previous) -> (input : spec.Input previous) ->
    (reference previous input).checks = work.checks ⟨previous, input⟩

/-- Public framework-generated result.  Its private constructor prevents a
caller from manufacturing a selected outcome, trace, or verification proof. -/
structure Result {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uInput, uOutcome, uTrace} Previous)
    (previous : Previous) (input : spec.Input previous) where
  private mk ::
  outcome : spec.Outcome previous input
  trace : spec.Trace previous input outcome
  sound : spec.Sound previous input outcome trace
  exhaustive : spec.Exhaustive previous input outcome
  checks : Nat

/-- The sole value added by an execution.  It retains the exact input and the
typed generated result indexed by that input. -/
structure Output {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uInput, uOutcome, uTrace} Previous)
    (previous : Previous) where
  private mk ::
  input : spec.Input previous
  result : Result spec previous input

/-- One CT execution is one dependent extension of the literal predecessor. -/
abbrev Stage {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uInput, uOutcome, uTrace} Previous) :=
  Residual.Ledger.Extension Previous (Output spec)

/-- Execute the registered deterministic reference implementation. -/
def runReference {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uInput, uOutcome, uTrace} Previous}
    (capability : Capability spec) (previous : Previous)
    (input : spec.Input previous) :
    Counted (ReferenceResult spec previous input) :=
  capability.reference previous input

/-- Run a CT entry and install its framework-generated output in the complete
incoming ledger. -/
def run {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uInput, uOutcome, uTrace} Previous}
    (capability : Capability spec) (previous : Previous)
    (input : spec.Input previous) : Stage spec :=
  let reference := runReference capability previous input
  Residual.Ledger.extend previous <| .mk input <| .mk
    reference.value.outcome
    reference.value.trace
    (capability.sound previous input)
    (capability.exhaustive previous input)
    reference.checks

@[simp] theorem run_previous {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uInput, uOutcome, uTrace} Previous}
    (capability : Capability spec) (previous : Previous)
    (input : spec.Input previous) :
    (run capability previous input).previous = previous :=
  rfl

@[simp] theorem run_input {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uInput, uOutcome, uTrace} Previous}
    (capability : Capability spec) (previous : Previous)
    (input : spec.Input previous) :
    (run capability previous input).added.input = input :=
  rfl

@[simp] theorem run_checks {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uInput, uOutcome, uTrace} Previous}
    (capability : Capability spec) (previous : Previous)
    (input : spec.Input previous) :
    (run capability previous input).added.result.checks =
      (runReference capability previous input).checks :=
  rfl

/-- Aggregate soundness of every generated execution. -/
theorem run_sound {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uInput, uOutcome, uTrace} Previous}
    (capability : Capability spec) (previous : Previous)
    (input : spec.Input previous) :
    spec.Sound previous input
      (run capability previous input).added.result.outcome
      (run capability previous input).added.result.trace :=
  (run capability previous input).added.result.sound

/-- The generated outcome belongs to the CT-specific exhaustive outcome
grammar. -/
theorem outcome_exhaustive {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uInput, uOutcome, uTrace} Previous}
    (capability : Capability spec) (previous : Previous)
    (input : spec.Input previous) :
    spec.Exhaustive previous input
      (run capability previous input).added.result.outcome :=
  (run capability previous input).added.result.exhaustive

/-- Execution is total for every predecessor-indexed input. -/
theorem run_total {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uInput, uOutcome, uTrace} Previous}
    (capability : Capability spec) (previous : Previous)
    (input : spec.Input previous) :
    exists stage : Stage spec,
      stage.previous = previous /\
        spec.Sound stage.previous stage.added.input
          stage.added.result.outcome stage.added.result.trace := by
  exact ⟨run capability previous input, rfl,
    (run capability previous input).added.result.sound⟩

/-- The reference implementation is deterministic in relational form. -/
theorem runReference_deterministic {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uInput, uOutcome, uTrace} Previous}
    (capability : Capability spec) (previous : Previous)
    (input : spec.Input previous)
    (first second : Counted (ReferenceResult spec previous input))
    (first_eq : runReference capability previous input = first)
    (second_eq : runReference capability previous input = second) :
    first = second :=
  first_eq.symm.trans second_eq

/-- Public execution has exactly the deterministic reference semantics. -/
theorem run_deterministic {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uInput, uOutcome, uTrace} Previous}
    (capability : Capability spec) (previous : Previous)
    (input : spec.Input previous) (first second : Stage spec)
    (first_eq : run capability previous input = first)
    (second_eq : run capability previous input = second) : first = second :=
  first_eq.symm.trans second_eq

/-- The visible primitive-check count is the count registered by the work
budget at this exact dependent input. -/
theorem run_checks_eq_work {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uInput, uOutcome, uTrace} Previous}
    (capability : Capability spec) (previous : Previous)
    (input : spec.Input previous) :
    (run capability previous input).added.result.checks =
      capability.work.checks ⟨previous, input⟩ := by
  rw [run_checks]
  exact capability.checks_eq previous input

/-- Every execution satisfies its visible polynomial work envelope. -/
theorem run_work_bounded {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uInput, uOutcome, uTrace} Previous}
    (capability : Capability spec) (previous : Previous)
    (input : spec.Input previous) :
    (run capability previous input).added.result.checks <=
      capability.work.coefficient *
        (capability.work.size ⟨previous, input⟩ + 1) ^
          capability.work.degree := by
  rw [run_checks_eq_work]
  exact capability.work.bounded ⟨previous, input⟩

/-- Executing on an accumulated residual ledger preserves its stable residual
definitionally. -/
@[simp] theorem run_residual {Previous : Type uPrevious}
    {ResidualType : Type uResidual}
    [Residual.HasResidual Previous ResidualType]
    {spec : Spec.{uPrevious, uInput, uOutcome, uTrace} Previous}
    (capability : Capability spec) (previous : Previous)
    (input : spec.Input previous) :
    Residual.residualOf (run capability previous input) =
      Residual.residualOf previous :=
  rfl

end Hypostructure.Core.Execution
