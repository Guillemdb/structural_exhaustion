import Hypostructure.CT10.Execution

/-!
# CT10 soundness, order, and totality
-/

namespace Hypostructure.CT10

universe uPrevious uDatum uClass uPromotion

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uDatum, uClass, uPromotion} Previous}

namespace DirectAbsent

/-- Indexed absence over a complete residual-owned class schedule excludes
every inhabitant of the declared class universe. -/
theorem all {capability : Capability spec} {previous : Previous}
    (absent : DirectAbsent capability previous)
    (cls : spec.Class previous) : Not (spec.Direct previous cls) := by
  have member : cls ∈ (capability.classesAt previous).values :=
    (capability.completeClassesAt previous).complete cls
  obtain ⟨index, equal⟩ :=
    ((capability.classesAt previous).mem_iff_exists_index cls).mp member
  intro direct
  exact absent index (by simpa [equal] using direct)

end DirectAbsent

namespace NoMissingClass

/-- Avoiding every missing row over a complete class schedule means every
declared class has a witness in the exact incoming datum schedule. -/
theorem observed {capability : Capability spec} {previous : Previous}
    (noMissing : NoMissingClass capability previous)
    (cls : spec.Class previous) : Observed capability previous cls := by
  match observedDecidable capability previous cls with
  | .isTrue observed => exact observed
  | .isFalse absent =>
      have member : cls ∈ (capability.classesAt previous).values :=
        (capability.completeClassesAt previous).complete cls
      obtain ⟨index, equal⟩ :=
        ((capability.classesAt previous).mem_iff_exists_index cls).mp member
      have missingAtIndex : Missing capability previous
          ((capability.classesAt previous).get index) := by
        simpa [Missing, equal] using absent
      exact (noMissing index missingAtIndex).elim

end NoMissingClass

namespace PromotedResidual

/-- The promoted class is absent from the exact incoming datum schedule. -/
theorem missing_sound {capability : Capability spec} {previous : Previous}
    (residual : PromotedResidual capability previous) :
    Missing capability previous residual.missing.value :=
  residual.missing.sound

/-- Every earlier declared class is observed; class order is execution data. -/
theorem earlier_observed {capability : Capability spec}
    {previous : Previous}
    (residual : PromotedResidual capability previous)
    (cls : spec.Class previous)
    (earlier : cls ∈ (capability.classesAt previous).values.take
      residual.missing.index.1) :
    Observed capability previous cls := by
  exact not_not.mp (residual.missing.first cls earlier)

/-- No declared class closes directly on a promoted branch. -/
theorem no_direct {capability : Capability spec} {previous : Previous}
    (residual : PromotedResidual capability previous)
    (cls : spec.Class previous) : Not (spec.Direct previous cls) :=
  residual.directAbsent.all cls

end PromotedResidual

namespace ExhaustiveCertificate

/-- No class is direct in an exhaustive classification. -/
theorem no_direct {capability : Capability spec} {previous : Previous}
    (certificate : ExhaustiveCertificate capability previous)
    (cls : spec.Class previous) : Not (spec.Direct previous cls) :=
  certificate.directAbsent.all cls

/-- Every class has an exact incoming datum witness. -/
theorem populated {capability : Capability spec} {previous : Previous}
    (certificate : ExhaustiveCertificate capability previous)
    (cls : spec.Class previous) : Observed capability previous cls :=
  certificate.noMissing.observed cls

end ExhaustiveCertificate

/-- Semantic proposition certified by each CT10 terminal. -/
def OutcomeClaim (capability : Capability spec) (previous : Previous) :
    Terminal -> Prop
  | .direct => Nonempty (DirectResidual capability previous)
  | .promoted => Nonempty (PromotedResidual capability previous)
  | .exhaustive => ExhaustiveCertificate capability previous

namespace Routed

/-- Aggregate soundness of the sealed framework route. -/
theorem verified {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous) :
    OutcomeClaim capability previous routed.terminal := by
  cases terminal : routed.terminal with
  | direct =>
      exact ⟨routed.directResidual terminal⟩
  | promoted =>
      exact ⟨routed.promotedResidual terminal⟩
  | exhaustive =>
      exact routed.exhaustiveCertificate terminal

end Routed

namespace ExecutionResult

/-- Aggregate semantic soundness. -/
theorem verified {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    OutcomeClaim capability result.stage.previous result.terminal :=
  result.stage.added.verified

/-- Every trace is exactly the terminal-indexed reference trace. -/
theorem trace_exact {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.traceNodes = Trace.expectedNodes result.terminal :=
  result.trace.nodes_eq_expected

/-- Retrieve the first direct class from a direct execution. -/
def directResidual {capability : Capability spec}
    (result : ExecutionResult spec capability)
    (terminal : result.terminal = .direct) :
    DirectResidual capability result.stage.previous :=
  result.stage.added.directResidual terminal

/-- Retrieve the first missing class and computed promotion. -/
def promotedResidual {capability : Capability spec}
    (result : ExecutionResult spec capability)
    (terminal : result.terminal = .promoted) :
    PromotedResidual capability result.stage.previous :=
  result.stage.added.promotedResidual terminal

/-- Retrieve exhaustive direct-absence and row-population evidence. -/
def exhaustiveCertificate {capability : Capability spec}
    (result : ExecutionResult spec capability)
    (terminal : result.terminal = .exhaustive) :
    ExhaustiveCertificate capability result.stage.previous :=
  result.stage.added.exhaustiveCertificate terminal

/-- A scheduled direct witness forces the direct terminal. -/
theorem terminal_direct_of_exists {capability : Capability spec}
    (result : ExecutionResult spec capability)
    (existsDirect : Exists fun cls =>
      cls ∈ (capability.classesAt result.stage.previous).values ∧
        spec.Direct result.stage.previous cls) :
    result.terminal = .direct := by
  rcases existsDirect with ⟨cls, member, direct⟩
  obtain ⟨index, equal⟩ :=
    ((capability.classesAt result.stage.previous).mem_iff_exists_index cls).mp
      member
  cases terminal : result.terminal with
  | direct => rfl
  | promoted =>
      let residual := result.promotedResidual terminal
      exact (residual.directAbsent index (by simpa [equal] using direct)).elim
  | exhaustive =>
      let certificate := result.exhaustiveCertificate terminal
      exact (certificate.directAbsent index
        (by simpa [equal] using direct)).elim

/-- No direct class plus one missing class forces promotion. -/
theorem terminal_promoted_of_noDirect_of_missing
    {capability : Capability spec}
    (result : ExecutionResult spec capability)
    (noDirect : forall cls, Not (spec.Direct result.stage.previous cls))
    (existsMissing : Exists fun cls =>
      Missing capability result.stage.previous cls) :
    result.terminal = .promoted := by
  rcases existsMissing with ⟨cls, missing⟩
  cases terminal : result.terminal with
  | direct =>
      let residual := result.directResidual terminal
      exact (noDirect residual.value residual.sound).elim
  | promoted => rfl
  | exhaustive =>
      let certificate := result.exhaustiveCertificate terminal
      exact (missing (certificate.populated cls)).elim

/-- No direct class and complete row population force the exhaustive terminal. -/
theorem terminal_exhaustive_of_noDirect_of_observed
    {capability : Capability spec}
    (result : ExecutionResult spec capability)
    (noDirect : forall cls, Not (spec.Direct result.stage.previous cls))
    (populated : forall cls, Observed capability result.stage.previous cls) :
    result.terminal = .exhaustive := by
  cases terminal : result.terminal with
  | direct =>
      let residual := result.directResidual terminal
      exact (noDirect residual.value residual.sound).elim
  | promoted =>
      let residual := result.promotedResidual terminal
      exact (residual.missing_sound (populated residual.missing.value)).elim
  | exhaustive => rfl

end ExecutionResult

/-- Public runner soundness. -/
theorem run_verified (capability : Capability spec) (previous : Previous) :
    OutcomeClaim capability previous (run capability previous).terminal :=
  (run capability previous).verified

/-- CT10 is total, traced, sound, predecessor-exact, and work-bounded. -/
theorem run_total (capability : Capability spec) (previous : Previous) :
    Exists fun result : ExecutionResult spec capability =>
      result.stage.previous = previous ∧
      OutcomeClaim capability previous result.terminal ∧
      result.traceNodes = Trace.expectedNodes result.terminal ∧
      result.checks <= capability.workCoefficient *
        (capability.inputSize previous + 1) ^ capability.workDegree := by
  let result := run capability previous
  exact ⟨result, rfl, result.verified, result.trace_exact,
    result.checks_le_polynomial⟩

/-- The pure reference executor is deterministic. -/
theorem run_deterministic (capability : Capability spec)
    (previous : Previous) (first second : ExecutionResult spec capability)
    (firstIsRun : first = run capability previous)
    (secondIsRun : second = run capability previous) : first = second :=
  firstIsRun.trans secondIsRun.symm

/-- No terminal outside direct, promoted, and exhaustive is reachable. -/
theorem outcome_exhaustive {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.terminal = .direct ∨ result.terminal = .promoted ∨
      result.terminal = .exhaustive := by
  cases result.terminal <;> simp

end Hypostructure.CT10
