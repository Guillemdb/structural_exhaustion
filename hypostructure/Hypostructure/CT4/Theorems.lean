import Hypostructure.CT4.Execution

/-!
# CT4 semantic soundness and totality
-/

namespace Hypostructure.CT4

universe uPrevious uDemand uPayer

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uDemand, uPayer} Previous}

namespace TotalAssignmentState

/-- Every inherited demand has a scheduled eligible payer selected by the
canonical first-hit assignment. -/
theorem existsEligible {capability : Capability spec} {previous : Previous}
    (total : TotalAssignmentState capability previous)
    (demand : spec.Demand previous)
    (member : demand ∈ (capability.demandsAt previous).values) :
    Exists fun payer : spec.Payer previous =>
      payer ∈ (capability.payersAt previous).values ∧
        spec.Eligible previous demand payer := by
  let hit := (total.assignment.execution demand).hitOfHasHit
    (total.total demand member)
  exact ⟨hit.value, hit.member, hit.sound⟩

end TotalAssignmentState

namespace OverloadedFibreResidual

/-- Canonically selected overloaded payer. -/
def payer {capability : Capability spec} {previous : Previous}
    {total : TotalAssignmentState capability previous}
    (residual : OverloadedFibreResidual capability previous total) :
    spec.Payer previous :=
  residual.value

/-- The overloaded payer belongs to the exact inherited payer schedule. -/
theorem scheduled {capability : Capability spec} {previous : Previous}
    {total : TotalAssignmentState capability previous}
    (residual : OverloadedFibreResidual capability previous total) :
    residual.payer ∈ (capability.payersAt previous).values :=
  residual.member

/-- The selected payer is genuinely overloaded by the canonical assignment. -/
theorem valid {capability : Capability spec} {previous : Previous}
    {total : TotalAssignmentState capability previous}
    (residual : OverloadedFibreResidual capability previous total) :
    spec.capacity previous residual.payer <
      fibreWeight total.assignment residual.payer :=
  residual.sound

end OverloadedFibreResidual

/-- Complete semantic claim advertised by each CT4 terminal. -/
def OutcomeClaim {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal -> Prop
  | .missingPayer, .missingPayer _assignment residual =>
      residual.demand ∈ (capability.demandsAt previous).values ∧
      (forall payer,
        payer ∈ (capability.payersAt previous).values ->
          Not (spec.Eligible previous residual.demand payer)) ∧
      (forall demand,
        demand ∈ (capability.demandsAt previous).values.take residual.index.1 ->
          Not (MissingAssignment capability previous _assignment demand))
  | .overloadedFibre, .overloadedFibre total residual =>
      (forall demand,
        demand ∈ (capability.demandsAt previous).values ->
          Exists fun payer : spec.Payer previous =>
            payer ∈ (capability.payersAt previous).values ∧
              spec.Eligible previous demand payer) ∧
      residual.payer ∈ (capability.payersAt previous).values ∧
      spec.capacity previous residual.payer <
        fibreWeight total.assignment residual.payer ∧
      (forall payer,
        payer ∈ (capability.payersAt previous).values.take residual.index.1 ->
          Not (Overloaded capability previous total payer))
  | .c4, .c4 total _bounded _certificate =>
      (forall demand,
        demand ∈ (capability.demandsAt previous).values ->
          Exists fun payer : spec.Payer previous =>
            payer ∈ (capability.payersAt previous).values ∧
              spec.Eligible previous demand payer) ∧
      (forall payer,
        payer ∈ (capability.payersAt previous).values ->
          fibreWeight total.assignment payer <= spec.capacity previous payer) ∧
      totalCapacity capability previous < spec.required previous
  | .capacity, .capacity total _bounded _residual =>
      (forall demand,
        demand ∈ (capability.demandsAt previous).values ->
          Exists fun payer : spec.Payer previous =>
            payer ∈ (capability.payersAt previous).values ∧
              spec.Eligible previous demand payer) ∧
      (forall payer,
        payer ∈ (capability.payersAt previous).values ->
          fibreWeight total.assignment payer <= spec.capacity previous payer) ∧
      spec.required previous <= totalCapacity capability previous

namespace Outcome

/-- Every generated terminal proves its exact semantic claim. -/
theorem verified {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal) :
    OutcomeClaim outcome := by
  cases outcome with
  | missingPayer assignment residual =>
      exact ⟨residual.scheduled, residual.noEligible, residual.first⟩
  | overloadedFibre total residual =>
      exact ⟨total.existsEligible, residual.scheduled, residual.valid,
        residual.first⟩
  | c4 total bounded certificate =>
      exact ⟨total.existsEligible, bounded.boundedAt, certificate⟩
  | capacity total bounded residual =>
      exact ⟨total.existsEligible, bounded.boundedAt, residual⟩

/-- No terminal outside the four CT4 alternatives is constructible. -/
theorem terminal_exhaustive {capability : Capability spec}
    {previous : Previous} {terminal : Terminal}
    (outcome : Outcome capability previous terminal) :
    terminal = .missingPayer ∨ terminal = .overloadedFibre ∨
      terminal = .c4 ∨ terminal = .capacity := by
  cases outcome with
  | missingPayer _ _ => exact Or.inl rfl
  | overloadedFibre _ _ => exact Or.inr (Or.inl rfl)
  | c4 _ _ _ => exact Or.inr (Or.inr (Or.inl rfl))
  | capacity _ _ _ => exact Or.inr (Or.inr (Or.inr rfl))

end Outcome

namespace ExecutionResult

/-- Aggregate semantic soundness. -/
theorem verified {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    OutcomeClaim result.outcome :=
  result.outcome.verified

/-- The terminal index fixes the complete observable trace. -/
theorem trace_exact {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.traceNodes = Trace.expectedNodes result.terminal :=
  result.trace.nodes_eq_expected

end ExecutionResult

/-- Public reference execution is semantically sound. -/
theorem run_verified (spec : Spec.{uPrevious, uDemand, uPayer} Previous)
    (capability : Capability spec) (previous : Previous) :
    OutcomeClaim (run spec capability previous).outcome :=
  (run spec capability previous).verified

/-- CT4 is total, exactly traced, polynomially bounded, and retains its
literal predecessor. -/
theorem run_total (spec : Spec.{uPrevious, uDemand, uPayer} Previous)
    (capability : Capability spec) (previous : Previous) :
    Exists fun result : ExecutionResult spec capability =>
      result.stage.previous = previous ∧
      OutcomeClaim result.outcome ∧
      result.traceNodes = Trace.expectedNodes result.terminal ∧
      result.checks <= capability.workCoefficient *
        (capability.inputSize previous + 1) ^ capability.workDegree := by
  let result := run spec capability previous
  exact ⟨result, rfl, result.verified, result.trace_exact,
    result.checks_le_polynomial⟩

/-- Reference execution is deterministic in relational form. -/
theorem run_deterministic
    (spec : Spec.{uPrevious, uDemand, uPayer} Previous)
    (capability : Capability spec) (previous : Previous)
    (first second : ExecutionResult spec capability)
    (firstIsRun : first = run spec capability previous)
    (secondIsRun : second = run spec capability previous) : first = second :=
  firstIsRun.trans secondIsRun.symm

/-- Exhaustive terminal grammar for a completed execution. -/
theorem outcome_exhaustive {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.terminal = .missingPayer ∨
      result.terminal = .overloadedFibre ∨
      result.terminal = .c4 ∨ result.terminal = .capacity :=
  result.outcome.terminal_exhaustive

end Hypostructure.CT4
