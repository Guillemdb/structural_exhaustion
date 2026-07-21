import Hypostructure.CT8.Execution

/-!
# CT8 soundness, exact semantics, and totality
-/

namespace Hypostructure.CT8

universe uPrevious uState uType uContext uValue uRemoval

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uState, uType, uContext, uValue, uRemoval}
    Previous}

/-- Mathematical claim carried by each exact generated outcome. -/
def OutcomeClaim {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal -> Prop
  | .noRepetition, .noRepetition _certificate =>
      forall indices : OrderedIndexPair (capability.sequenceAt previous).length,
        Not (SameExactType capability previous indices)
  | .separation, .separation residual =>
      SameExactType capability previous residual.pair.indices ∧
        ResponseDiffers capability previous residual.pair
          residual.separator.context
  | .removal, .removal certificate =>
      SameExactType capability previous certificate.pair.indices ∧
        ResponsesEqual capability previous certificate.pair ∧
        certificate.replacement = capability.remove previous
          certificate.pair.first certificate.pair.second
          certificate.pair.typesEqual certificate.responsesEqual ∧
        spec.StrictlySmaller previous certificate.replacement

namespace Outcome

/-- Every framework-generated typed outcome proves its advertised claim. -/
theorem verified {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal) :
    OutcomeClaim outcome := by
  cases outcome with
  | noRepetition certificate =>
      exact certificate.typesDifferent
  | separation residual =>
      exact ⟨residual.pair.typesEqual, residual.separator.differs⟩
  | removal certificate =>
      exact ⟨certificate.pair.typesEqual, certificate.responsesEqual,
        certificate.replacement_exact, certificate.smaller⟩

end Outcome

namespace ExecutionResult

/-- Aggregate semantic soundness. -/
theorem verified {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    OutcomeClaim result.outcome :=
  result.outcome.verified

/-- The terminal index fixes the complete reference trace. -/
theorem trace_exact {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.traceNodes = Trace.expectedNodes result.terminal :=
  result.trace.nodes_eq_expected

/-- Pairwise exact-type distinction forces the no-repetition terminal. -/
theorem terminal_noRepetition_of_pairwiseDifferent
    {capability : Capability spec}
    (result : ExecutionResult spec capability)
    (different : forall indices :
      OrderedIndexPair (capability.sequenceAt result.stage.previous).length,
      Not (SameExactType capability result.stage.previous indices)) :
    result.terminal = .noRepetition := by
  cases terminal : result.terminal with
  | noRepetition => rfl
  | separation =>
      let residual := result.separationResidual terminal
      exact (different residual.pair.indices residual.pair.typesEqual).elim
  | removal =>
      let certificate := result.removalCertificate terminal
      exact (different certificate.pair.indices
        certificate.pair.typesEqual).elim

/-- Existence of a repetition and separation of every repeated pair force the
response-separation terminal. -/
theorem terminal_separation_of_repeated_of_separating
    {capability : Capability spec}
    (result : ExecutionResult spec capability)
    (repeated : Exists fun indices :
      OrderedIndexPair (capability.sequenceAt result.stage.previous).length =>
      SameExactType capability result.stage.previous indices)
    (separating : forall pair :
      OrderedRepeatedPair capability result.stage.previous,
      Exists fun context =>
        ResponseDiffers capability result.stage.previous pair context) :
    result.terminal = .separation := by
  cases terminal : result.terminal with
  | noRepetition =>
      let certificate := result.noRepetitionCertificate terminal
      obtain ⟨indices, sameType⟩ := repeated
      exact (certificate.typesDifferent indices sameType).elim
  | separation => rfl
  | removal =>
      let certificate := result.removalCertificate terminal
      obtain ⟨context, differs⟩ := separating certificate.pair
      exact (differs (certificate.responsesEqual context)).elim

/-- Existence of a repetition and response equality for every repeated pair
force the strict-removal terminal. -/
theorem terminal_removal_of_repeated_of_neutral
    {capability : Capability spec}
    (result : ExecutionResult spec capability)
    (repeated : Exists fun indices :
      OrderedIndexPair (capability.sequenceAt result.stage.previous).length =>
      SameExactType capability result.stage.previous indices)
    (neutral : forall pair :
      OrderedRepeatedPair capability result.stage.previous,
      ResponsesEqual capability result.stage.previous pair) :
    result.terminal = .removal := by
  cases terminal : result.terminal with
  | noRepetition =>
      let certificate := result.noRepetitionCertificate terminal
      obtain ⟨indices, sameType⟩ := repeated
      exact (certificate.typesDifferent indices sameType).elim
  | separation =>
      let residual := result.separationResidual terminal
      exact (residual.separator.differs
        (neutral residual.pair residual.separator.context)).elim
  | removal => rfl

end ExecutionResult

/-- Public reference execution is semantically sound. -/
theorem run_verified
    (spec : Spec.{uPrevious, uState, uType, uContext, uValue, uRemoval}
      Previous)
    (capability : Capability spec) (previous : Previous) :
    OutcomeClaim (run spec capability previous).outcome :=
  (run spec capability previous).verified

/-- CT8 is predecessor-exact, total, sound, exactly traced, and polynomially
bounded. -/
theorem run_total
    (spec : Spec.{uPrevious, uState, uType, uContext, uValue, uRemoval}
      Previous)
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

/-- The pure reference executor is deterministic. -/
theorem run_deterministic
    (spec : Spec.{uPrevious, uState, uType, uContext, uValue, uRemoval}
      Previous)
    (capability : Capability spec) (previous : Previous)
    (first second : ExecutionResult spec capability)
    (firstIsRun : first = run spec capability previous)
    (secondIsRun : second = run spec capability previous) : first = second :=
  firstIsRun.trans secondIsRun.symm

/-- No terminal outside the three CT8 alternatives is representable. -/
theorem outcome_exhaustive {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.terminal = .noRepetition ∨
      result.terminal = .separation ∨ result.terminal = .removal := by
  cases result.terminal <;> simp

end Hypostructure.CT8
