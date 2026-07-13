import StructuralExhaustion.CT3.Execution

namespace StructuralExhaustion.CT3

namespace RawOutcome

/-- Each terminal proves exactly its advertised structural fact. -/
theorem verified {P : Core.Problem} {S : Spec P} {C : Capability S}
    {input : Input S} {terminal : Graph.Terminal}
    (outcome : RawOutcome S C input terminal) : OutcomeClaim outcome := by
  cases outcome with
  | compression certificate => exact certificate.valid
  | distinguishing residual => exact residual.differs
  | knownRow certificate => exact certificate.rowMatches
  | novelRow residual => exact residual.novel

end RawOutcome

namespace ExecutionResult

theorem verified {P : Core.Problem} {S : Spec P} {C : Capability S}
    {input : Input S} (result : ExecutionResult S C input) :
    OutcomeClaim result.outcome :=
  result.outcome.verified

theorem traceValid {P : Core.Problem} {S : Spec P} {C : Capability S}
    {input : Input S} (result : ExecutionResult S C input) :
    @Graph.ValidTrace P S C input result.trace :=
  ⟨result.terminal, result.path, rfl⟩

end ExecutionResult

/-- Aggregate soundness of reference execution. -/
theorem run_verified {P : Core.Problem} (S : Spec P) (C : Capability S)
    (input : Input S) : OutcomeClaim (run S C input).outcome :=
  (run S C input).verified

/-- Every erased trace is backed by an exact dependent path. -/
theorem run_trace_valid {P : Core.Problem} (S : Spec P) (C : Capability S)
    (input : Input S) :
    @Graph.ValidTrace P S C input (run S C input).trace :=
  (run S C input).traceValid

/-- Exact finite capabilities make CT3 total. -/
theorem run_total {P : Core.Problem} (S : Spec P) (C : Capability S)
    (input : Input S) :
    ∃ result : ExecutionResult S C input,
      OutcomeClaim result.outcome ∧
        @Graph.ValidTrace P S C input result.trace := by
  let result := run S C input
  exact ⟨result, result.verified, result.traceValid⟩

/-- Reference execution is a pure function and has one typed result. -/
theorem run_deterministic {P : Core.Problem} (S : Spec P)
    (C : Capability S) (input : Input S)
    (first second : ExecutionResult S C input)
    (firstRun : first = run S C input)
    (secondRun : second = run S C input) : first = second :=
  firstRun.trans secondRun.symm

/-- The result space is exactly the four structural CT3 alternatives. -/
theorem outcome_exhaustive {P : Core.Problem} {S : Spec P}
    {C : Capability S} {input : Input S}
    (result : ExecutionResult S C input) :
    result.terminal = .compression ∨
      result.terminal = .distinguishing ∨
      result.terminal = .knownRow ∨
      result.terminal = .novelRow := by
  cases result with
  | mk _ _ outcome =>
      cases outcome with
      | compression _ => exact Or.inl rfl
      | distinguishing _ => exact Or.inr (Or.inl rfl)
      | knownRow _ => exact Or.inr (Or.inr (Or.inl rfl))
      | novelRow _ => exact Or.inr (Or.inr (Or.inr rfl))

/-- Exact-vector certification exposes literal equality with the semantic
response function. -/
theorem exact_vector_sound {P : Core.Problem} (S : Spec P)
    (input : Input S) :
    (computeExactVector S input).vector = S.response input.piece :=
  rfl

/-- Compression evidence includes admissibility, strict decrease, exact
preservation, and therefore response inclusion. -/
theorem compression_sound {P : Core.Problem} {S : Spec P}
    {C : Capability S} {input : Input S}
    {vector : ExactVectorState S input}
    (certificate : CompressionCertificate S C input vector) :
    S.Admissible input.context.G input.piece certificate.candidate ∧
      S.Smaller input.context.G input.piece certificate.candidate ∧
      SameResponse S (S.candidatePiece certificate.candidate) input.piece ∧
      ResponseIncluded S (S.candidatePiece certificate.candidate) input.piece :=
  ⟨certificate.valid.1, certificate.valid.2.1,
    certificate.valid.2.2, certificate.included⟩

/-- The clean prefix stored in a compression certificate proves that no
earlier candidate was valid. -/
theorem compression_is_first {P : Core.Problem} {S : Spec P}
    {C : Capability S} {input : Input S}
    {vector : ExactVectorState S input}
    (certificate : CompressionCertificate S C input vector) :
    ∀ candidate, candidate ∈ certificate.hit.before →
      ¬ Compresses S input candidate :=
  certificate.hit.beforeAbsent

/-- An uncompressible state excludes every candidate, not merely the rows
visited by an implementation shortcut. -/
theorem uncompressible_complete {P : Core.Problem} {S : Spec P}
    {C : Capability S} {input : Input S}
    {vector : ExactVectorState S input}
    (state : UncompressibleExternalType S C input vector) :
    ∀ candidate, ¬ Compresses S input candidate :=
  state.noCandidate

/-- A validated table agrees pointwise with each representative. -/
theorem exact_table_sound {P : Core.Problem} {S : Spec P}
    {C : Capability S} (table : ExactTableState S C) :
    ∀ row context,
      S.response (S.rowPiece row) context = S.rowResponse row context :=
  table.exact

end StructuralExhaustion.CT3
