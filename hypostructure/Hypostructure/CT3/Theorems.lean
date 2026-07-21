import Hypostructure.CT3.Execution

/-!
# CT3 soundness, totality, and transport
-/

namespace Hypostructure.CT3

universe uPrevious uRepresentative uContext uCoordinate uValue uCandidate uRow

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue,
    uCandidate, uRow} Previous}

namespace UncompressibleState

/-- Exhaustive failure excludes every member of the queried candidate
schedule. -/
theorem noCandidate {capability : Capability spec} {previous : Previous}
    (state : UncompressibleState capability previous)
    (candidate : spec.Candidate)
    (member : candidate ∈ (capability.candidatesAt previous).values) :
    Not (Compresses capability previous candidate) := by
  obtain ⟨index, indexed⟩ :=
    ((capability.candidatesAt previous).mem_iff_exists_index candidate).mp member
  exact fun compresses => state index (by simpa [indexed] using compresses)

end UncompressibleState

/-- Complete semantic claim advertised by each terminal. -/
def OutcomeClaim {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal -> Prop
  | .compression, .compression certificate =>
      Compresses capability previous certificate.candidate
  | .distinguishing, .distinguishing _ certificate =>
      (forall candidate,
        candidate ∈ (capability.candidatesAt previous).values ->
          Not (Compresses capability previous candidate)) ∧
      spec.system.coordinateResponse (spec.rowPiece certificate.row)
          certificate.coordinate ≠
        spec.rowResponse certificate.row certificate.coordinate
  | .knownRow, .knownRow _ _ certificate =>
      (forall candidate,
        candidate ∈ (capability.candidatesAt previous).values ->
          Not (Compresses capability previous candidate)) ∧
      (forall row,
        row ∈ (capability.rowsAt previous).values ->
          forall coordinate,
            coordinate ∈ (capability.coordinatesAt previous).values ->
              spec.system.coordinateResponse (spec.rowPiece row) coordinate =
                spec.rowResponse row coordinate) ∧
      RowMatches capability previous certificate.row
  | .novelRow, .novelRow _ _ _ =>
      (forall candidate,
        candidate ∈ (capability.candidatesAt previous).values ->
          Not (Compresses capability previous candidate)) ∧
      (forall row,
        row ∈ (capability.rowsAt previous).values ->
          forall coordinate,
            coordinate ∈ (capability.coordinatesAt previous).values ->
              spec.system.coordinateResponse (spec.rowPiece row) coordinate =
                spec.rowResponse row coordinate) ∧
      (forall row,
        row ∈ (capability.rowsAt previous).values ->
          Not (RowMatches capability previous row))

namespace Outcome

/-- Every framework-produced outcome proves its complete branch claim. -/
theorem verified {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal) :
    OutcomeClaim outcome := by
  cases outcome with
  | compression certificate => exact certificate.valid
  | distinguishing uncompressible certificate =>
      exact ⟨uncompressible.noCandidate, certificate.differs⟩
  | knownRow uncompressible table certificate =>
      exact ⟨uncompressible.noCandidate,
        fun _row rowMember _coordinate coordinateMember =>
          table.equalAt rowMember coordinateMember,
        certificate.rowMatches⟩
  | novelRow uncompressible table novel =>
      exact ⟨uncompressible.noCandidate,
        fun _row rowMember _coordinate coordinateMember =>
          table.equalAt rowMember coordinateMember,
        novel.noMatch⟩

/-- An actual scheduled compression witness excludes every non-compression
outcome. -/
theorem terminal_compression_of_exists
    {capability : Capability spec} {previous : Previous} {terminal : Terminal}
    (outcome : Outcome capability previous terminal)
    (existsCompression : Exists fun candidate =>
      candidate ∈ (capability.candidatesAt previous).values ∧
        Compresses capability previous candidate) :
    terminal = .compression := by
  obtain ⟨candidate, member, compresses⟩ := existsCompression
  cases outcome with
  | compression _ => rfl
  | distinguishing uncompressible _ =>
      exact (uncompressible.noCandidate candidate member compresses).elim
  | knownRow uncompressible _ _ =>
      exact (uncompressible.noCandidate candidate member compresses).elim
  | novelRow uncompressible _ _ =>
      exact (uncompressible.noCandidate candidate member compresses).elim

end Outcome

namespace ExecutionResult

/-- Aggregate semantic soundness. -/
theorem verified {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    OutcomeClaim result.outcome :=
  result.outcome.verified

/-- The terminal index fixes the complete trace. -/
theorem trace_exact {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.traceNodes = Trace.expectedNodes result.terminal :=
  result.trace.nodes_eq_expected

/-- An actual residual-owned compression witness forces the compression
terminal of any framework result. -/
theorem terminal_compression_of_exists {capability : Capability spec}
    (result : ExecutionResult spec capability)
    (existsCompression : Exists fun candidate =>
      candidate ∈ (capability.candidatesAt result.stage.previous).values ∧
        Compresses capability result.stage.previous candidate) :
    result.terminal = .compression :=
  result.outcome.terminal_compression_of_exists existsCompression

end ExecutionResult

/-- Public reference execution is semantically sound. -/
theorem run_verified
    (spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue,
      uCandidate, uRow} Previous)
    (capability : Capability spec) (previous : Previous) :
    OutcomeClaim (run spec capability previous).outcome :=
  (run spec capability previous).verified

/-- Exact finite capabilities make CT3 total, traced, and polynomially
bounded while preserving the literal predecessor. -/
theorem run_total
    (spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue,
      uCandidate, uRow} Previous)
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
    (spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue,
      uCandidate, uRow} Previous)
    (capability : Capability spec) (previous : Previous)
    (first second : ExecutionResult spec capability)
    (firstIsRun : first = run spec capability previous)
    (secondIsRun : second = run spec capability previous) : first = second :=
  firstIsRun.trans secondIsRun.symm

/-- No terminal outside the four CT3 alternatives is reachable. -/
theorem Outcome.terminal_exhaustive {capability : Capability spec}
    {previous : Previous} {terminal : Terminal}
    (outcome : Outcome capability previous terminal) :
    terminal = .compression ∨ terminal = .distinguishing ∨
      terminal = .knownRow ∨ terminal = .novelRow := by
  cases outcome with
  | compression _ => exact Or.inl rfl
  | distinguishing _ _ => exact Or.inr (Or.inl rfl)
  | knownRow _ _ _ => exact Or.inr (Or.inr (Or.inl rfl))
  | novelRow _ _ _ => exact Or.inr (Or.inr (Or.inr rfl))

theorem outcome_exhaustive {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.terminal = .compression ∨
      result.terminal = .distinguishing ∨
      result.terminal = .knownRow ∨
      result.terminal = .novelRow :=
  result.outcome.terminal_exhaustive

/-- Compression transports the registered target in every semantic context. -/
theorem CompressionCertificate.target_iff
    {capability : Capability spec} {previous : Previous}
    (certificate : CompressionCertificate capability previous)
    (context : spec.system.Context) :
    spec.semantics.TargetResponse (capability.sourceAt previous) context ↔
      spec.semantics.TargetResponse
        (spec.candidatePiece certificate.candidate) context :=
  certificate.targetComplete.targetIff context

/-- A validated known row transports the registered target in every semantic
context. -/
theorem KnownRowCertificate.target_iff
    {capability : Capability spec} {previous : Previous}
    (table : ExactTableState capability previous)
    (certificate : KnownRowCertificate capability previous)
    (context : spec.system.Context) :
    spec.semantics.TargetResponse (capability.sourceAt previous) context ↔
      spec.semantics.TargetResponse (spec.rowPiece certificate.row) context :=
  (certificate.targetComplete table).targetIff context

end Hypostructure.CT3
