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

/-! ## Good-terminal replacement extraction -/

/-- A CT3 replacement candidate with all structural facts needed by downstream
compression consumers: admissibility in the inherited ambient object, strict
decrease, exact response equality, and derived response inclusion. -/
structure StrictResponseReplacement {P : Core.Problem} (S : Spec P)
    (input : Input S) where
  candidate : S.Candidate
  admissible : S.Admissible input.context.G input.piece candidate
  smaller : S.Smaller input.context.G input.piece candidate
  sameResponse : SameResponse S (S.candidatePiece candidate) input.piece

namespace StrictResponseReplacement

theorem included {P : Core.Problem} {S : Spec P} {input : Input S}
    (replacement : StrictResponseReplacement S input) :
    ResponseIncluded S (S.candidatePiece replacement.candidate) input.piece :=
  sameResponse_included S replacement.sameResponse

end StrictResponseReplacement

/-- Reusable bridge for CT3 tables whose exact rows are themselves admissible
strict replacement candidates.  This is framework-level plumbing: the
application supplies only the row-to-candidate interpretation and its local
semantic facts; CT3 owns the terminal extraction. -/
structure RowCandidateEmbedding {P : Core.Problem} (S : Spec P)
    (input : Input S) where
  rowCandidate : S.Row → S.Candidate
  rowCandidatePiece : ∀ row,
    S.candidatePiece (rowCandidate row) = S.rowPiece row
  rowAdmissible : ∀ row,
    S.Admissible input.context.G input.piece (rowCandidate row)
  rowSmaller : ∀ row,
    S.Smaller input.context.G input.piece (rowCandidate row)
  rowResponse_exact : ∀ row context,
    S.rowResponse row context = S.response (S.rowPiece row) context

/-- Compression facts already contain a strict same-response replacement. -/
def strictResponseReplacement_of_compresses {P : Core.Problem}
    {S : Spec P} {input : Input S} {candidate : S.Candidate}
    (compresses : Compresses S input candidate) :
    StrictResponseReplacement S input where
  candidate := candidate
  admissible := compresses.1
  smaller := compresses.2.1
  sameResponse := compresses.2.2

/-- A known exact table row becomes the same strict replacement once the table
row is interpreted as an admissible strictly smaller candidate. -/
def strictResponseReplacement_of_rowMatches {P : Core.Problem}
    {S : Spec P} {input : Input S} (embedding : RowCandidateEmbedding S input)
    {row : S.Row} (rowMatches : RowMatches S input row) :
    StrictResponseReplacement S input where
  candidate := embedding.rowCandidate row
  admissible := embedding.rowAdmissible row
  smaller := embedding.rowSmaller row
  sameResponse := by
    intro context
    calc
      S.response (S.candidatePiece (embedding.rowCandidate row)) context =
          S.response (S.rowPiece row) context := by
        rw [embedding.rowCandidatePiece row]
      _ = S.rowResponse row context := by
        rw [embedding.rowResponse_exact row context]
      _ = S.response input.piece context := by
        exact (rowMatches context).symm

end StructuralExhaustion.CT3
