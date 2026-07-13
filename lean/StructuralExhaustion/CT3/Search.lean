import StructuralExhaustion.CT3.State

namespace StructuralExhaustion.CT3

universe uAmbient uBranch uPiece uContext uCandidate uRow

/-- Exact response equality is decided by exhaustive context comparison. -/
def sameResponseDecidable {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P)
    (C : Capability S) (left right : S.Piece) :
    Decidable (SameResponse S left right) :=
  match Core.ResponseComparison.compare C.contexts
      (S.response left) (S.response right) with
  | .equal allEqual => .isTrue allEqual
  | .different context differs => .isFalse fun same =>
      differs (same context)

/-- All compression conditions are decided independently from the runner's
control flow. -/
def compressesDecidable {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P)
    (C : Capability S) (input : Input S) (candidate : S.Candidate) :
    Decidable (Compresses S input candidate) :=
  match C.admissibleDecidable input.context.G input.piece candidate with
  | .isFalse absent => .isFalse fun valid => absent valid.1
  | .isTrue admissible =>
      match C.smallerDecidable input.context.G input.piece candidate with
      | .isFalse absent => .isFalse fun valid => absent valid.2.1
      | .isTrue smaller =>
          match sameResponseDecidable S C (S.candidatePiece candidate)
              input.piece with
          | .isFalse absent => .isFalse fun valid => absent valid.2.2
          | .isTrue same => .isTrue ⟨admissible, smaller, same⟩

/-- Exhaustive ordered compression search. -/
inductive CompressionDecision {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P)
    (C : Capability S) (input : Input S)
    (vector : ExactVectorState S input) where
  | compressed (certificate : CompressionCertificate S C input vector)
  | uncompressible (state : UncompressibleExternalType S C input vector)

/-- Select the first valid compression candidate, or certify absence over the
entire exact candidate universe. -/
def findCompression {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P)
    (C : Capability S) (input : Input S)
    (vector : ExactVectorState S input) :
    CompressionDecision S C input vector :=
  match Core.FiniteSearch.first C.candidates (Compresses S input)
      (compressesDecidable S C input) with
  | .found hit => .compressed ⟨hit⟩
  | .absent absentProof => .uncompressible ⟨fun candidate =>
      absentProof candidate (C.candidates.mem_orderedValues candidate)⟩

/-- Result of validating every stored table bit against its representative. -/
inductive TableValidationDecision
    {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P)
    (C : Capability S) (input : Input S) where
  | defect (residual : DistinguishingContextResidual S C input)
  | exact (state : ExactTableState S C)

/-- Exhaustively validate the row/context product.  A hit is a concrete table
defect; absence establishes exactness of every row at every context. -/
def validateTable {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P)
    (C : Capability S) (input : Input S) : TableValidationDecision S C input :=
  let enumeration : Core.DependentEnumeration S.Row (fun _ => S.Context) := {
    indices := C.rows
    fibres := fun _ => C.contexts
  }
  match Core.FiniteSearch.dependentSearch enumeration
      (fun row context =>
        S.response (S.rowPiece row) context ≠ S.rowResponse row context)
      (fun _ _ => inferInstance) with
  | .found row context differs => .defect {
      row := row
      rowMember := C.rows.mem_orderedValues row
      context := context
      contextMember := C.contexts.mem_orderedValues context
      differs := differs
    }
  | .absent noDefect => .exact {
      exact := fun row context =>
        match decEq (S.response (S.rowPiece row) context)
            (S.rowResponse row context) with
        | .isTrue same => same
        | .isFalse differs => (noDefect row context differs).elim
    }

/-- Exact equality with one stored row is decidable by the common response
comparison engine. -/
def rowMatchesDecidable {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P)
    (C : Capability S) (input : Input S) (row : S.Row) :
    Decidable (RowMatches S input row) :=
  match Core.ResponseComparison.compare C.contexts
      (S.response input.piece) (S.rowResponse row) with
  | .equal allEqual => .isTrue allEqual
  | .different context differs => .isFalse fun same =>
      differs (same context)

/-- Result of exact lookup after table validation. -/
inductive RowLookupDecision {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P)
    (C : Capability S) (input : Input S)
    (table : ExactTableState S C) where
  | known (certificate : KnownRowCertificate S C input table)
  | novel (residual : NovelExternalTypeResidual S C input table)

/-- Select the first exact matching row or certify that the source vector is
novel relative to every row. -/
def lookupRow {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P)
    (C : Capability S) (input : Input S)
    (table : ExactTableState S C) : RowLookupDecision S C input table :=
  match Core.FiniteSearch.first C.rows (RowMatches S input)
      (rowMatchesDecidable S C input) with
  | .found hit => .known ⟨hit⟩
  | .absent absentProof => .novel ⟨fun row =>
      absentProof row (C.rows.mem_orderedValues row)⟩

end StructuralExhaustion.CT3
