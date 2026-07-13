import StructuralExhaustion.CT3.Capability

namespace StructuralExhaustion.CT3

universe uAmbient uBranch uPiece uContext uCandidate uRow

/-- CT3 receives the shared branch context and one source piece. -/
structure Input {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P) where
  context : Core.BranchContext P
  piece : S.Piece

namespace Input

/-- Materialize the runner input from a trigger whose dependent index fixes the
shared branch context. -/
def ofTrigger {P : Core.Problem.{uAmbient, uBranch}}
    {S : Spec P} (context : Core.BranchContext P)
    (trigger : Trigger S context) : Input S where
  context := context
  piece := trigger.piece

end Input

/-- Framework-produced exact-vector state.  The equality makes it impossible
for an execution to substitute an unverified compact or coarse type. -/
structure ExactVectorState {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P) (input : Input S) where
  vector : S.Context → Bool
  exact : vector = S.response input.piece

/-- Exact-vector certification is definitional. -/
def computeExactVector {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P) (input : Input S) :
    ExactVectorState S input where
  vector := S.response input.piece
  exact := rfl

/-- A candidate satisfies every structural condition checked by CT3. -/
def Compresses {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P) (input : Input S)
    (candidate : S.Candidate) : Prop :=
  S.Admissible input.context.G input.piece candidate ∧
  S.Smaller input.context.G input.piece candidate ∧
  SameResponse S (S.candidatePiece candidate) input.piece

/-- First valid compression candidate, including the exact clean prefix. -/
structure CompressionCertificate {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P)
    (C : Capability S) (input : Input S)
    (_vector : ExactVectorState S input) where
  hit : Core.FiniteSearch.FirstHit C.candidates.orderedValues (Compresses S input)

namespace CompressionCertificate

def candidate {P : Core.Problem.{uAmbient, uBranch}}
    {S : Spec P}
    {C : Capability S} {input : Input S} {vector : ExactVectorState S input}
    (certificate : CompressionCertificate S C input vector) : S.Candidate :=
  certificate.hit.value

theorem valid {P : Core.Problem.{uAmbient, uBranch}}
    {S : Spec P}
    {C : Capability S} {input : Input S} {vector : ExactVectorState S input}
    (certificate : CompressionCertificate S C input vector) :
    Compresses S input certificate.candidate :=
  certificate.hit.holds

theorem included {P : Core.Problem.{uAmbient, uBranch}}
    {S : Spec P}
    {C : Capability S} {input : Input S} {vector : ExactVectorState S input}
    (certificate : CompressionCertificate S C input vector) :
    ResponseIncluded S (S.candidatePiece certificate.candidate) input.piece :=
  sameResponse_included S certificate.valid.2.2

end CompressionCertificate

/-- Exhaustive failure of compression over the exact candidate universe. -/
structure UncompressibleExternalType {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P)
    (_C : Capability S) (input : Input S)
    (_vector : ExactVectorState S input) : Prop where
  noCandidate : ∀ candidate, ¬ Compresses S input candidate

/-- A concrete inconsistency between a declared table row and the exact
responses of its representative. -/
structure DistinguishingContextResidual
    {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P)
    (C : Capability S) (_input : Input S) where
  row : S.Row
  rowMember : row ∈ C.rows.orderedValues
  context : S.Context
  contextMember : context ∈ C.contexts.orderedValues
  differs :
    S.response (S.rowPiece row) context ≠ S.rowResponse row context

/-- Universal certification that every declared row is exact. -/
structure ExactTableState {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P)
    (_C : Capability S) : Prop where
  exact : ∀ row context,
    S.response (S.rowPiece row) context = S.rowResponse row context

/-- The source vector equals a declared exact row. -/
def RowMatches {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P)
    (input : Input S) (row : S.Row) : Prop :=
  ∀ context, S.response input.piece context = S.rowResponse row context

/-- The first table row equal to the source's exact vector. -/
structure KnownRowCertificate {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P)
    (C : Capability S) (input : Input S)
    (_table : ExactTableState S C) where
  hit : Core.FiniteSearch.FirstHit C.rows.orderedValues (RowMatches S input)

namespace KnownRowCertificate

def row {P : Core.Problem.{uAmbient, uBranch}}
    {S : Spec P}
    {C : Capability S} {input : Input S} {table : ExactTableState S C}
    (certificate : KnownRowCertificate S C input table) : S.Row :=
  certificate.hit.value

theorem rowMatches {P : Core.Problem.{uAmbient, uBranch}}
    {S : Spec P}
    {C : Capability S} {input : Input S} {table : ExactTableState S C}
    (certificate : KnownRowCertificate S C input table) :
    RowMatches S input certificate.row :=
  certificate.hit.holds

end KnownRowCertificate

/-- The source's exact external type is absent from the complete declared
table. -/
structure NovelExternalTypeResidual
    {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P)
    (_C : Capability S) (input : Input S)
    (_table : ExactTableState S _C) : Prop where
  novel : ∀ row, ¬ RowMatches S input row

end StructuralExhaustion.CT3
