import StructuralExhaustion.Core.AutomationFirst

namespace StructuralExhaustion.CT3

universe uAmbient uBranch uPiece uContext uCandidate uRow uCode

/-!
Problem-independent mathematical vocabulary for exact external-response
compression.  This layer contains no execution choice and no consumer tactic.
-/

/-- The problem-specific semantics needed by CT3.  `response` is the canonical
external type: the exact Boolean response vector over the declared context
universe.  Table rows may use a stored vector, but the runner validates it
against `rowPiece` before trusting it. -/
structure Spec (P : Core.Problem.{uAmbient, uBranch}) where
  Piece : Type uPiece
  Context : Type uContext
  Candidate : Type uCandidate
  Row : Type uRow
  response : Piece → Context → Bool
  candidatePiece : Candidate → Piece
  Admissible : P.Ambient → Piece → Candidate → Prop
  Smaller : P.Ambient → Piece → Candidate → Prop
  rowPiece : Row → Piece
  rowResponse : Row → Context → Bool

/-- The exact response vector of a piece. -/
def ExactResponse {P : Core.Problem.{uAmbient, uBranch}} (S : Spec P)
    (piece : S.Piece) : S.Context → Bool :=
  S.response piece

/-- Exact response equality.  There is no quotient, coarse label, or hidden
congruence in this relation. -/
def SameResponse {P : Core.Problem.{uAmbient, uBranch}} (S : Spec P)
    (left right : S.Piece) : Prop :=
  ∀ context, S.response left context = S.response right context

/-- Response inclusion is retained as a derived structural fact for consumers
that need only monotonicity. -/
def ResponseIncluded {P : Core.Problem.{uAmbient, uBranch}} (S : Spec P)
    (left right : S.Piece) : Prop :=
  ∀ context, S.response left context = true →
    S.response right context = true

theorem sameResponse_included {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P) {left right : S.Piece}
    (same : SameResponse S left right) : ResponseIncluded S left right := by
  intro context leftTrue
  rw [same context] at leftTrue
  exact leftTrue

/-- Optional compact encodings are accepted only through one reusable
refinement theorem back to the canonical exact vector. -/
structure CompactCodeRefinement {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P) (Code : Type uCode) where
  encode : S.Piece → Code
  decode : Code → S.Context → Bool
  refines : ∀ piece context,
    decode (encode piece) context = S.response piece context

namespace CompactCodeRefinement

theorem sameCode_sameResponse {P : Core.Problem.{uAmbient, uBranch}}
    {S : Spec P} {Code : Type uCode}
    (refinement : CompactCodeRefinement S Code)
    {left right : S.Piece}
    (sameCode : refinement.encode left = refinement.encode right) :
    SameResponse S left right := by
  intro context
  rw [← refinement.refines left context, ← refinement.refines right context,
    sameCode]

end CompactCodeRefinement

end StructuralExhaustion.CT3
