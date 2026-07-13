import StructuralExhaustion.Core.AutomationFirst

namespace StructuralExhaustion.CT2

universe uAmbient uBranch uPiece

/-!
Finite, branch-indexed pieces and automatic CT2 trigger discovery.

The piece universe and the two local predicates are mathematical instance data.
The search procedure and its absence proof belong to the framework.
-/

/-- Problem-specific pieces and their exact Mathlib finite enumeration. -/
structure PieceSystem (P : Core.Problem.{uAmbient, uBranch}) where
  Piece : P.Ambient → Type uPiece
  pieces : (G : P.Ambient) → FinEnum (Piece G)
  Proper : {G : P.Ambient} → Piece G → Prop
  Admissible : {G : P.Ambient} → P.BranchState G → Piece G → Prop
  properDecidable : {G : P.Ambient} → (piece : Piece G) → Decidable (Proper piece)
  admissibleDecidable : {G : P.Ambient} → (branch : P.BranchState G) →
    (piece : Piece G) → Decidable (Admissible branch piece)

/-- The minimal semantic seed required to invoke CT2. -/
structure Seed {P : Core.Problem.{uAmbient, uBranch}}
    (pieces : PieceSystem.{uAmbient, uBranch, uPiece} P)
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target) where
  piece : pieces.Piece ctx.G
  proper : pieces.Proper piece
  admissible : pieces.Admissible ctx.state piece

namespace PieceSystem

/-- The predicate searched by CT2 capability discovery. -/
def Eligible {P : Core.Problem.{uAmbient, uBranch}}
    (pieces : PieceSystem.{uAmbient, uBranch, uPiece} P)
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target)
    (piece : pieces.Piece ctx.G) : Prop :=
  pieces.Proper piece ∧ pieces.Admissible ctx.state piece

/-- Eligibility is decidable from the primitive problem specification. -/
def eligibleDecidable {P : Core.Problem.{uAmbient, uBranch}}
    (pieces : PieceSystem.{uAmbient, uBranch, uPiece} P)
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target)
    (piece : pieces.Piece ctx.G) : Decidable (pieces.Eligible ctx piece) :=
  @instDecidableAnd _ _ (pieces.properDecidable piece)
    (pieces.admissibleDecidable ctx.state piece)

/-- Exhaustively discover the first proper admissible piece in enumeration
order, or prove that no such piece exists. -/
def discover {P : Core.Problem.{uAmbient, uBranch}}
    (pieces : PieceSystem.{uAmbient, uBranch, uPiece} P)
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target) :
    Core.Routing.Discovery (Seed pieces ctx) :=
  match Core.FiniteSearch.search (pieces.pieces ctx.G)
      (pieces.Eligible ctx) (pieces.eligibleDecidable ctx) with
  | .found piece eligible =>
      .enabled ⟨piece, eligible.1, eligible.2⟩
  | .absent absent =>
      .disabled fun seed => absent seed.piece ⟨seed.proper, seed.admissible⟩

theorem discover_enabled_sound {P : Core.Problem.{uAmbient, uBranch}}
    {pieces : PieceSystem.{uAmbient, uBranch, uPiece} P}
    {Target : P.Ambient → Prop}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {seed : Seed pieces ctx}
    (_h : pieces.discover ctx = .enabled seed) :
    pieces.Proper seed.piece ∧ pieces.Admissible ctx.state seed.piece := by
  exact ⟨seed.proper, seed.admissible⟩

theorem discover_disabled_complete {P : Core.Problem.{uAmbient, uBranch}}
    {pieces : PieceSystem.{uAmbient, uBranch, uPiece} P}
    {Target : P.Ambient → Prop}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {reject : Seed pieces ctx → False}
    (_h : pieces.discover ctx = .disabled reject) :
    ∀ piece : pieces.Piece ctx.G,
      ¬ pieces.Proper piece ∨ ¬ pieces.Admissible ctx.state piece := by
  intro piece
  cases hp : pieces.properDecidable piece with
  | isFalse notProper => exact Or.inl notProper
  | isTrue proper =>
      cases ha : pieces.admissibleDecidable ctx.state piece with
      | isFalse notAdmissible => exact Or.inr notAdmissible
      | isTrue admissible =>
          have seed : Seed pieces ctx := ⟨piece, proper, admissible⟩
          exact (reject seed).elim

end PieceSystem

end StructuralExhaustion.CT2
