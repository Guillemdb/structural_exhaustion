import StructuralExhaustion.CT2.ContextSystem

namespace StructuralExhaustion.CT2

universe uAmbient uBranch uPiece uInterface uAbstract uContext uCandidate

/-! Exact finite legal replacements.  Legality is encoded by `Candidate`; the
operation itself carries the strict rank decrease required by minimality. -/

structure ReplacementSystem
    {P : Core.Problem.{uAmbient, uBranch}}
    {pieces : PieceSystem.{uAmbient, uBranch, uPiece} P}
    {interfaces : InterfaceSystem.{uAmbient, uBranch, uPiece, uInterface} pieces}
    (contexts : ContextSystem.{uAmbient, uBranch, uPiece, uInterface,
      uAbstract, uContext} interfaces) where
  Candidate : {G : P.Ambient} → pieces.Piece G → Type uCandidate
  candidates : {G : P.Ambient} → (piece : pieces.Piece G) →
    FinEnum (Candidate piece)
  replacement : {G : P.Ambient} → (piece : pieces.Piece G) →
    Candidate piece → contexts.AbstractPiece (interfaces.interface piece)
  decreases : {G : P.Ambient} → (piece : pieces.Piece G) →
    (candidate : Candidate piece) →
    P.rank (contexts.glue (contexts.currentContext piece)
      (replacement piece candidate)) < P.rank G

namespace ReplacementSystem

def asSmaller
    {P : Core.Problem.{uAmbient, uBranch}}
    {pieces : PieceSystem.{uAmbient, uBranch, uPiece} P}
    {interfaces : InterfaceSystem.{uAmbient, uBranch, uPiece, uInterface} pieces}
    {contexts : ContextSystem.{uAmbient, uBranch, uPiece, uInterface,
      uAbstract, uContext} interfaces}
    (replacements : ReplacementSystem.{uAmbient, uBranch, uPiece, uInterface,
      uAbstract, uContext, uCandidate} contexts)
    {G : P.Ambient} (piece : pieces.Piece G)
    (candidate : replacements.Candidate piece) : Core.SmallerObject P G where
  value := contexts.glue (contexts.currentContext piece)
    (replacements.replacement piece candidate)
  decreases := replacements.decreases piece candidate

end ReplacementSystem

end StructuralExhaustion.CT2
