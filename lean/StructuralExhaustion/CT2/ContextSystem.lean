import StructuralExhaustion.CT2.InterfaceSystem

namespace StructuralExhaustion.CT2

universe uAmbient uBranch uPiece uInterface uAbstract uContext

/-!
Exact outside contexts and gluing.  The reconstruction theorem is the single
representation bridge required by reference observation semantics.
-/

structure ContextSystem
    {P : Core.Problem.{uAmbient, uBranch}}
    {pieces : PieceSystem.{uAmbient, uBranch, uPiece} P}
    (interfaces : InterfaceSystem.{uAmbient, uBranch, uPiece, uInterface} pieces) where
  AbstractPiece : interfaces.Interface → Type uAbstract
  Context : interfaces.Interface → Type uContext
  contexts : (interface : interfaces.Interface) →
    FinEnum (Context interface)
  glue : {interface : interfaces.Interface} →
    Context interface → AbstractPiece interface → P.Ambient
  abstract : {G : P.Ambient} → (piece : pieces.Piece G) →
    AbstractPiece (interfaces.interface piece)
  currentContext : {G : P.Ambient} → (piece : pieces.Piece G) →
    Context (interfaces.interface piece)
  reconstruct : {G : P.Ambient} → (piece : pieces.Piece G) →
    glue (currentContext piece) (abstract piece) = G

end StructuralExhaustion.CT2
