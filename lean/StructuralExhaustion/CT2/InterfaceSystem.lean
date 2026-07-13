import StructuralExhaustion.CT2.PieceSystem

namespace StructuralExhaustion.CT2

universe uAmbient uBranch uPiece uInterface

/-! The interface type and canonical interface of each piece. CT2 only
enumerates the compatible contexts for the selected interface; it never
enumerates the global interface type. -/

structure InterfaceSystem
    {P : Core.Problem.{uAmbient, uBranch}}
    (pieces : PieceSystem.{uAmbient, uBranch, uPiece} P) where
  Interface : Type uInterface
  interface : {G : P.Ambient} → pieces.Piece G → Interface

end StructuralExhaustion.CT2
