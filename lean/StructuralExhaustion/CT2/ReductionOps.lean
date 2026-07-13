import StructuralExhaustion.CT2.PieceSystem

namespace StructuralExhaustion.CT2

universe uAmbient uBranch uPiece

/-! Proof-carrying deletion; decrease is part of the operation result. -/

structure ReductionOps
    {P : Core.Problem.{uAmbient, uBranch}}
    (pieces : PieceSystem.{uAmbient, uBranch, uPiece} P) where
  delete : {G : P.Ambient} → pieces.Piece G → Core.SmallerObject P G

end StructuralExhaustion.CT2
