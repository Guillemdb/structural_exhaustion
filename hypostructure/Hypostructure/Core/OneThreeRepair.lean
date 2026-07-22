import Hypostructure.Core.AffineBalance

namespace Hypostructure.Core.OneThreeRepair

/-! Abstract one--three repair arithmetic.  Graph adapters provide only the
handshake and cycle-rank identities; this theorem performs the repair. -/

theorem identity
    {internal boundary edgeCount cycleRank surplus : Int}
    (handshake : 3 * internal + surplus + boundary =
      2 * edgeCount)
    (rank : cycleRank = edgeCount - internal - boundary + 1) :
    internal = boundary - 2 + 2 * cycleRank - surplus :=
  AffineBalance.solve_one_three handshake rank

end Hypostructure.Core.OneThreeRepair
