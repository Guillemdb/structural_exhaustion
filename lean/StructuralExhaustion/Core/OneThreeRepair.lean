import Mathlib.Tactic

namespace StructuralExhaustion.Core.OneThreeRepair

/-!
# Exact one--three repair accounting

This is the arithmetic kernel for a connected repair component whose boundary
vertices are leaves and whose internal degree sum is cubic plus a recorded
surplus.  The theorem is stated over integers so that the manuscript identity
does not silently use truncated natural subtraction.
-/

/-- Handshake plus the connected cycle-rank identity imply the exact
one--three repair formula. -/
theorem identity
    (internalVertices boundaryLeaves internalEdges cycleRank surplus : Int)
    (handshake :
      3 * internalVertices + surplus + boundaryLeaves =
        2 * (internalEdges + boundaryLeaves))
    (cycleRankEq : cycleRank = internalEdges - internalVertices + 1) :
    internalVertices =
      boundaryLeaves - 2 + 2 * cycleRank - surplus := by
  omega

end StructuralExhaustion.Core.OneThreeRepair
