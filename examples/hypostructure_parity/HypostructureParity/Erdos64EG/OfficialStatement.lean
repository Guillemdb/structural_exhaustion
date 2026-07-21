import Erdos64EG.OfficialStatement
import HypostructureErdos64EG.OfficialStatement

namespace HypostructureParity.Erdos64EG

universe u

/-!
# Official-statement parity

This test-only theorem compares the two pinned public propositions directly in
Mathlib's `SimpleGraph` vocabulary.
-/

/-- The legacy and Hypostructure applications expose the exact same official
mathematical proposition. -/
theorem officialStatement_iff :
    _root_.Erdos64EG.OfficialStatement.{u} ↔
      HypostructureErdos64EG.OfficialStatement.{u} := by
  constructor
  · intro legacy V G _ _ minimumDegree
    exact legacy V G minimumDegree
  · intro modern V G _ _ minimumDegree
    exact modern V G minimumDegree

#print axioms officialStatement_iff

end HypostructureParity.Erdos64EG
