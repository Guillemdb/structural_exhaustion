import StructuralExhaustion.Examples.DeletedEdgeReturnThirdIncidence
import StructuralExhaustion.Graph.DeletedEdgeReturnChordResolution

namespace StructuralExhaustion.Examples.DeletedEdgeReturnChordResolutionK4

open StructuralExhaustion
open DeletedEdgeReturnThirdIncidenceK4

/-!
The textbook graph `K₄` transfer fixture reuses the exact predecessor run on
the return `1-2-3-0`.  Its selected third endpoint is at canonical support
index two, so the local chord is a triangle.  A triangle target exercises the
accepted branch; the exact-length-four predicate exercises the shorter-return
branch on the identical input.
-/

noncomputable def input : Graph.DeletedEdgeReturnChordResolution.Input chordSetup where
  member := by native_decide
  runExact := rfl

example : input.index = 2 := by native_decide

example : input.chordCycle.length = 3 := by
  rw [input.chordCycle_length]
  native_decide

instance (length : Nat) : Decidable (Graph.TriangleLength length) := by
  unfold Graph.TriangleLength
  infer_instance

example : match Graph.DeletedEdgeReturnChordResolution.run input Graph.TriangleLength inferInstance with
  | .target certificate => certificate.walk.length = 3
  | .rejected _ _ _ _ => False := by
  change (input.chordCycle.length = 3)
  exact input.chordCycle_length.trans (by native_decide)

def LengthFour (length : Nat) : Prop := length = 4

instance (length : Nat) : Decidable (LengthFour length) := by
  unfold LengthFour
  infer_instance

example : match Graph.DeletedEdgeReturnChordResolution.run input LengthFour inferInstance with
  | .target _ => False
  | .rejected _ shorter _ strict =>
      shorter.path.length < chordSetup.returnPath.path.length := by
  change input.shorterReturn.path.length < chordSetup.returnPath.path.length
  exact input.shorterReturn_strict

example : Graph.DeletedEdgeReturnChordResolution.visibleChecks input ≤
    chordSetup.returnPath.path.support.length + 1 :=
  Graph.DeletedEdgeReturnChordResolution.visibleChecks_le input (by rfl)

end StructuralExhaustion.Examples.DeletedEdgeReturnChordResolutionK4
