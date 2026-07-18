import StructuralExhaustion.Graph.TypeADeclaredContinuationCoordinate
import StructuralExhaustion.Graph.NegativeSupportHandoff

namespace StructuralExhaustion.Graph.TypeASeparatorHandoff

open StructuralExhaustion
open TypeACanonicalReceiverTrace

universe u v w x y

variable {V : Type u} (object : FiniteObject V)
variable (profile : SupportProfile object)
variable (port : TypeAAnchoredReturnCoordinate.Port object profile)
variable {Label : Type v} {SupportDatum : Type w} {Value : Type x} {Fibre : Type y}

abbrev Family := TypeADeclaredContinuationCoordinate.Family object profile port
  Label SupportDatum Value Fibre

abbrev Separator
    (family : Family object profile port (Label := Label)
      (SupportDatum := SupportDatum) (Value := Value) (Fibre := Fibre)) :=
  TypeADeclaredContinuationCoordinate.Family.Separator object profile port family

namespace Separator

variable {family : Family object profile port (Label := Label)
  (SupportDatum := SupportDatum) (Value := Value) (Fibre := Fibre)}

private noncomputable def armOf
    (separator : Separator object profile port family)
    (coordinate : TypeADeclaredContinuationCoordinate.Coordinate object profile port
      Label SupportDatum Value Fibre)
    (_coordinate_eq_left : coordinate = separator.left) :
    NegativeSupportHandoff.Arm object profile.support
      (separator.vertex object profile port) := by
  subst coordinate
  let deletedPath := separator.left.connector.path.drop (separator.branch.index + 1)
  let ambientPath := deletedPath.mapLe (object.graph.deleteEdges_le _)
  refine {
    first := separator.left.connector.path.getVert (separator.branch.index + 1)
    terminal := separator.left.first.entry object profile port separator.left.anchored
    center_adjacent := by
      simpa [TypeADeclaredContinuationCoordinate.Family.Separator.leftNext] using
        separator.left_ambient_adjacent object profile port
    terminal_mem := separator.left.first.entry_mem_support object profile port
      separator.left.anchored
    path := ?_
    isPath := ?_
    firstEntry := ?_
    center_avoided := ?_ }
  · exact ambientPath
  · dsimp [ambientPath, deletedPath]
    exact (separator.left.connector.isPath.drop
      (separator.branch.index + 1)).mapLe (object.graph.deleteEdges_le _)
  · intro vertex member memberCore
    have memberDeleted : vertex ∈ deletedPath.support := by
      simpa [ambientPath, SimpleGraph.Walk.support_mapLe_eq_support] using member
    have memberWhole : vertex ∈ separator.left.connector.path.support := by
      rw [SimpleGraph.Walk.drop_support_eq_support_drop_min] at memberDeleted
      exact List.mem_of_mem_drop memberDeleted
    by_contra notTerminal
    exact separator.left.connector.support_before_outside object profile port
      separator.left.anchored separator.left.first vertex memberWhole notTerminal memberCore
  · intro centerMember
    have centerMemberDeleted : separator.vertex object profile port ∈ deletedPath.support := by
      simpa [ambientPath, SimpleGraph.Walk.support_mapLe_eq_support] using centerMember
    have suffix : deletedPath.support =
        separator.left.connector.path.support.drop (separator.branch.index + 1) := by
      simp [deletedPath, SimpleGraph.Walk.drop_support_eq_support_drop_min]
      have indexLe : separator.branch.index + 1 ≤ separator.left.connector.path.length := by
        have bound : separator.branch.index < separator.left.connector.path.length := by
          simpa [TypeADeclaredContinuationCoordinate.Coordinate.tail,
            TypeADeclaredContinuationCoordinate.Coordinate.word,
            SimpleGraph.Walk.length_support] using separator.branch.leftBound
        omega
      omega
    rw [suffix] at centerMemberDeleted
    have centerBound : separator.branch.index <
        separator.left.connector.path.support.length := by
      have pathBound : separator.branch.index < separator.left.connector.path.length := by
        simpa [TypeADeclaredContinuationCoordinate.Coordinate.tail,
          TypeADeclaredContinuationCoordinate.Coordinate.word,
          SimpleGraph.Walk.length_support] using separator.branch.leftBound
      rw [SimpleGraph.Walk.length_support]
      omega
    have centerAt : separator.left.connector.path.support[separator.branch.index]'centerBound =
        separator.vertex object profile port := by
      exact (SimpleGraph.Walk.support_getElem_eq_getVert
        separator.left.connector.path centerBound).trans rfl
    have nodup := separator.left.connector.isPath.support_nodup
    obtain ⟨j, jBound, atJ⟩ := List.mem_iff_getElem.mp centerMemberDeleted
    have laterBound : separator.branch.index + 1 + j <
        separator.left.connector.path.support.length := by
      rw [List.length_drop] at jBound
      omega
    have sameValue :
        separator.left.connector.path.support[separator.branch.index]'centerBound =
          separator.left.connector.path.support[separator.branch.index + 1 + j]'laterBound := by
      rw [centerAt, ← atJ]
      exact List.getElem_drop (i := separator.branch.index + 1) (j := j)
    have sameIndex : separator.branch.index = separator.branch.index + 1 + j :=
      nodup.getElem_inj_iff.mp sameValue
    omega

noncomputable def leftArm
    (separator : Separator object profile port family) :
    NegativeSupportHandoff.Arm object profile.support
      (separator.vertex object profile port) :=
  separator.armOf object profile port separator.left rfl

noncomputable def rightArm
    (separator : Separator object profile port family) :
    NegativeSupportHandoff.Arm object profile.support
      (separator.vertex object profile port) := by
  let deletedPath := separator.right.connector.path.drop (separator.branch.index + 1)
  let ambientPath := deletedPath.mapLe (object.graph.deleteEdges_le _)
  refine {
    first := separator.right.connector.path.getVert (separator.branch.index + 1)
    terminal := separator.right.first.entry object profile port separator.right.anchored
    center_adjacent := by
      simpa [TypeADeclaredContinuationCoordinate.Family.Separator.rightNext] using
        separator.right_ambient_adjacent object profile port
    terminal_mem := separator.right.first.entry_mem_support object profile port
      separator.right.anchored
    path := ambientPath
    isPath := ?_
    firstEntry := ?_
    center_avoided := ?_ }
  · dsimp [ambientPath, deletedPath]
    exact (separator.right.connector.isPath.drop
      (separator.branch.index + 1)).mapLe (object.graph.deleteEdges_le _)
  · intro vertex member memberCore
    have memberDeleted : vertex ∈ deletedPath.support := by
      simpa [ambientPath, SimpleGraph.Walk.support_mapLe_eq_support] using member
    have memberWhole : vertex ∈ separator.right.connector.path.support := by
      rw [SimpleGraph.Walk.drop_support_eq_support_drop_min] at memberDeleted
      exact List.mem_of_mem_drop memberDeleted
    by_contra notTerminal
    exact separator.right.connector.support_before_outside object profile port
      separator.right.anchored separator.right.first vertex memberWhole notTerminal memberCore
  · intro centerMember
    have centerMemberDeleted : separator.vertex object profile port ∈ deletedPath.support := by
      simpa [ambientPath, SimpleGraph.Walk.support_mapLe_eq_support] using centerMember
    have suffix : deletedPath.support =
        separator.right.connector.path.support.drop (separator.branch.index + 1) := by
      simp [deletedPath, SimpleGraph.Walk.drop_support_eq_support_drop_min]
      have indexLe : separator.branch.index + 1 ≤ separator.right.connector.path.length := by
        have bound : separator.branch.index < separator.right.connector.path.length := by
          simpa [TypeADeclaredContinuationCoordinate.Coordinate.tail,
            TypeADeclaredContinuationCoordinate.Coordinate.word,
            SimpleGraph.Walk.length_support] using separator.branch.rightBound
        omega
      omega
    rw [suffix] at centerMemberDeleted
    have centerBound : separator.branch.index <
        separator.right.connector.path.support.length := by
      have pathBound : separator.branch.index < separator.right.connector.path.length := by
        simpa [TypeADeclaredContinuationCoordinate.Coordinate.tail,
          TypeADeclaredContinuationCoordinate.Coordinate.word,
          SimpleGraph.Walk.length_support] using separator.branch.rightBound
      rw [SimpleGraph.Walk.length_support]
      omega
    have centerAt : separator.right.connector.path.support[separator.branch.index]'centerBound =
        separator.vertex object profile port := by
      calc
        separator.right.connector.path.support[separator.branch.index]'centerBound =
            separator.right.connector.path.getVert separator.branch.index :=
          SimpleGraph.Walk.support_getElem_eq_getVert
            separator.right.connector.path centerBound
        _ = separator.vertex object profile port :=
          separator.right_vertex_eq object profile port
    have nodup := separator.right.connector.isPath.support_nodup
    obtain ⟨j, jBound, atJ⟩ := List.mem_iff_getElem.mp centerMemberDeleted
    have laterBound : separator.branch.index + 1 + j <
        separator.right.connector.path.support.length := by
      rw [List.length_drop] at jBound
      omega
    have sameValue :
        separator.right.connector.path.support[separator.branch.index]'centerBound =
          separator.right.connector.path.support[separator.branch.index + 1 + j]'laterBound := by
      rw [centerAt, ← atJ]
      exact List.getElem_drop (i := separator.branch.index + 1) (j := j)
    have sameIndex : separator.branch.index = separator.branch.index + 1 + j :=
      nodup.getElem_inj_iff.mp sameValue
    omega

@[simp] theorem leftArm_first
    (separator : Separator object profile port family) :
    (separator.leftArm object profile port).first =
      separator.leftNext object profile port :=
  rfl

@[simp] theorem rightArm_first
    (separator : Separator object profile port family) :
    (separator.rightArm object profile port).first =
      separator.rightNext object profile port :=
  rfl

end Separator

end StructuralExhaustion.Graph.TypeASeparatorHandoff
