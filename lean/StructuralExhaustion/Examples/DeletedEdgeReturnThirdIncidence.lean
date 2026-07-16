import StructuralExhaustion.Graph.DeletedEdgeReturnThirdIncidence

namespace StructuralExhaustion.Examples.DeletedEdgeReturnThirdIncidenceK4

open StructuralExhaustion

/-!
`K₄` gives a small non-Erdős transfer fixture for both exact outcomes.
For the dart `0→1`, the declared-order third incidence at root `1` is `3`.
It lies on the return `1–2–3–0`, and lies outside the shorter return
`1–2–0`.
-/

abbrev Vertex := Fin 4

def graph : SimpleGraph Vertex := ⊤

def input : Graph.FiniteInput graph where
  vertices := inferInstance
  decideAdj := by
    change DecidableRel fun left right : Vertex => left ≠ right
    infer_instance

def object : Graph.FiniteObject Vertex := ⟨graph, input⟩

def rootDart : object.graph.Dart := ⟨(0, 1), by
  change (0 : Vertex) ≠ 1
  decide⟩

def chordWalk : (object.graph.deleteEdges {rootDart.edge}).Walk 1 0 :=
  .cons (v := 2) (by
      simp [object, graph, rootDart, SimpleGraph.Dart.edge])
    (.cons (v := 3) (by
        simp [object, graph, rootDart, SimpleGraph.Dart.edge])
      (.cons (v := 0) (by
        simp [object, graph, rootDart, SimpleGraph.Dart.edge]) .nil))

def outsideWalk : (object.graph.deleteEdges {rootDart.edge}).Walk 1 0 :=
  .cons (v := 2) (by
      simp [object, graph, rootDart, SimpleGraph.Dart.edge])
    (.cons (v := 0) (by
      simp [object, graph, rootDart, SimpleGraph.Dart.edge]) .nil)

def chordReturn : Graph.DartReturn object.graph rootDart where
  path := chordWalk
  isPath := by native_decide

def outsideReturn : Graph.DartReturn object.graph rootDart where
  path := outsideWalk
  isPath := by native_decide

def chordSetup :
    Graph.DeletedEdgeReturnThirdIncidence.Setup object rootDart where
  returnPath := chordReturn
  degree_ge_three := by native_decide
  root_not_high := by native_decide

def outsideSetup :
    Graph.DeletedEdgeReturnThirdIncidence.Setup object rootDart where
  returnPath := outsideReturn
  degree_ge_three := by native_decide
  root_not_high := by native_decide

example : chordSetup.firstNext = 2 := by native_decide

example : chordSetup.third.hit.value = 3 := by native_decide

example : match Graph.DeletedEdgeReturnThirdIncidence.run chordSetup with
  | .nonRootChord _ => True
  | .outsideBoundary _ => False := by
  change True
  trivial

example : outsideSetup.third.hit.value = 3 := by native_decide

example : match Graph.DeletedEdgeReturnThirdIncidence.run outsideSetup with
  | .nonRootChord _ => False
  | .outsideBoundary _ => True := by
  change True
  trivial

example :
    Graph.DeletedEdgeReturnThirdIncidence.visibleChecks chordSetup ≤
      2 * object.input.vertices.card + 3 + 4 :=
  Graph.DeletedEdgeReturnThirdIncidence.visibleChecks_le chordSetup
    (scale := 4) (by native_decide)

end StructuralExhaustion.Examples.DeletedEdgeReturnThirdIncidenceK4
