import Mathlib.Combinatorics.SimpleGraph.Circulant
import StructuralExhaustion.Graph.OrderedBFSTree
import StructuralExhaustion.Graph.RootIncidence
import StructuralExhaustion.Graph.CubicStar

namespace StructuralExhaustion.Examples.OrderedBFSTreeK5

open StructuralExhaustion

/-! Concrete non-Erdős execution on `K₅`. -/

abbrev Vertex := Fin 5

def graph : SimpleGraph Vertex := ⊤

def input : Graph.FiniteInput graph where
  vertices := inferInstance
  decideAdj := by
    change DecidableRel fun left right : Vertex => left ≠ right
    infer_instance

def object : Graph.FiniteObject Vertex := ⟨graph, input⟩

def profile : Graph.OrderedBFSTree.Profile object where
  root := 0

def preconnected : object.graph.Preconnected := by
  intro left right
  by_cases equal : left = right
  · subst right
    exact .rfl
  · exact (show object.graph.Adj left right from equal).reachable

example : profile.discovered 0 = {0} := by native_decide

example : profile.layer 1 = {1, 2, 3, 4} := by native_decide

example : profile.discovered 1 = Finset.univ := by native_decide

example : profile.layer 2 = ∅ := by native_decide

/-- Every first-layer vertex selects the root as its declared-order first
parent. -/
example (vertex : Vertex) (nonroot : vertex ≠ 0) :
    profile.parent? 0 vertex = some 0 := by
  fin_cases vertex <;> simp_all <;> native_decide

example : profile.depth preconnected 0 = 0 :=
  profile.depth_root preconnected

example : profile.depth preconnected 4 = 1 := by native_decide

example : profile.treeParent preconnected 4 (by decide) = 0 := by native_decide

example : profile.depth preconnected
      (profile.treeParent preconnected 4 (by decide)) + 1 =
    profile.depth preconnected 4 :=
  profile.treeParent_depth_drop preconnected 4 (by decide)

example : (profile.treeWalk preconnected 4).length = 1 := by native_decide

example : (profile.treeWalk preconnected 4).IsPath :=
  profile.treeWalk_isPath preconnected 4

example : (profile.treeWalk preconnected 4).length =
    object.graph.dist profile.root 4 :=
  profile.treeWalk_shortest preconnected 4

example : profile.depth preconnected
      ((profile.treeWalk preconnected 4).getVert 1) = 1 :=
  profile.treeWalk_getVert_depth preconnected 4 1 (by native_decide)

example : (profile.treeWalk preconnected
      (profile.treeParent preconnected 4 (by decide))).support <+:
    (profile.treeWalk preconnected 4).support :=
  profile.parent_support_prefix preconnected 4 (by decide)

example : ∃ index : Nat,
    index ≤ (profile.treeWalk preconnected 3).length ∧
    index ≤ (profile.treeWalk preconnected 4).length ∧
    (profile.treeWalk preconnected 3).getVert index = 0 ∧
    (profile.treeWalk preconnected 4).getVert index = 0 :=
  profile.common_support_has_same_depth_index preconnected 3 4 0
    (profile.treeWalk preconnected 3).start_mem_support
    (profile.treeWalk preconnected 4).start_mem_support

example : (profile.treeWalk preconnected
      ((profile.treeWalk preconnected 4).getVert 0)).support =
    (profile.treeWalk preconnected 4).support.take 1 :=
  profile.treeWalk_getVert_support_eq_take preconnected 4 0 (by omega)

example : (profile.treeWalk preconnected 3).support.take 1 =
    (profile.treeWalk preconnected 4).support.take 1 :=
  profile.common_vertex_forces_equal_prefixes preconnected 3 4 0
    (profile.treeWalk preconnected 3).start_mem_support
    (profile.treeWalk preconnected 4).start_mem_support

example : (profile.compareTreePaths preconnected 3 4).common = [0] := by
  native_decide

example : (profile.compareTreePaths preconnected 3 4).leftRest = [3] := by
  native_decide

example : (profile.compareTreePaths preconnected 3 4).rightRest = [4] := by
  native_decide

/-- The scan's distinct residual branches cannot reconverge. -/
example : List.Disjoint ([3] : List Vertex) [4] :=
  profile.compareTreePaths_divergent_disjoint preconnected 3 4 3 4 [] []
    (by native_decide) (by native_decide) (by decide)

/-- The first residual vertex is connected to the common predecessor by an
actual graph edge, not merely by a list-level decomposition. -/
example : object.graph.Adj 0 3 :=
  profile.adjacent_at_support_boundary preconnected 3 0 3 [] []
    (by native_decide)

example : match profile.classifyTreePaths preconnected 3 4 with
  | .divergeAtRoot .. => True
  | _ => False := by
  change True
  trivial

/-- The equality convention chooses `leftPrefix` when both supports agree. -/
example : match profile.classifyTreePaths preconnected 3 3 with
  | .leftPrefix .. => True
  | _ => False := by
  change True
  trivial

def rootDivergence : Graph.RootIncidence.Divergence object 0 where
  leftNext := 3
  rightNext := 4
  leftAdjacent := by
    change (0 : Vertex) ≠ 3
    decide
  rightAdjacent := by
    change (0 : Vertex) ≠ 4
    decide
  distinct := by decide

/-- Non-Erdős transfer of the reusable incidence classifier: `K₅` takes
the high-degree branch after selecting the first neighbour other than 3,4. -/
example : match Graph.RootIncidence.classify object 0 (by native_decide)
      rootDivergence with
  | .high .. => True
  | _ => False := by
  change True
  trivial

example : profile.budget 5 ≤
    1 + 5 * (input.vertices.card * (input.vertices.card + 1)) :=
  profile.budget_polynomial 5

end StructuralExhaustion.Examples.OrderedBFSTreeK5

namespace StructuralExhaustion.Examples.OrderedBFSTreeBranch

open StructuralExhaustion

/-! A five-vertex tree whose two leaves split after the edge `0–1`. -/

abbrev Vertex := Fin 5

def forwardEdge (left right : Vertex) : Prop :=
  (left = 0 ∧ right = 1) ∨
  (left = 1 ∧ right = 2) ∨
  (left = 2 ∧ right = 3) ∨
  (left = 2 ∧ right = 4)

def graph : SimpleGraph Vertex := SimpleGraph.fromRel forwardEdge

def input : Graph.FiniteInput graph where
  vertices := inferInstance
  decideAdj := by
    unfold graph forwardEdge
    infer_instance

def object : Graph.FiniteObject Vertex := ⟨graph, input⟩

def profile : Graph.OrderedBFSTree.Profile object where
  root := 0

def preconnected : object.graph.Preconnected := by
  letI : DecidableRel object.graph.Adj := input.decideAdj
  have fromRoot : ∀ vertex : Vertex, object.graph.Reachable 0 vertex := by
    intro vertex
    fin_cases vertex
    · exact .rfl
    · exact (show object.graph.Adj 0 1 by
        simp [object, graph, forwardEdge]).reachable
    · exact (show object.graph.Adj 0 1 by
        simp [object, graph, forwardEdge]).reachable |>.trans
          (show object.graph.Adj 1 2 by
            simp [object, graph, forwardEdge]).reachable
    · exact ((show object.graph.Adj 0 1 by
        simp [object, graph, forwardEdge]).reachable |>.trans
          (show object.graph.Adj 1 2 by
            simp [object, graph, forwardEdge]).reachable) |>.trans
              (show object.graph.Adj 2 3 by
                simp [object, graph, forwardEdge]).reachable
    · exact ((show object.graph.Adj 0 1 by
        simp [object, graph, forwardEdge]).reachable |>.trans
          (show object.graph.Adj 1 2 by
            simp [object, graph, forwardEdge]).reachable) |>.trans
              (show object.graph.Adj 2 4 by
                simp [object, graph, forwardEdge]).reachable
  intro left right
  exact (fromRoot left).symm.trans (fromRoot right)

example : (profile.treeWalk preconnected 3).support = [0, 1, 2, 3] := by
  native_decide

example : (profile.treeWalk preconnected 4).support = [0, 1, 2, 4] := by
  native_decide

example : match profile.classifyTreePaths preconnected 3 4 with
  | .divergeAfterEdge .. => True
  | _ => False := by
  change True
  trivial

def separatorIncidence : Graph.RootIncidence.AfterEdge object 2 where
  predecessor := 1
  leftNext := 3
  rightNext := 4
  predecessorAdjacent := by simp [object, graph, forwardEdge]
  leftAdjacent := by simp [object, graph, forwardEdge]
  rightAdjacent := by simp [object, graph, forwardEdge]
  predecessor_ne_left := by decide
  predecessor_ne_right := by decide
  left_ne_right := by decide

/-- The branching-tree separator has exactly its three retained incidences,
so the generic after-edge classifier takes the cubic branch. -/
example : match Graph.RootIncidence.classifyAfterEdge object 2
      (by native_decide) separatorIncidence with
  | .cubic .. => True
  | _ => False := by
  change True
  trivial

example : Graph.RootIncidence.afterEdgeChecks = 1 := rfl

def cubicStar : Graph.CubicStar.Data object 2 :=
  Graph.CubicStar.ofAfterEdge object separatorIncidence (by native_decide)

/-- The generic cubic certificate recovers the exact four-vertex claw, with
all three center incidences owned by its labelled switch boundary. -/
example : Graph.CubicStar.Data.support object cubicStar = {1, 2, 3, 4} := by
  ext vertex
  fin_cases vertex <;>
    simp [Graph.CubicStar.Data.support, Graph.CubicStar.Data.boundary,
      cubicStar, Graph.CubicStar.ofAfterEdge, separatorIncidence]

example : (Graph.CubicStar.Data.fullNeighborFinset object 2) = {1, 3, 4} := by
  rw [Graph.CubicStar.Data.neighborFinset_eq_boundary object cubicStar]
  ext vertex
  fin_cases vertex <;>
    simp [Graph.CubicStar.Data.boundary, cubicStar,
      Graph.CubicStar.ofAfterEdge, separatorIncidence]

example : (Graph.CubicStar.Data.support object cubicStar).card = 4 :=
  Graph.CubicStar.Data.support_card object cubicStar

example : Graph.CubicStar.Data.constructionChecks = 0 := rfl

example : Graph.CubicStar.Data.ambientNeighborChecks object =
    input.vertices.card :=
  Graph.CubicStar.Data.ambientNeighborChecks_eq_order object

end StructuralExhaustion.Examples.OrderedBFSTreeBranch

namespace StructuralExhaustion.Examples.OrderedBFSTreeEvenCycle

open StructuralExhaustion

/-! Non-Erdős transfer: minimum-depth target selection on `C₆`. -/

abbrev Vertex := Fin 6

def graph : SimpleGraph Vertex := SimpleGraph.cycleGraph 6

def input : Graph.FiniteInput graph where
  vertices := inferInstance
  decideAdj := by
    unfold graph
    infer_instance

def object : Graph.FiniteObject Vertex := ⟨graph, input⟩

def profile : Graph.OrderedBFSTree.Profile object where
  root := 0

def preconnected : object.graph.Preconnected :=
  SimpleGraph.cycleGraph_preconnected

def target : Finset Vertex := {2, 4}

def selection : profile.TargetSelection preconnected target :=
  profile.selectTarget preconnected target (by simp [target])

/-- Both target vertices have depth two, so declared order selects `2`. -/
example : selection.vertex = 2 := by
  native_decide

example : selection.vertex ∈ target := selection.vertex_mem

example : selection.vertex ∈ target ∧
    ∀ index < (profile.treeWalk preconnected selection.vertex).length,
      (profile.treeWalk preconnected selection.vertex).getVert index ∉ target :=
  selection.treeWalk_first_lands

end StructuralExhaustion.Examples.OrderedBFSTreeEvenCycle
