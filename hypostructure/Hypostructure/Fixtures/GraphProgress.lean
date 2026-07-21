import Hypostructure.Graph.Progress

/-!
# Finite-graph progress fixtures

These fixtures exercise graph-owned decrease certificates and Core-owned
minimal-counterexample selection on tiny explicit graphs.
-/

namespace Hypostructure.Fixtures.GraphProgress

open Graph

/-! ## Primitive graph decreases -/

/-- The complete graph on two vertices. -/
abbrev k2 : FiniteObject where
  Vertex := Fin 2
  graph := ⊤
  vertices := inferInstance
  decideAdj := inferInstance

/-- One certified edge of `k2`. -/
def k2Edge : k2.graph.edgeSet :=
  ⟨s((0 : Fin 2), (1 : Fin 2)), by
    change (⊤ : SimpleGraph (Fin 2)).Adj 0 1
    decide⟩

def firstVertex : Finset k2.Vertex := {0}

theorem firstVertex_strict : firstVertex.card < k2.vertexCount := by
  decide

theorem induced_support_decreases :
    (k2.induce firstVertex).LexicographicallySmaller k2 :=
  (Graph.ProperSubgraph.ofInducedSupport
    k2 firstVertex firstVertex_strict).decreases

theorem edge_deletion_decreases :
    (k2.deleteEdge k2Edge).LexicographicallySmaller k2 :=
  (Graph.ProperSubgraph.deleteEdge k2 k2Edge).decreases

theorem vertex_deletion_decreases :
    (k2.deleteVertex (0 : Fin 2)).LexicographicallySmaller k2 :=
  (Graph.ProperSubgraph.deleteVertex k2 0).decreases

/-! ## Framework-owned minimal selection -/

/-- Every finite graph is admitted in this tiny baseline class. -/
def Baseline (_object : FiniteObject) : Prop := True

/-- A dependent branch-state family used to test the public initializer. -/
def BranchState (object : FiniteObject) : Type :=
  Fin (object.vertexCount + 1)

/-- The target consists exactly of zero-vertex graphs. -/
def Target (object : FiniteObject) : Prop :=
  object.vertexCount = 0

def stateOf (object : FiniteObject) : BranchState object :=
  ⟨0, by omega⟩

/-- A one-vertex target-avoiding baseline graph. -/
abbrev oneVertex : FiniteObject where
  Vertex := Fin 1
  graph := ⊥
  vertices := inferInstance
  decideAdj := inferInstance

theorem oneVertex_count : oneVertex.vertexCount = 1 := by
  rfl

theorem oneVertex_avoids : Not (Target oneVertex) := by
  intro target
  change oneVertex.vertexCount = 0 at target
  rw [oneVertex_count] at target
  omega

/-- Graph owns the selected successor; the fixture supplies only the external
problem predicates, initial evidence, and branch-state initializer. -/
noncomputable def selected :
    Core.MinimalCounterexampleContext
      (Graph.problem Baseline BranchState) Target
      (Graph.lexicographicProgress Baseline BranchState) :=
  Graph.selectLexicographicMinimal oneVertex trivial oneVertex_avoids stateOf

theorem selected_vertexCount_pos : 0 < selected.G.vertexCount := by
  have nonzero : selected.G.vertexCount ≠ 0 := by
    simpa only [Target] using selected.avoids
  exact Nat.pos_of_ne_zero nonzero

/-- The unique graph on no vertices. -/
abbrev emptyGraph : FiniteObject where
  Vertex := Fin 0
  graph := ⊥
  vertices := inferInstance
  decideAdj := inferInstance

theorem emptyGraph_count : emptyGraph.vertexCount = 0 := by
  rfl

theorem emptyGraph_smaller :
    (Graph.lexicographicProgress Baseline BranchState).Smaller
      emptyGraph selected.G := by
  rw [Graph.lexicographicProgress_smaller_iff]
  apply FiniteObject.lexicographicallySmaller_of_vertexCount_lt
  simpa only [emptyGraph_count] using selected_vertexCount_pos

/-- `target_of_smaller` is supplied by Core; Graph contributes only the
lexicographic decrease. -/
theorem emptyGraph_target_of_smaller : Target emptyGraph :=
  selected.target_of_smaller emptyGraph_smaller trivial

/-- The original one-vertex avoiding graph cannot lie strictly below the
framework-selected minimal graph.  Graph constructs no selected output or
application-owned context in this argument. -/
theorem oneVertex_not_smaller_selected :
    Not ((Graph.lexicographicProgress Baseline BranchState).Smaller
      oneVertex selected.G) := by
  intro smaller
  exact Graph.contradiction_of_smallerAvoidingGraph selected oneVertex
    trivial (stateOf oneVertex) oneVertex_avoids smaller

/-! ## Isomorphism invariance of the measure -/

def swapK2 : k2.Iso k2 := by
  change (⊤ : SimpleGraph (Fin 2)) ≃g (⊤ : SimpleGraph (Fin 2))
  exact SimpleGraph.Iso.completeGraph (Equiv.swap 0 1)

theorem relabelled_k2_not_smaller :
    Not (k2.LexicographicallySmaller k2) :=
  FiniteObject.not_lexicographicallySmaller_of_isomorphic ⟨swapK2⟩

#print axioms induced_support_decreases
#print axioms edge_deletion_decreases
#print axioms vertex_deletion_decreases
#print axioms emptyGraph_target_of_smaller
#print axioms oneVertex_not_smaller_selected
#print axioms relabelled_k2_not_smaller

end Hypostructure.Fixtures.GraphProgress
