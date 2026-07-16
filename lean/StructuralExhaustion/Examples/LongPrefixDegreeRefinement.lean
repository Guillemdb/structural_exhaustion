import StructuralExhaustion.Graph.LongPrefixDegreeRefinement

namespace StructuralExhaustion.Examples.LongPrefixDegreeRefinement

open StructuralExhaustion

universe u

/-! Theorem-independent transfer of the exact-degree refinement. -/

variable {V : Type u} {object : Graph.FiniteObject V}
variable {input : Graph.LongPrefixObservedLabel.Input object}

noncomputable def source :
    Graph.LongPrefixDegreeRefinement.Source (input := input) :=
  ⟨Graph.LongPrefixObservedLabel.run input⟩

noncomputable def result := Graph.LongPrefixDegreeRefinement.run
  (source (input := input))

example :
    (∃ residual, result (input := input) = .exactDegree residual) ∨
      (∃ residual, result (input := input) = .congruentDegreeGap residual) :=
  Graph.LongPrefixDegreeRefinement.run_exhaustive _

example (equal : (source (input := input)).firstDegree =
    (source (input := input)).secondDegree) :
    ∃ residual, result (input := input) = .exactDegree residual :=
  Graph.LongPrefixDegreeRefinement.run_eq_exactDegree _ equal

example (different : (source (input := input)).firstDegree ≠
    (source (input := input)).secondDegree) :
    ∃ residual, result (input := input) = .congruentDegreeGap residual :=
  Graph.LongPrefixDegreeRefinement.run_eq_congruentDegreeGap _ different

example : (source (input := input)).first ≠ (source (input := input)).second :=
  Graph.LongPrefixDegreeRefinement.source_occurrences_distinct _

example : Graph.LongPrefixDegreeRefinement.visibleChecks (object := object) ≤
    2 * (object.input.vertices.card + 1) :=
  Graph.LongPrefixDegreeRefinement.visibleChecks_le

end StructuralExhaustion.Examples.LongPrefixDegreeRefinement

namespace StructuralExhaustion.Examples.LongPrefixDegreeRefinementK9

open StructuralExhaustion

/-! Concrete non-Erdős transfer on the textbook complete graph `K₉`. -/

abbrev Vertex := Fin 9

def graph : SimpleGraph Vertex := ⊤

def finiteInput : Graph.FiniteInput graph where
  vertices := inferInstance
  decideAdj := by
    change DecidableRel fun left right : Vertex => left ≠ right
    infer_instance

def object : Graph.FiniteObject Vertex := ⟨graph, finiteInput⟩

def observedInput : Graph.LongPrefixObservedLabel.Input object where
  support := (inferInstance : FinEnum Vertex).orderedValues
  marked := Finset.univ
  firstNine := by simp

noncomputable def source :
    Graph.LongPrefixDegreeRefinement.Source (input := observedInput) :=
  ⟨Graph.LongPrefixObservedLabel.run observedInput⟩

noncomputable def result :=
  Graph.LongPrefixDegreeRefinement.run source

/-- Every `K₉` vertex has degree eight, so the actual observed collision
executes the exact-degree branch. -/
example : ∃ residual, result = .exactDegree residual := by
  apply Graph.LongPrefixDegreeRefinement.run_eq_exactDegree
  have allDegree (vertex : Vertex) : object.degree vertex = 8 := by
    rw [object.degree_eq_ncard_neighborSet]
    change (graph.neighborSet vertex).ncard = 8
    rw [show graph.neighborSet vertex = ({vertex} : Set Vertex)ᶜ by
      ext other
      simp [graph]]
    rw [Set.ncard_compl]
    simp
  unfold Graph.LongPrefixDegreeRefinement.Source.firstDegree
    Graph.LongPrefixDegreeRefinement.Source.secondDegree
  rw [allDegree, allDegree]

example : source.first ≠ source.second :=
  Graph.LongPrefixDegreeRefinement.source_occurrences_distinct source

example : Graph.LongPrefixDegreeRefinement.visibleChecks (object := object) ≤
    2 * (object.input.vertices.card + 1) :=
  Graph.LongPrefixDegreeRefinement.visibleChecks_le

end StructuralExhaustion.Examples.LongPrefixDegreeRefinementK9
