import Mathlib.Combinatorics.SimpleGraph.Metric
import StructuralExhaustion.Graph.FiniteObject

namespace StructuralExhaustion.Graph.FiniteConnector

open StructuralExhaustion

universe u

/-!
# Proof-carrying shortest connectors

The producer selects endpoints by a finite minimum-distance scan and retains
one shortest path certificate.  Consumers inspect only the supplied path and
its two finite endpoint supports; they never enumerate paths or connected
subgraphs.
-/

variable {V : Type u}

/-- A shortest connector between two nonempty finite vertex supports. -/
structure Certificate (object : FiniteObject V)
    (left right : Finset V) where
  start : V
  finish : V
  start_mem : start ∈ left
  finish_mem : finish ∈ right
  path : object.graph.Walk start finish
  isPath : path.IsPath
  shortest : path.length = object.graph.dist start finish
  supportMinimum : ∀ leftVertex ∈ left, ∀ rightVertex ∈ right,
    path.length ≤ object.graph.dist leftVertex rightVertex

/-- A certificate exists from finite endpoint minimization and one Mathlib
shortest-path witness whenever the ambient graph is preconnected. -/
theorem exists_certificate (object : FiniteObject V)
    (preconnected : object.graph.Preconnected)
    {left right : Finset V} (leftNonempty : left.Nonempty)
    (rightNonempty : right.Nonempty) :
    Nonempty (Certificate object left right) := by
  let endpointPairs : Finset (V × V) := left ×ˢ right
  have endpointPairsNonempty : endpointPairs.Nonempty := by
    exact leftNonempty.product rightNonempty
  obtain ⟨endpoints, endpointsMem, minimum⟩ :=
    endpointPairs.exists_min_image
      (fun endpoints ↦ object.graph.dist endpoints.1 endpoints.2)
      endpointPairsNonempty
  have startMem : endpoints.1 ∈ left := (Finset.mem_product.mp endpointsMem).1
  have finishMem : endpoints.2 ∈ right := (Finset.mem_product.mp endpointsMem).2
  obtain ⟨path, isPath, shortest⟩ :=
    (preconnected endpoints.1 endpoints.2).exists_path_of_dist
  exact ⟨{
    start := endpoints.1
    finish := endpoints.2
    start_mem := startMem
    finish_mem := finishMem
    path := path
    isPath := isPath
    shortest := shortest
    supportMinimum := by
      intro leftVertex leftMem rightVertex rightMem
      rw [shortest]
      exact minimum (leftVertex, rightVertex)
        (Finset.mem_product.mpr ⟨leftMem, rightMem⟩)
  }⟩

/-- Proof-selected canonical connector.  All later computation is over this
single retained certificate. -/
noncomputable def canonical (object : FiniteObject V)
    (preconnected : object.graph.Preconnected)
    {left right : Finset V} (leftNonempty : left.Nonempty)
    (rightNonempty : right.Nonempty) :
    Certificate object left right :=
  Classical.choice
    (exists_certificate object preconnected leftNonempty rightNonempty)

namespace Certificate

variable {object : FiniteObject V} {left right : Finset V}

/-- Exact finite connected carrier retained for the pair response. -/
noncomputable def support (connector : Certificate object left right) :
    Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact left ∪ connector.path.support.toFinset ∪ right

theorem left_subset_support (connector : Certificate object left right) :
    left ⊆ connector.support := by
  intro vertex member
  simp [support, member]

theorem right_subset_support (connector : Certificate object left right) :
    right ⊆ connector.support := by
  intro vertex member
  simp [support, member]

theorem path_subset_support (connector : Certificate object left right) :
    ∀ vertex ∈ connector.path.support, vertex ∈ connector.support := by
  intro vertex member
  simp [support, member]

/-- Checking the retained connector scans only its two supports and path. -/
def checks (connector : Certificate object left right) : Nat :=
  left.card + connector.path.support.length + right.card + 1

theorem checks_linear (connector : Certificate object left right) :
    connector.checks ≤
      left.card + connector.path.support.length + right.card + 1 :=
  le_rfl

end Certificate

end StructuralExhaustion.Graph.FiniteConnector
