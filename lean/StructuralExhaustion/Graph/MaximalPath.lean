import StructuralExhaustion.Graph.Basic
import StructuralExhaustion.Graph.Path
import StructuralExhaustion.Core.FiniteSaturation

namespace StructuralExhaustion.Graph

open StructuralExhaustion

universe u

variable {V : Type u} {G : SimpleGraph V} {root : V}

/-!
# Deterministic endpoint-maximal paths

This is the graph instantiation of the framework's exact finite-saturation
machine.  Graph semantics and path simplicity are Mathlib-native; the declared
`FiniteInput.vertices` order determines which enabled extension is selected
first.
-/

/-- A rooted Mathlib path with no fresh neighbour at its active endpoint. -/
structure EndpointMaximalPath (G : SimpleGraph V) (root : V) where
  path : RootedPath G root
  endpoint_closed :
    ∀ vertex, G.Adj path.endpoint vertex → vertex ∈ path.vertices

namespace EndpointMaximalPath

theorem no_fresh_endpoint_neighbor
    (maximal : EndpointMaximalPath G root) :
    ∀ vertex, ¬(G.Adj maximal.path.endpoint vertex ∧
      vertex ∉ maximal.path.vertices) := by
  intro vertex extension
  exact extension.2 (maximal.endpoint_closed vertex extension.1)

end EndpointMaximalPath

/-- A vertex extends a rooted path exactly when it is a fresh neighbour of the
active endpoint.  The adjacency orientation matches `Walk.cons`. -/
def CanExtend (G : SimpleGraph V) (path : RootedPath G root)
    (vertex : V) : Prop :=
  G.Adj vertex path.endpoint ∧ vertex ∉ path.vertices

def canExtendDecidable (input : FiniteInput G)
    (path : RootedPath G root) (vertex : V) :
    Decidable (CanExtend G path vertex) := by
  letI : DecidableEq V := input.vertices.decEq
  letI : DecidableRel G.Adj := input.decideAdj
  unfold CanExtend
  infer_instance

namespace GreedyPath

/-- Exact first-enabled extension machine for one fixed path root. -/
def machine (input : FiniteInput G) (root : V) :
    Core.FiniteSaturation.Machine (RootedPath G root) V where
  frontier _ := input.vertices.toOrderedCollection
  Enabled path vertex := CanExtend G path vertex
  decideEnabled path vertex := canExtendDecidable input path vertex
  advance path vertex _ extension :=
    path.prepend vertex extension.1 extension.2
  measure path := input.vertices.orderedValues.length - path.vertices.length
  advance_decreases path vertex _ extension := by
    change input.vertices.orderedValues.length - (vertex :: path.vertices).length <
      input.vertices.orderedValues.length - path.vertices.length
    exact Core.FiniteSaturation.remainingSlots_cons_lt input.vertices
      (List.nodup_cons.mpr ⟨extension.2, path.vertices_nodup⟩)

/-- Run greedy extension to its certified saturated terminal state. -/
def grow (input : FiniteInput G) (path : RootedPath G root) :
    EndpointMaximalPath G root := by
  let execution := (machine input root).execute path
  let terminal := execution.terminal
  refine
    { path := terminal
      endpoint_closed := ?_ }
  intro vertex adjacent
  letI : DecidableEq V := input.vertices.decEq
  by_cases member : vertex ∈ terminal.vertices
  · exact member
  · have inFrontier :
        vertex ∈ ((machine input root).frontier terminal).values :=
      input.vertices.mem_orderedValues vertex
    have disabled : ¬CanExtend G terminal vertex := by
      simpa [terminal, machine] using
        execution.terminal_saturated vertex inFrontier
    exact (disabled ⟨adjacent.symm, member⟩).elim

end GreedyPath

/-- Deterministic endpoint-maximal path rooted at a specified vertex. -/
def endpointMaximalPathFrom (input : FiniteInput G) (start : V) :
    EndpointMaximalPath G start :=
  GreedyPath.grow input (RootedPath.singleton G start)

/-- Choose the first scheduled vertex and grow an endpoint-maximal path. -/
def endpointMaximalPath (input : FiniteInput G)
    (nonempty : input.vertices.orderedValues ≠ []) :
    EndpointMaximalPath G (input.vertices.orderedValues.head nonempty) :=
  endpointMaximalPathFrom input (input.vertices.orderedValues.head nonempty)

end StructuralExhaustion.Graph
