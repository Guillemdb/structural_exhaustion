import Mathlib.Combinatorics.SimpleGraph.Circulant
import MantelExample.Run
import StructuralExhaustion.Core.ConditionalFibreProductCost

namespace MantelExample.ConditionalFibreProductCost

open StructuralExhaustion

/-!
# A graph-semantic conditional-fibre transfer

This transfer uses the textbook triangle-free graph `C₅`.  Its supplied
states are the actual vertices of the graph, its two coordinates are vertices
at distance two, and `accepts` is graph adjacency.  The successive fibres are
therefore the first neighbourhood and then the common neighbourhood, not a
stand-alone `Fin`/`Bool` fixture.

The exact local calculation is

`|V(C₅)| = 5`, `|N(0)| = 2`, `|N(0) ∩ N(2)| = 1`.

It instantiates the Core product theorem with safe factor two and flat factor
one, while the ordinary Mantel theorem independently verifies the extremal
bound for the same triangle-free graph.
-/

abbrev Vertex := Fin 5

def graph : SimpleGraph Vertex := SimpleGraph.cycleGraph 5

def input : Graph.FiniteInput graph where
  vertices := inferInstance
  decideAdj := by
    change DecidableRel (SimpleGraph.cycleGraph 5).Adj
    infer_instance

def object : Graph.FiniteObject Vertex := ⟨graph, input⟩

/-- The two distance-two vertices whose neighbourhoods are filtered in order. -/
def coordinates : Core.OrderedCollection Vertex where
  values := [0, 2]
  nodup := by decide
  decEq := inferInstance

/-- A state survives a coordinate precisely when it is adjacent to that
coordinate in the actual `C₅`. -/
def accepts (coordinate state : Vertex) : Bool :=
  @decide (object.graph.Adj coordinate state)
    (object.input.decideAdj coordinate state)

def profile : Core.ConditionalFibreProductCost.Profile where
  State := Vertex
  Coordinate := Vertex
  states := object.input.vertices.toOrderedCollection
  coordinates := coordinates
  accepts := accepts
  safe := 2
  flat := 1
  skeletonCount := object.input.vertices.card

def ledger :
    Core.ConditionalFibreProductCost.Profile.Ledger profile
      profile.states.values profile.coordinates.values := by
  refine .cons (by native_decide) ?_
  refine .cons (by native_decide) ?_
  exact .nil _

def certificate :
    Core.ConditionalFibreProductCost.Profile.Certificate profile where
  ledger := ledger
  startCapacity := by native_decide
  finalNonempty := by native_decide

/-- The example really lies in the hypothesis class of Mantel's theorem. -/
theorem triangleFree : object.graph.CliqueFree 3 := by
  letI : FinEnum Vertex := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  rw [← SimpleGraph.cliqueFinset_eq_empty_iff]
  native_decide

/-- The standard Mantel conclusion for the same graph used by the fibre scan. -/
theorem mantel_bound : Target object := mantel object triangleFree

/-- The first fibre is literally the neighbourhood of vertex `0`. -/
theorem mem_first_fibre_iff (state : Vertex) :
    state ∈ profile.prefixStates 1 ↔ object.graph.Adj 0 state := by
  letI : DecidableEq profile.State := profile.states.decEq
  letI : DecidableRel object.graph.Adj := fun left right =>
    object.input.decideAdj left right
  fin_cases state <;> decide

/-- The terminal fibre is literally the common neighbourhood of `0` and `2`. -/
theorem mem_final_fibre_iff (state : Vertex) :
    state ∈ profile.prefixStates 2 ↔
      object.graph.Adj 0 state ∧ object.graph.Adj 2 state := by
  letI : DecidableEq profile.State := profile.states.decEq
  letI : DecidableRel object.graph.Adj := fun left right =>
    object.input.decideAdj left right
  fin_cases state <;> decide

theorem prefix_counts_exact :
    profile.prefixCount 0 = 5 ∧
      profile.prefixCount 1 = 2 ∧
      profile.prefixCount 2 = 1 := by
  native_decide

theorem common_neighborhood_exact :
    certificate.ledger.finalStates.length = 1 := by
  native_decide

/-- Core's local conditional-fibre theorem applied to actual graph
neighbourhoods in the textbook triangle-free `C₅`. -/
theorem product_cost :
    profile.safe ^ profile.coordinates.values.length ≤
      profile.flat ^ profile.coordinates.values.length *
        profile.skeletonCount :=
  certificate.power_le_flat_mul_skeleton profile

theorem product_cost_exact : 2 ^ 2 ≤ 1 ^ 2 * object.input.vertices.card := by
  simpa [profile, coordinates] using product_cost

theorem checker_work_exact : profile.checks = 7 := by
  native_decide

theorem checker_work_local :
    profile.checks ≤
      profile.states.values.length * profile.coordinates.values.length :=
  profile.checks_le_state_mul_coordinate

end MantelExample.ConditionalFibreProductCost
