import MantelExample.Concrete
import StructuralExhaustion.Graph.FiniteSupportResponse
import StructuralExhaustion.Graph.PositiveDeficiencyWedge
import StructuralExhaustion.Graph.ClosedRankDrop
import StructuralExhaustion.Graph.OneThreeRepair

namespace MantelExample.CT15EdgeResponses

open StructuralExhaustion

/-!
# CT15 transfer: the two labelled ends of `K₂`

This textbook Mantel fixture instantiates the same exact finite-support
response and admissible-quotient CT15 profile used by the Erdős surplus-pair
stage.  The two coordinates are the two labelled one-vertex supports of the
unique edge of `K₂`; outside contexts are literal boundaried graphs and target
responses are literal triangle-cycle tests after gluing.
-/

abbrev Vertex := Fin 2

def graph : SimpleGraph Vertex := ⊤

def input : Graph.FiniteInput graph where
  vertices := inferInstance
  decideAdj := by
    change DecidableRel fun left right : Vertex ↦ left ≠ right
    infer_instance

def object : Graph.FiniteObject Vertex := ⟨graph, input⟩

def triangleInput : Graph.PackedMinimumDegreeCycle.StaticInput where
  minimumDegree := 1
  LengthOK := Graph.TriangleLength

theorem baseline : triangleInput.minimumDegree ≤ object.minDegree := by
  native_decide

theorem triangleFree : object.graph.CliqueFree 3 := by
  letI : FinEnum Vertex := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  rw [← SimpleGraph.cliqueFinset_eq_empty_iff]
  native_decide

theorem avoids :
    ¬Graph.HasCycleWithLength object.graph triangleInput.LengthOK :=
  Graph.not_hasCycleWithTriangleLength_of_cliqueFree triangleFree

/-- `K₂` is already lexicographically minimal among finite graphs of minimum
degree at least one. -/
noncomputable def minimalContext :
    Core.MinimalCounterexampleContext triangleInput.problem
      triangleInput.Target where
  toAvoidingContext := {
    toBranchContext := {
      G := Graph.PackedFiniteObject.pack object
      baseline := baseline
      state := ()
    }
    avoids := avoids
  }
  minimal := by
    intro packed smaller packedBaseline
    exfalso
    have positive : 0 < packed.object.minDegree :=
      lt_of_lt_of_le Nat.zero_lt_one packedBaseline
    letI : Nonempty packed.Vertex :=
      packed.object.nonempty_of_minDegree_pos positive
    let vertex : packed.Vertex := Classical.choice inferInstance
    have twoLeVertices : 2 ≤ packed.vertexCount := by
      have oneLeDegree : 1 ≤ packed.object.degree vertex :=
        packedBaseline.trans (packed.object.minDegree_le_degree vertex)
      have degreeLt := packed.object.degree_lt_vertexCount vertex
      simpa [Graph.PackedFiniteObject.vertexCount] using
        (Nat.succ_le_of_lt (oneLeDegree.trans_lt degreeLt))
    have oneLeEdges : 1 ≤ packed.edgeCount := by
      let dart := packed.object.dartOfMinDegreePos positive
      letI : FinEnum packed.Vertex := packed.object.input.vertices
      letI : DecidableRel packed.object.graph.Adj :=
        packed.object.input.decideAdj
      change 0 < packed.object.graph.edgeFinset.card
      apply Finset.card_pos.mpr
      exact ⟨dart.edge, SimpleGraph.mem_edgeFinset.mpr dart.edge_mem⟩
    have nineLe : 9 ≤ packed.lexRank := by
      change 9 ≤ packed.vertexCount ^ 3 + packed.edgeCount
      have eightLe : 8 ≤ packed.vertexCount ^ 3 := by
        exact Nat.pow_le_pow_left twoLeVertices 3
      omega
    have sourceRank :
        (Graph.PackedFiniteObject.pack object).lexRank = 9 := by
      native_decide
    change packed.lexRank <
      (Graph.PackedFiniteObject.pack object).lexRank at smaller
    rw [sourceRank] at smaller
    omega

@[implicit_reducible]
def coordinates : FinEnum Vertex := inferInstance

noncomputable def responseProfile :
    Graph.FiniteSupportResponse.Profile triangleInput minimalContext Vertex where
  coordinates := coordinates
  support := fun vertex ↦ by
    letI : DecidableEq Vertex := inferInstance
    exact {vertex}

noncomputable def ct15Profile := responseProfile.ct15Profile

theorem verified : CT15.AdmissibleQuotient.VerifiedFor ct15Profile :=
  ct15Profile.verifiedFor

theorem terminal : ct15Profile.run.terminal = .fullRankLedger :=
  verified.terminal

theorem trace : ct15Profile.run.trace =
    [.entry, .rankComputation, .rankSplit, .ledgerComputation,
      .ledgerComparison, .fullRankLedgerTerminal] :=
  verified.trace

theorem coordinate_count : coordinates.card = 2 := by
  native_decide

theorem closedProposal_exact
    (proposal : CT15.AdmissibleQuotient.Proposal responseProfile.responseSystem)
    (quotient : CT15.AdmissibleQuotient.Admissible minimalContext
      responseProfile.responseSystem proposal) :
    Function.Injective proposal.code :=
  quotient.injective

theorem closedProposal_total
    (proposal : CT15.AdmissibleQuotient.Proposal responseProfile.responseSystem)
    (quotient : CT15.AdmissibleQuotient.Admissible minimalContext
      responseProfile.responseSystem proposal) :
    Graph.ClosedRankDrop.ExactBarrier minimalContext
      responseProfile.responseSystem proposal :=
  Graph.ClosedRankDrop.exactBarrier quotient

theorem fourLeafBinaryRepair_identity :
    (2 : Int) = 4 - 2 + 2 * 0 - 0 := by
  apply Core.OneThreeRepair.identity 2 4 1 0 0
  · norm_num
  · norm_num

/-! A literal graph-level transfer of the repair identity.  The complete
graph `K₄` is connected, every vertex is internal of degree three, and its
cycle rank is three.  Thus the generic graph theorem computes
`4 = 0 - 2 + 2 * 3 - 0` from the graph itself. -/

namespace K4Repair

abbrev Vertex := Fin 4

def graph : SimpleGraph Vertex := ⊤

def input : Graph.FiniteInput graph where
  vertices := inferInstance
  decideAdj := by
    change DecidableRel fun left right : Vertex ↦ left ≠ right
    infer_instance

def object : Graph.FiniteObject Vertex := ⟨graph, input⟩

noncomputable def component : Graph.OneThreeRepair.Component Vertex where
  object := object
  boundary := ∅
  boundaryDegree := by simp
  internalDegreeThree := by
    intro vertex _internal
    fin_cases vertex <;> native_decide
  boundaryCard_le_edgeCount := by simp
  connected := by
    exact SimpleGraph.connected_top

theorem identity :
    (component.internal.card : Int) =
      component.boundary.card - 2 + 2 * component.cycleRank -
        component.surplus :=
  component.identity

theorem computed_identity : (4 : Int) = 0 - 2 + 2 * 3 - 0 := by
  norm_num

end K4Repair

/-! The same graph-generic deficiency/wedge kernel used by the Erdős
remainder stage is independently instantiated on the textbook edge `K₂`.
This transfer checks that the kernel depends only on a finite graph and a
declared support, not on packed paths or the Erdős target. -/

noncomputable def wholeSupportProfile :
    Graph.PositiveDeficiencyWedge.Profile object where
  core := object.vertexFinset

theorem wholeSupport_wedgeFloor :
    3 * wholeSupportProfile.core.card -
        2 * wholeSupportProfile.positiveDeficiency ≤
      wholeSupportProfile.wedgeCount :=
  wholeSupportProfile.wedgeFloor

theorem wholeSupport_wedgeCount_le_cube :
    wholeSupportProfile.wedgeCount ≤ object.input.vertices.card ^ 3 :=
  wholeSupportProfile.wedgeCount_le_cube

theorem wholeSupport_checks_quadratic :
    wholeSupportProfile.checks ≤ object.input.vertices.card ^ 2 :=
  wholeSupportProfile.checks_le_square

end MantelExample.CT15EdgeResponses
