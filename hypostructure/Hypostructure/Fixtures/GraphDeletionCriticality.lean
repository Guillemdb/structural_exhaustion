import Hypostructure.Graph.DeletionCriticality

/-!
# Graph deletion-criticality fixture

The complete graph on two vertices is a minimal graph of minimum degree one.
The fixture derives its no-proper-baseline certificate, registers it after the
context in one accumulated ledger, and invokes the focused Graph executor
through typed queries.  Its unique edge then has a tight endpoint at the
generic threshold `1`.
-/

namespace Hypostructure.Fixtures.GraphDeletionCriticality

open Hypostructure.Graph
open Hypostructure.Core.Residual

abbrev k2 : FiniteObject where
  Vertex := Fin 2
  graph := ⊤
  vertices := inferInstance
  decideAdj := inferInstance

def Baseline : FiniteObject → Prop :=
  MinimumDegreeAtLeast 1

def BranchState (_object : FiniteObject) := Unit

def Target (_object : FiniteObject) : Prop := False

@[simp]
theorem k2_vertexCount : k2.vertexCount = 2 := by
  decide

@[simp]
theorem k2_edgeCount : k2.edgeCount = 1 := by
  decide

theorem k2_baseline : Baseline k2 := by
  change 1 ≤ (⊤ : SimpleGraph (Fin 2)).minDegree
  rw [SimpleGraph.minDegree_top]
  decide

theorem k2_avoids : Not (Target k2) := by
  simp [Target]

def context : Core.MinimalCounterexampleContext
    (problem Baseline BranchState) Target
    (lexicographicProgress Baseline BranchState) where
  toAvoidingContext := {
    toBranchContext := {
      G := k2
      baseline := k2_baseline
      state := ()
    }
    avoids := k2_avoids
  }
  minimal := by
    intro candidate smaller baseline
    exfalso
    rw [lexicographicProgress_smaller_iff,
      FiniteObject.lexicographicallySmaller_iff] at smaller
    have candidateNonempty : Nonempty candidate.Vertex := by
      cases isEmpty_or_nonempty candidate.Vertex with
      | inl empty =>
          letI : IsEmpty candidate.Vertex := empty
          have zero : candidate.minDegree = 0 := by
            letI : FinEnum candidate.Vertex := candidate.vertices
            letI : DecidableRel candidate.graph.Adj := candidate.decideAdj
            unfold FiniteObject.minDegree
            exact SimpleGraph.minDegree_of_isEmpty candidate.graph
          exact False.elim (by
            change 1 ≤ candidate.minDegree at baseline
            omega)
      | inr nonempty => exact nonempty
    letI : FinEnum candidate.Vertex := candidate.vertices
    letI : DecidableRel candidate.graph.Adj := candidate.decideAdj
    letI : Nonempty candidate.Vertex := candidateNonempty
    have minDegreeLt : candidate.minDegree < candidate.vertexCount := by
      change candidate.graph.minDegree < candidate.vertices.card
      simpa [FinEnum.card_eq_fintypeCard] using
        candidate.graph.minDegree_lt_card
    have twoLeVertices : 2 ≤ candidate.vertexCount := by
      change 1 ≤ candidate.minDegree at baseline
      omega
    rcases smaller with vertexLt | ⟨_vertexEq, edgeLt⟩
    · rw [k2_vertexCount] at vertexLt
      omega
    · obtain ⟨vertex⟩ := candidateNonempty
      have degreePos : 0 < candidate.degree vertex := by
        have degreeLower := candidate.minDegree_le_degree vertex
        change 1 ≤ candidate.minDegree at baseline
        omega
      have graphDegreePos : 0 < candidate.graph.degree vertex := by
        exact degreePos
      obtain ⟨neighbor, adjacent⟩ :=
        (candidate.graph.degree_pos_iff_exists_adj vertex).mp graphDegreePos
      have edgeMember : s(vertex, neighbor) ∈ candidate.graph.edgeFinset :=
        SimpleGraph.mem_edgeFinset.mpr adjacent
      have edgeCountPos : 0 < candidate.edgeCount := by
        unfold FiniteObject.edgeCount
        exact Finset.card_pos.mpr ⟨_, edgeMember⟩
      rw [k2_edgeCount] at edgeLt
      omega

def minimalityProfile :
    ProperSubgraphMinimalityProfile Baseline BranchState Target where
  targetMonotone := {
    map := by
      intro _source _subgraph target
      exact target
  }
  stateOf := fun _object => ()

def noProper : NoProperBaselineCertificate context :=
  deriveNoProperBaseline minimalityProfile context

/-- The root residual owns the selected context. -/
structure Input where
  context : Core.MinimalCounterexampleContext
    (problem Baseline BranchState) Target
    (lexicographicProgress Baseline BranchState)

def input : Input := ⟨context⟩

abbrev Root := Ledger Input

def root : Root := Ledger.initial input

def rootInputQuery : Query Root (fun _root => Input) :=
  Query.residual

def rootContextQuery : Query Root (fun _root =>
    Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)) :=
  rootInputQuery.map fun _root value => value.context

/-- The inherited no-proper-baseline fact is the next entry of the same
accumulated ledger, with its type indexed by the context already registered. -/
abbrev Previous := Ledger.Extension Root (fun root =>
  NoProperBaselineCertificate (rootContextQuery.read root))

def previous : Previous :=
  Ledger.extend root noProper

/-- The fixture keeps its only branch active; production callers may use any
decision-generated focus with the same executor. -/
def focus : Focus.Profile Previous where
  Active := fun _previous => True
  activeDecidable := fun _previous => .isTrue trivial

def contextLedgerQuery : Query Previous (fun _previous =>
    Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)) :=
  rootContextQuery.preserve

def noProperLedgerQuery : Query Previous (fun previous =>
    NoProperBaselineCertificate (contextLedgerQuery.read previous)) :=
  Query.latest

def contextQuery : Focus.ActiveQuery focus (fun _previous _active =>
    Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)) :=
  Focus.ActiveQuery.ofQuery contextLedgerQuery

def noProperQuery : Focus.ActiveQuery focus (fun previous active =>
    NoProperBaselineCertificate (contextQuery.read previous active)) :=
  Focus.ActiveQuery.ofQuery noProperLedgerQuery

def stage : FocusedMinimumDegreeDeletionCriticalityStage 1 focus contextQuery :=
  executeFocusedMinimumDegreeDeletionCriticality 1 focus contextQuery
    noProperQuery previous

abbrev stageFocus :=
  FocusedMinimumDegreeDeletionCriticalityProfile 1 focus contextQuery

def certificateQuery :=
  focusedMinimumDegreeDeletionCriticalityQuery 1 focus contextQuery

def active : stageFocus.Active stage :=
  trivial

def dart : k2.graph.Dart :=
  ⟨((0 : Fin 2), (1 : Fin 2)), by decide⟩

theorem executor_preserves_previous : stage.previous = previous :=
  rfl

theorem generated_tight_endpoint :
    k2.degree dart.fst = 1 ∨ k2.degree dart.snd = 1 := by
  exact (certificateQuery.read stage active).tightEndpoint dart

theorem generated_slack_independence {left right : k2.Vertex}
    (leftSlack : 2 ≤ k2.degree left)
    (rightSlack : 2 ≤ k2.degree right) :
    Not (k2.graph.Adj left right) := by
  exact (certificateQuery.read stage active).slackVerticesIndependent
    leftSlack rightSlack

def contextAtStageQuery :
    Focus.ActiveQuery stageFocus (fun _stage _active =>
      Core.MinimalCounterexampleContext
        (problem Baseline BranchState) Target
        (lexicographicProgress Baseline BranchState)) :=
  contextQuery.preserve

def independenceStage :=
  executeFocusedMinimumDegreeSlackVertexIndependence 1 stageFocus
    contextAtStageQuery certificateQuery stage

abbrev independenceFocus :=
  FocusedSlackVertexIndependenceProfile stageFocus
    (minimumDegreeDeletionCriticalityProfile 1) contextAtStageQuery

def independenceQuery :=
  focusedMinimumDegreeSlackVertexIndependenceQuery 1 stageFocus
    contextAtStageQuery

def independenceActive : independenceFocus.Active independenceStage :=
  trivial

theorem independence_executor_preserves_previous :
    independenceStage.previous = stage :=
  rfl

theorem registered_slack_independence {left right : k2.Vertex}
    (leftSlack : 2 ≤ k2.degree left)
    (rightSlack : 2 ≤ k2.degree right) :
    Not (k2.graph.Adj left right) := by
  exact independenceQuery.read independenceStage independenceActive
    leftSlack rightSlack

#print axioms FiniteObject.deleteEdge_preserves_minDegree
#print axioms deriveDeletionCriticality
#print axioms executeFocusedDeletionCriticality
#print axioms executeFocusedMinimumDegreeDeletionCriticality
#print axioms executeFocusedMinimumDegreeSlackVertexIndependence
#print axioms generated_tight_endpoint
#print axioms generated_slack_independence
#print axioms registered_slack_independence

end Hypostructure.Fixtures.GraphDeletionCriticality
