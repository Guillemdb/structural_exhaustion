import Hypostructure.Graph.Minimality

/-!
# Proper-subgraph minimality fixture

The complete graph on two vertices is minimal in the baseline class with its
exact lexicographic size and avoids triangle cycles.  The generic graph
profile therefore rejects every proper subgraph as a member of that baseline.
-/

namespace Hypostructure.Fixtures.GraphMinimality

open Hypostructure.Graph

abbrev k2 : FiniteObject where
  Vertex := Fin 2
  graph := ⊤
  vertices := inferInstance
  decideAdj := inferInstance

def Baseline (object : FiniteObject) : Prop :=
  object.lexicographicSize = k2.lexicographicSize

def BranchState (_object : FiniteObject) := Unit

def TriangleLength (length : Nat) : Prop := length = 3

def Target (object : FiniteObject) : Prop :=
  HasCycleWithLength TriangleLength object

theorem k2_avoids : Not (Target k2) := by
  rintro ⟨certificate⟩
  have lengthLower := certificate.isCycle.three_le_length
  have lengthUpper : certificate.walk.length <= 2 := by
    have supportBound :=
      certificate.isCycle.nodup_dropLast_support.length_le_card
    simpa [SimpleGraph.Walk.length_support] using supportBound
  omega

def context : Core.MinimalCounterexampleContext
    (problem Baseline BranchState) Target
    (lexicographicProgress Baseline BranchState) where
  toAvoidingContext := {
    toBranchContext := {
      G := k2
      baseline := rfl
      state := ()
    }
    avoids := k2_avoids
  }
  minimal := by
    intro candidate smaller baseline
    have measureEq : candidate.lexicographicSize = k2.lexicographicSize :=
      baseline
    rw [lexicographicProgress_smaller_iff,
      FiniteObject.LexicographicallySmaller, measureEq] at smaller
    exact False.elim
      ((wellFounded_lt.prod_lex wellFounded_lt).irrefl.irrefl _ smaller)

def profile : ProperSubgraphMinimalityProfile Baseline BranchState Target where
  targetMonotone := cycleProperSubgraphTargetMonotone TriangleLength
  stateOf := fun _object => ()

def certificate : NoProperBaselineCertificate context :=
  deriveNoProperBaseline profile context

def edge : k2.graph.edgeSet :=
  ⟨s((0 : Fin 2), (1 : Fin 2)), by decide⟩

def deleted : ProperSubgraph k2 :=
  ProperSubgraph.deleteEdge k2 edge

theorem deleted_not_baseline : Not (Baseline deleted.value) :=
  certificate.excludes deleted

theorem deleted_closure_mechanism (baseline : Baseline deleted.value) :
    (certificate.closure deleted baseline).mechanism =
      Core.Closure.Mechanism.strictProgress :=
  rfl

#print axioms deleted_not_baseline
#print axioms deleted_closure_mechanism

end Hypostructure.Fixtures.GraphMinimality
