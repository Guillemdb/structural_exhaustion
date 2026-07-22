import Hypostructure.Core.Context
import Hypostructure.Core.Residual.Focus
import Hypostructure.Graph.Deletion
import Hypostructure.Graph.Isomorphism
import Hypostructure.Graph.Problem

/-!
# Finite-graph progress and minimal selection

The graph layer registers the manuscript order on packed finite graphs as the
genuine lexicographic order on vertex and edge counts.  Core remains
responsible for well-founded minimal selection and for every contradiction
with a smaller baseline object.

Primitive graph operations below prove only structural decrease.  They do not
claim that an application baseline is preserved by a deletion or restriction.
-/

namespace Hypostructure.Graph

universe u v w

/-- The representation-independent size used for generic graph minimality. -/
abbrev LexicographicSize := Nat × Nat

namespace FiniteObject

/-- Vertex count followed by edge count. -/
def lexicographicSize (object : FiniteObject) : LexicographicSize :=
  (object.vertexCount, object.edgeCount)

/-- Strict lexicographic graph-size reduction. -/
def LexicographicallySmaller (smaller larger : FiniteObject) : Prop :=
  Prod.Lex (· < ·) (· < ·)
    smaller.lexicographicSize larger.lexicographicSize

theorem lexicographicallySmaller_iff {smaller larger : FiniteObject} :
    smaller.LexicographicallySmaller larger ↔
      smaller.vertexCount < larger.vertexCount ∨
        (smaller.vertexCount = larger.vertexCount ∧
          smaller.edgeCount < larger.edgeCount) := by
  simp only [LexicographicallySmaller, lexicographicSize, Prod.lex_iff]

/-- Fewer vertices always give strict graph progress. -/
theorem lexicographicallySmaller_of_vertexCount_lt
    {smaller larger : FiniteObject}
    (countLt : smaller.vertexCount < larger.vertexCount) :
    smaller.LexicographicallySmaller larger :=
  Prod.Lex.left _ _ countLt

/-- At fixed vertex count, fewer edges give strict graph progress. -/
theorem lexicographicallySmaller_of_vertexCount_eq_edgeCount_lt
    {smaller larger : FiniteObject}
    (countEq : smaller.vertexCount = larger.vertexCount)
    (edgeLt : smaller.edgeCount < larger.edgeCount) :
    smaller.LexicographicallySmaller larger := by
  exact FiniteObject.lexicographicallySmaller_iff.mpr
    (Or.inr ⟨countEq, edgeLt⟩)

/-- Isomorphic packed graphs have exactly the same progress measure, even
when their hidden vertex types and execution schedules differ. -/
theorem lexicographicSize_eq_of_isomorphic {left right : FiniteObject}
    (equivalent : left.Isomorphic right) :
    left.lexicographicSize = right.lexicographicSize := by
  apply Prod.ext
  · exact left.vertexCount_eq_of_isomorphic equivalent
  · exact left.edgeCount_eq_of_isomorphic equivalent

/-- Replacing the left graph by an isomorphic representation does not change
whether a strict reduction holds. -/
theorem lexicographicallySmaller_congr_left
    {left right larger : FiniteObject}
    (equivalent : left.Isomorphic right) :
    left.LexicographicallySmaller larger ↔
      right.LexicographicallySmaller larger := by
  rw [LexicographicallySmaller, LexicographicallySmaller,
    left.lexicographicSize_eq_of_isomorphic equivalent]

/-- Replacing the right graph by an isomorphic representation does not change
whether a strict reduction holds. -/
theorem lexicographicallySmaller_congr_right
    {smaller left right : FiniteObject}
    (equivalent : left.Isomorphic right) :
    smaller.LexicographicallySmaller left ↔
      smaller.LexicographicallySmaller right := by
  rw [LexicographicallySmaller, LexicographicallySmaller,
    left.lexicographicSize_eq_of_isomorphic equivalent]

/-- Isomorphic representations cannot be strictly smaller than one another. -/
theorem not_lexicographicallySmaller_of_isomorphic
    {left right : FiniteObject} (equivalent : left.Isomorphic right) :
    Not (left.LexicographicallySmaller right) := by
  intro decrease
  have measureEq := left.lexicographicSize_eq_of_isomorphic equivalent
  rw [LexicographicallySmaller, measureEq] at decrease
  exact (wellFounded_lt.prod_lex wellFounded_lt).irrefl.irrefl _ decrease

end FiniteObject

/-- Generic well-founded progress for packed finite graphs, ordered first by
vertex count and then by edge count. -/
def lexicographicProgress
    (Baseline : FiniteObject.{u} -> Prop)
    (BranchState : FiniteObject.{u} -> Type v) :
    Core.Progress (problem Baseline BranchState) where
  Measure := LexicographicSize
  lt := Prod.Lex (· < ·) (· < ·)
  wellFounded := wellFounded_lt.prod_lex wellFounded_lt
  measure := FiniteObject.lexicographicSize

@[simp]
theorem lexicographicProgress_measure
    (Baseline : FiniteObject.{u} -> Prop)
    (BranchState : FiniteObject.{u} -> Type v)
    (object : FiniteObject.{u}) :
    (lexicographicProgress Baseline BranchState).measure object =
      object.lexicographicSize :=
  rfl

theorem lexicographicProgress_smaller_iff
    (Baseline : FiniteObject.{u} -> Prop)
    (BranchState : FiniteObject.{u} -> Type v)
    {smaller larger : FiniteObject.{u}} :
    (lexicographicProgress Baseline BranchState).Smaller smaller larger ↔
      smaller.LexicographicallySmaller larger :=
  Iff.rfl

/-- Read the current graph from a focused minimal-counterexample context.  The
context remains predecessor-owned; this query only projects the graph needed
by downstream graph CTs. -/
def focusedMinimalContextObjectQuery
    {Previous : Type w}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState))) :
    Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active => FiniteObject.{u}) :=
  context.map fun _previous _active ctx => ctx.G

/-- A graph-local certificate that `value` embeds as a subgraph of `source`
and strictly decreases the registered lexicographic measure. -/
structure ProperSubgraph (source : FiniteObject.{u}) where
  value : FiniteObject.{u}
  vertexEmbedding : value.Vertex ↪ source.Vertex
  included : value.graph.map vertexEmbedding <= source.graph
  decreases : value.LexicographicallySmaller source

namespace ProperSubgraph

/-- Construct a proper-subgraph certificate from the mathematical embedding,
inclusion, and the two possible lexicographic count witnesses. -/
def ofStrictCounts (source value : FiniteObject.{u})
    (vertexEmbedding : value.Vertex ↪ source.Vertex)
    (included : value.graph.map vertexEmbedding <= source.graph)
    (strict : value.vertexCount < source.vertexCount ∨
      (value.vertexCount = source.vertexCount ∧
        value.edgeCount < source.edgeCount)) :
    ProperSubgraph source where
  value := value
  vertexEmbedding := vertexEmbedding
  included := included
  decreases := FiniteObject.lexicographicallySmaller_iff.mpr strict

/-- An induced graph on a strictly smaller explicit support is a proper
subgraph. -/
def ofInducedSupport (source : FiniteObject.{u})
    (support : Finset source.Vertex)
    (supportStrict : support.card < source.vertexCount) :
    ProperSubgraph source where
  value := source.induce support
  vertexEmbedding := (source.induceEmbedding support).toEmbedding
  included := source.induce_le support
  decreases :=
    FiniteObject.lexicographicallySmaller_of_vertexCount_lt (by
      simpa only [FiniteObject.vertexCount_induce] using supportStrict)

/-- Edge deletion is a proper spanning subgraph. -/
def deleteEdge (source : FiniteObject.{u}) (edge : source.graph.edgeSet) :
    ProperSubgraph source where
  value := source.deleteEdge edge
  vertexEmbedding := ⟨id, Function.injective_id⟩
  included := by
    rintro _ _ ⟨_different, left, right, adjacent, rfl, rfl⟩
    exact source.deleteEdge_le edge adjacent
  decreases :=
    FiniteObject.lexicographicallySmaller_of_vertexCount_eq_edgeCount_lt
      (source.vertexCount_deleteEdge edge) (source.edgeCount_deleteEdge_lt edge)

/-- Vertex deletion is a proper induced subgraph. -/
def deleteVertex (source : FiniteObject.{u}) (vertex : source.Vertex) :
    ProperSubgraph source where
  value := source.deleteVertex vertex
  vertexEmbedding := (source.deleteVertexEmbedding vertex).toEmbedding
  included := source.deleteVertex_le vertex
  decreases :=
    FiniteObject.lexicographicallySmaller_of_vertexCount_lt (by
      have exactDrop := source.vertexCount_deleteVertex_add_one vertex
      omega)

/-- Every certified proper subgraph decreases the registered graph progress. -/
theorem smaller
    {source : FiniteObject.{u}} (subgraph : ProperSubgraph source)
    (Baseline : FiniteObject.{u} -> Prop)
    (BranchState : FiniteObject.{u} -> Type v) :
    (lexicographicProgress Baseline BranchState).Smaller
      subgraph.value source :=
  subgraph.decreases

/-- Core minimality proves the target on every baseline-preserving certified
proper subgraph. -/
theorem target_of_minimality
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState))
    (subgraph : ProperSubgraph ctx.G)
    (baseline : Baseline subgraph.value) :
    Target subgraph.value :=
  ctx.target_of_smaller
    (subgraph.smaller Baseline BranchState) baseline

/-- A baseline-preserving proper subgraph that also avoids the target
contradicts Core minimality. -/
theorem contradiction_of_minimality
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState))
    (subgraph : ProperSubgraph ctx.G)
    (baseline : Baseline subgraph.value)
    (avoids : Not (Target subgraph.value)) : False :=
  avoids (subgraph.target_of_minimality ctx baseline)

end ProperSubgraph

/-- Framework-owned selection of a lexicographically minimal graph from one
known target-avoiding baseline graph.  The caller supplies theorem semantics
and initializes branch state; it never chooses or repackages the successor. -/
noncomputable def selectLexicographicMinimal
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (object : FiniteObject.{u})
    (baseline : Baseline object)
    (avoids : Not (Target object))
    (stateOf : (current : FiniteObject.{u}) -> BranchState current) :
    Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState) := by
  let initial : Core.AvoidingContext
      (problem Baseline BranchState) Target :=
    Core.AvoidingContext.ofBranch
      ({ G := object, baseline := baseline, state := stateOf object } :
        Core.BranchContext (problem Baseline BranchState))
      avoids
  exact Classical.choice
    (initial.exists_minimalCounterexample
      (lexicographicProgress Baseline BranchState) stateOf)

/-- Payload generated by Graph's focused lexicographic minimal-selection
executor. -/
abbrev FocusedLexicographicMinimalOutput
    {Previous : Type w}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (_object : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active => FiniteObject.{u}))
    (_baseline : Core.Residual.Focus.ActiveQuery focus
      (fun previous active => Baseline (_object.read previous active)))
    (_avoids : Core.Residual.Focus.ActiveQuery focus
      (fun previous active => Not (Target (_object.read previous active))))
    (_stage : Previous) (_active : focus.Active _stage) :=
  Core.MinimalCounterexampleContext
    (problem Baseline BranchState) Target
    (lexicographicProgress Baseline BranchState)

/-- Exact focused residual after Graph selects a lexicographically minimal
counterexample. -/
abbrev FocusedLexicographicMinimalStage
    {Previous : Type w}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (object : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active => FiniteObject.{u}))
    (baseline : Core.Residual.Focus.ActiveQuery focus
      (fun previous active => Baseline (object.read previous active)))
    (avoids : Core.Residual.Focus.ActiveQuery focus
      (fun previous active => Not (Target (object.read previous active)))) :=
  Core.Residual.Focus.Stage focus
    (FocusedLexicographicMinimalOutput (BranchState := BranchState)
      focus object baseline avoids)

/-- Focus inherited after Graph selects a lexicographically minimal
counterexample. -/
abbrev FocusedLexicographicMinimalProfile
    {Previous : Type w}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (object : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active => FiniteObject.{u}))
    (baseline : Core.Residual.Focus.ActiveQuery focus
      (fun previous active => Baseline (object.read previous active)))
    (avoids : Core.Residual.Focus.ActiveQuery focus
      (fun previous active => Not (Target (object.read previous active)))) :=
  Core.Residual.Focus.successor focus
    (FocusedLexicographicMinimalOutput (BranchState := BranchState)
      focus object baseline avoids)

/-- Query the selected minimal graph context from the newest focused ledger
entry. -/
def focusedLexicographicMinimalContextQuery
    {Previous : Type w}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (object : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active => FiniteObject.{u}))
    (baseline : Core.Residual.Focus.ActiveQuery focus
      (fun previous active => Baseline (object.read previous active)))
    (avoids : Core.Residual.Focus.ActiveQuery focus
      (fun previous active => Not (Target (object.read previous active)))) :
    Core.Residual.Focus.ActiveQuery
      (FocusedLexicographicMinimalProfile (BranchState := BranchState)
        focus object baseline avoids)
      (fun stage active =>
        FocusedLexicographicMinimalOutput (BranchState := BranchState)
          focus object baseline avoids stage.previous active) :=
  Core.Residual.Focus.ActiveQuery.latest

/-- Counted focused execution of Graph's lexicographic minimal-counterexample
selector. -/
noncomputable def executeFocusedLexicographicMinimalCounted
    {Previous : Type w}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (object : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active => FiniteObject.{u}))
    (baseline : Core.Residual.Focus.ActiveQuery focus
      (fun previous active => Baseline (object.read previous active)))
    (avoids : Core.Residual.Focus.ActiveQuery focus
      (fun previous active => Not (Target (object.read previous active))))
    (stateOf : (current : FiniteObject.{u}) -> BranchState current)
    (previous : Previous) :
    Core.Counted
      (FocusedLexicographicMinimalStage (BranchState := BranchState)
        focus object baseline avoids) :=
  Core.Residual.Focus.runCounted focus
    (Output := FocusedLexicographicMinimalOutput
      (BranchState := BranchState) focus object baseline avoids) previous
    fun active _checks _exact =>
      selectLexicographicMinimal (object.read previous active)
        (baseline.read previous active) (avoids.read previous active)
        stateOf

/-- Public stage projection of Graph's lexicographic minimal-counterexample
selector. -/
noncomputable def executeFocusedLexicographicMinimal
    {Previous : Type w}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (object : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active => FiniteObject.{u}))
    (baseline : Core.Residual.Focus.ActiveQuery focus
      (fun previous active => Baseline (object.read previous active)))
    (avoids : Core.Residual.Focus.ActiveQuery focus
      (fun previous active => Not (Target (object.read previous active))))
    (stateOf : (current : FiniteObject.{u}) -> BranchState current)
    (previous : Previous) :
    FocusedLexicographicMinimalStage (BranchState := BranchState)
      focus object baseline avoids :=
  (executeFocusedLexicographicMinimalCounted focus object baseline avoids
    stateOf previous).value

@[simp] theorem executeFocusedLexicographicMinimalCounted_checks
    {Previous : Type w}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (object : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active => FiniteObject.{u}))
    (baseline : Core.Residual.Focus.ActiveQuery focus
      (fun previous active => Baseline (object.read previous active)))
    (avoids : Core.Residual.Focus.ActiveQuery focus
      (fun previous active => Not (Target (object.read previous active))))
    (stateOf : (current : FiniteObject.{u}) -> BranchState current)
    (previous : Previous) :
    (executeFocusedLexicographicMinimalCounted focus object baseline avoids
      stateOf previous).checks = focus.selectionBudget.checks previous := by
  rw [executeFocusedLexicographicMinimalCounted,
    Core.Residual.Focus.runCounted_checks]

/-- Predicate-form work theorem for Graph's focused minimal selector. -/
theorem executeFocusedLexicographicMinimalCounted_work_within
    {Previous : Type w}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (object : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active => FiniteObject.{u}))
    (baseline : Core.Residual.Focus.ActiveQuery focus
      (fun previous active => Baseline (object.read previous active)))
    (avoids : Core.Residual.Focus.ActiveQuery focus
      (fun previous active => Not (Target (object.read previous active))))
    (stateOf : (current : FiniteObject.{u}) -> BranchState current)
    (previous : Previous) :
    focus.selectionBudget.Within previous
      (executeFocusedLexicographicMinimalCounted focus object baseline avoids
        stateOf previous).checks :=
  Core.Residual.Focus.runCounted_work_within focus previous _

/-- A raw smaller graph carrying the same baseline and target avoidance is
closed by the selected Core minimality kernel.  The caller does not construct
or copy an `AvoidingContext`. -/
theorem contradiction_of_smallerAvoidingGraph
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState))
    (candidate : FiniteObject.{u})
    (baseline : Baseline candidate)
    (state : BranchState candidate)
    (avoids : Not (Target candidate))
    (smaller : (lexicographicProgress Baseline BranchState).Smaller
      candidate ctx.G) : False :=
  ctx.contradiction_of_smaller
    (Core.AvoidingContext.ofBranch
      ({ G := candidate, baseline := baseline, state := state } :
        Core.BranchContext (problem Baseline BranchState))
      avoids)
    smaller

end Hypostructure.Graph
