import Hypostructure.Core.Minimality
import Hypostructure.Graph.Progress
import Hypostructure.Graph.Target

/-!
# Proper-subgraph minimality

This module re-exports the graph minimality API as a thin specialization of the
generic core minimality executor. Domain-specific objects (`ProperSubgraph`,
cycle target transport, and focused stage wrappers) are retained here; all core
logic and routing stays in `Hypostructure.Core.Minimality`.
-/

namespace Hypostructure.Graph

universe u v uPrevious

namespace ProperSubgraph

/-- The injective graph homomorphism carried by a proper-subgraph certificate. -/
def hom {source : FiniteObject.{u}} (subgraph : ProperSubgraph source) :
    subgraph.value.graph →g source.graph where
  toFun := subgraph.vertexEmbedding
  map_rel' := by
    intro left right adjacent
    exact subgraph.included ((SimpleGraph.map_adj_apply).2 adjacent)

theorem hom_injective {source : FiniteObject.{u}}
    (subgraph : ProperSubgraph source) :
    Function.Injective subgraph.hom :=
  subgraph.vertexEmbedding.injective

end ProperSubgraph

/-- Target transport required by the proper-subgraph minimality pattern. -/
structure ProperSubgraphTargetMonotone
    (Target : FiniteObject.{u} -> Prop) : Prop where
  map : forall {source : FiniteObject.{u}}
    (subgraph : ProperSubgraph source), Target subgraph.value -> Target source

/-- Accepted cycles map injectively from every certified proper subgraph. -/
def cycleProperSubgraphTargetMonotone (LengthOK : Nat -> Prop) :
    ProperSubgraphTargetMonotone (HasCycleWithLength LengthOK) where
  map := by
    intro source subgraph target
    rcases target with ⟨certificate⟩
    exact ⟨certificate.mapHom subgraph.hom subgraph.hom_injective⟩

/-- Graph-level profile for applying strict-progress minimality to proper
subgraphs. -/
structure ProperSubgraphMinimalityProfile
    (Baseline : FiniteObject.{u} -> Prop)
    (BranchState : FiniteObject.{u} -> Type v)
    (Target : FiniteObject.{u} -> Prop) where
  targetMonotone : ProperSubgraphTargetMonotone Target
  stateOf : (object : FiniteObject.{u}) -> BranchState object

private def toCoreProfile
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (profile : ProperSubgraphMinimalityProfile Baseline BranchState Target) :
    Core.Minimality.SubobjectMinimalityProfile
      (P := problem Baseline BranchState)
      Target
      (lexicographicProgress Baseline BranchState)
      ProperSubgraph :=
  { toAmbient := fun subgraph => subgraph.value
    smaller := fun subgraph =>
      subgraph.smaller Baseline BranchState
    targetMonotone := fun subgraph target =>
      profile.targetMonotone.map subgraph target
    stateOf := profile.stateOf
  }

/-- Framework-owned no-proper-baseline result. Every subgraph exclusion is
tagged by Core's strict-progress mechanism. -/
structure NoProperBaselineCertificate
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)) :=
  private mk ::
  closure : ∀ (subgraph : ProperSubgraph ctx.G), Baseline subgraph.value ->
    Core.Closure.Result False
  mechanism : ∀ (subgraph : ProperSubgraph ctx.G) (baseline : Baseline subgraph.value),
    (closure subgraph baseline).mechanism =
      Core.Closure.Mechanism.strictProgress

namespace NoProperBaselineCertificate

/-- No certified proper subgraph can retain the baseline. -/
theorem excludes
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)}
    (certificate : NoProperBaselineCertificate ctx)
    (subgraph : ProperSubgraph ctx.G) : Not (Baseline subgraph.value) := by
  intro baseline
  exact (certificate.closure subgraph baseline).proof

end NoProperBaselineCertificate

/-- Execute the generic proper-subgraph strict-progress closure. -/
def deriveNoProperBaseline
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (profile : ProperSubgraphMinimalityProfile Baseline BranchState Target)
    (ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)) :
    NoProperBaselineCertificate ctx :=
  let certificate :
      Core.Minimality.NoSubobjectBaselineCertificate
        (P := problem Baseline BranchState)
        (Target := Target)
        (progress := lexicographicProgress Baseline BranchState)
        (Subobject := ProperSubgraph)
        (profile := toCoreProfile profile) ctx :=
    Core.Minimality.deriveNoSubobjectBaseline
      (P := problem Baseline BranchState)
      (Target := Target)
      (progress := lexicographicProgress Baseline BranchState)
      (Subobject := ProperSubgraph)
      (profile := toCoreProfile profile) ctx
  { closure := certificate.closure
    mechanism := certificate.mechanism }

/-- Cycle-target specialization used by minimum-degree counterexamples. -/
def cycleProperSubgraphMinimalityProfile
    (Baseline : FiniteObject.{u} -> Prop)
    (BranchState : FiniteObject.{u} -> Type v)
    (LengthOK : Nat -> Prop)
    (stateOf : (object : FiniteObject.{u}) -> BranchState object) :
    ProperSubgraphMinimalityProfile Baseline BranchState
      (HasCycleWithLength LengthOK) where
  targetMonotone := cycleProperSubgraphTargetMonotone LengthOK
  stateOf := stateOf

/-! ## Focused accumulated execution -/

/-- The graph-owned payload produced on one active minimal-context branch. -/
abbrev FocusedNoProperBaselineOutput
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject -> Prop}
    {BranchState : FiniteObject -> Type v}
    {Target : FiniteObject -> Prop}
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext
        (problem Baseline BranchState) Target
        (lexicographicProgress Baseline BranchState))
    (previous : Previous) (active : focus.Active previous) :=
  NoProperBaselineCertificate (context.read previous active)

/-- Exact accumulated stage after focused proper-subgraph closure. -/
abbrev FocusedNoProperBaselineStage
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject -> Prop}
    {BranchState : FiniteObject -> Type v}
    {Target : FiniteObject -> Prop}
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext
        (problem Baseline BranchState) Target
        (lexicographicProgress Baseline BranchState)) :=
  Core.Residual.Focus.Stage focus
    (FocusedNoProperBaselineOutput focus context)

/-- Counted execution of generic proper-subgraph minimality on the active
branch. The derived certificate is proof-only, so the exact work is the
framework-owned focus selection. -/
def executeFocusedNoProperBaselineCounted
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject -> Prop}
    {BranchState : FiniteObject -> Type v}
    {Target : FiniteObject -> Prop}
    (profile : ProperSubgraphMinimalityProfile Baseline BranchState Target)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext
        (problem Baseline BranchState) Target
        (lexicographicProgress Baseline BranchState))
    (previous : Previous) :
  Core.Counted (FocusedNoProperBaselineStage focus context) :=
  Core.Residual.Focus.runCounted focus
    (Output := FocusedNoProperBaselineOutput focus context)
    previous
    (fun active _checks _exact =>
      deriveNoProperBaseline profile (context.read previous active))

/-- Public stage projection of counted proper-subgraph minimality. -/
def executeFocusedNoProperBaseline
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject -> Prop}
    {BranchState : FiniteObject -> Type v}
    {Target : FiniteObject -> Prop}
    (profile : ProperSubgraphMinimalityProfile Baseline BranchState Target)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext
        (problem Baseline BranchState) Target
        (lexicographicProgress Baseline BranchState))
    (previous : Previous) :
    FocusedNoProperBaselineStage focus context :=
  (executeFocusedNoProperBaselineCounted focus profile context previous).value

@[simp] theorem executeFocusedNoProperBaselineCounted_checks
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject -> Prop}
    {BranchState : FiniteObject -> Type v}
    {Target : FiniteObject -> Prop}
    (profile : ProperSubgraphMinimalityProfile Baseline BranchState Target)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext
        (problem Baseline BranchState) Target
        (lexicographicProgress Baseline BranchState))
    (previous : Previous) :
    (executeFocusedNoProperBaselineCounted focus profile context previous).checks =
      focus.selectionBudget.checks previous := by
  simpa [executeFocusedNoProperBaselineCounted]
    using
      (Core.Residual.Focus.runCounted_checks focus
        (Output := FocusedNoProperBaselineOutput focus context)
        previous
        (fun active _checks _exact =>
          deriveNoProperBaseline profile (context.read previous active)))

theorem executeFocusedNoProperBaselineCounted_checks_bounded
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject -> Prop}
    {BranchState : FiniteObject -> Type v}
    {Target : FiniteObject -> Prop}
    (profile : ProperSubgraphMinimalityProfile Baseline BranchState Target)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext
        (problem Baseline BranchState) Target
        (lexicographicProgress Baseline BranchState))
    (previous : Previous) :
    (executeFocusedNoProperBaselineCounted focus profile context previous).checks <=
      focus.selectionBudget.coefficient *
        (focus.selectionBudget.size previous + 1) ^
          focus.selectionBudget.degree := by
  rw [executeFocusedNoProperBaselineCounted_checks]
  exact focus.selectionBudget.bounded previous

/-- Predicate-form work theorem for focused proper-subgraph minimality. -/
theorem executeFocusedNoProperBaselineCounted_work_within
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject -> Prop}
    {BranchState : FiniteObject -> Type v}
    {Target : FiniteObject -> Prop}
    (profile : ProperSubgraphMinimalityProfile Baseline BranchState Target)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext
        (problem Baseline BranchState) Target
        (lexicographicProgress Baseline BranchState))
    (previous : Previous) :
    focus.selectionBudget.Within previous
      (executeFocusedNoProperBaselineCounted focus profile context previous).checks :=
  by
    rw [executeFocusedNoProperBaselineCounted_checks focus profile context previous]
    exact focus.selectionBudget.bounded previous

/-- Focus inherited after the Graph minimality executor. -/
abbrev FocusedNoProperBaselineProfile
    {Previous : Type uPrevious}
  (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject -> Prop}
    {BranchState : FiniteObject -> Type v}
    {Target : FiniteObject -> Prop}
  (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext
        (problem Baseline BranchState) Target
        (lexicographicProgress Baseline BranchState)) :=
  Core.Residual.Focus.successor focus
    (FocusedNoProperBaselineOutput focus context)

/-- Query the exact graph-owned no-proper-baseline certificate. -/
def focusedNoProperBaselineQuery
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject -> Prop}
    {BranchState : FiniteObject -> Type v}
    {Target : FiniteObject -> Prop}
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext
        (problem Baseline BranchState) Target
        (lexicographicProgress Baseline BranchState)) :
  Core.Residual.Focus.ActiveQuery
      (FocusedNoProperBaselineProfile focus context)
      (fun stage active =>
        FocusedNoProperBaselineOutput focus context
          stage.previous active) :=
  Core.Residual.Focus.ActiveQuery.latest

end Hypostructure.Graph
