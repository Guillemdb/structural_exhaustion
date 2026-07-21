import Hypostructure.Core.Closure
import Hypostructure.Core.Residual.Focus
import Hypostructure.Graph.Progress
import Hypostructure.Graph.Target

/-!
# Proper-subgraph minimality

This module packages the reusable graph form of strict-progress closure.  A
domain registers target monotonicity from certified proper subgraphs to their
source.  Graph then derives, rather than receives, the certificate that a
minimal target-avoiding object has no proper subgraph satisfying the baseline.
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

/-- Complete reusable profile for excluding baseline-preserving proper
subgraphs of one minimal target-avoiding graph. -/
structure ProperSubgraphMinimalityProfile
    (Baseline : FiniteObject.{u} -> Prop)
    (BranchState : FiniteObject.{u} -> Type v)
    (Target : FiniteObject.{u} -> Prop) where
  targetMonotone : ProperSubgraphTargetMonotone Target
  stateOf : (object : FiniteObject.{u}) -> BranchState object

/-- Framework-owned no-proper-baseline result.  Every pointwise exclusion is
tagged by Core's strict-progress mechanism. -/
structure NoProperBaselineCertificate
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)) where
  private mk ::
  closure : forall (subgraph : ProperSubgraph ctx.G),
    Baseline subgraph.value -> Core.Closure.Result False
  mechanism : forall (subgraph : ProperSubgraph ctx.G)
    (baseline : Baseline subgraph.value),
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
    NoProperBaselineCertificate ctx where
  closure := by
    intro subgraph baseline
    let candidate : Core.AvoidingContext
        (problem Baseline BranchState) Target :=
      Core.AvoidingContext.ofBranch
        ({
          G := subgraph.value
          baseline := baseline
          state := profile.stateOf subgraph.value
        } : Core.BranchContext (problem Baseline BranchState))
        (fun target => ctx.avoids (profile.targetMonotone.map subgraph target))
    exact Core.Closure.Result.strictProgress {
      candidate := candidate
      smaller := subgraph.smaller Baseline BranchState
    }
  mechanism := by
    intro subgraph baseline
    rfl

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

/-- Execute generic proper-subgraph minimality only on the active branch. -/
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
  Core.Residual.Focus.run focus previous fun active =>
    deriveNoProperBaseline profile (context.read previous active)

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
        FocusedNoProperBaselineOutput focus context stage.previous active) :=
  Core.Residual.Focus.ActiveQuery.latest

end Hypostructure.Graph
