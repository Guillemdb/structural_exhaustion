import StructuralExhaustion.Core.AutomationFirst
import StructuralExhaustion.Core.FiniteSequentialFiltration

namespace StructuralExhaustion.Routes.SequentialRatioFailureHandoff

open StructuralExhaustion
open StructuralExhaustion.Core.FiniteSequentialFiltration

universe uAmbient uBranch uState

/-!
# Exact sequential-ratio failure handoff

This route retains the strongest conclusion supplied by a failed finite
sequential filtration: the inherited branch context, the exact profile and
reference-run equation, the first failing barrier, and its before/after state
fibres.  It intentionally is not a CT6, CT7, or CT10 residual.

The arithmetic inequality in `FirstFailure.fails` does not construct CT6
failure semantics, a CT7 representative/context pair, or a CT10 datum,
classification, and promotion.  An application may build a later route only
after an independent graph reflection theorem constructs one of those exact
trigger payloads from the retained states.
-/

variable {P : Core.Problem.{uAmbient, uBranch}}

/-- Proof-carrying source emitted by the exact filtration reference run. -/
structure Source (ctx : Core.BranchContext P) (profile : Profile.{uState}) where
  failure : FirstFailure profile.states.orderedValues profile.barriers
  run_eq : profile.run = Outcome.firstFailure failure

/-- Consumer-side arithmetic residual.  Both dependent indices and the whole
source are retained, so neither context nor filtration can be replaced. -/
structure Residual (ctx : Core.BranchContext P) (profile : Profile.{uState}) where
  source : Source ctx profile

/-- Forced identity handoff on the first-ratio-failure branch. -/
def route {ctx : Core.BranchContext P} {profile : Profile.{uState}}
    (source : Source ctx profile) : Residual ctx profile :=
  ⟨source⟩

@[simp] theorem route_source {ctx : Core.BranchContext P}
    {profile : Profile.{uState}} (source : Source ctx profile) :
    (route source).source = source :=
  rfl

/-- Zero-based position of the exact first failing barrier. -/
def Residual.index {ctx : Core.BranchContext P} {profile : Profile.{uState}}
    (residual : Residual ctx profile) : Nat :=
  residual.source.failure.index

/-- Exact conditioning fibre immediately before the failed barrier. -/
def Residual.beforeStates {ctx : Core.BranchContext P}
    {profile : Profile.{uState}} (residual : Residual ctx profile) :
    List profile.State :=
  residual.source.failure.beforeStates

/-- Exact barrier selected by the canonical filtration run. -/
def Residual.barrier {ctx : Core.BranchContext P}
    {profile : Profile.{uState}} (residual : Residual ctx profile) :
    Barrier profile.State :=
  residual.source.failure.barrier

/-- Exact retained fibre immediately after the failed barrier. -/
def Residual.afterStates {ctx : Core.BranchContext P}
    {profile : Profile.{uState}} (residual : Residual ctx profile) :
    List profile.State :=
  residual.source.failure.afterStates

theorem routed_run_eq {ctx : Core.BranchContext P}
    {profile : Profile.{uState}} (source : Source ctx profile) :
    profile.run = Outcome.firstFailure (route source).source.failure :=
  source.run_eq

/-- The routed residual retains the literal strict cardinality inequality. -/
theorem routed_fails {ctx : Core.BranchContext P}
    {profile : Profile.{uState}} (source : Source ctx profile) :
    Fails (route source).beforeStates (route source).barrier :=
  source.failure.fails

/-- The after-fibre remains a literal sublist of the before-fibre. -/
theorem routed_after_sublist_before {ctx : Core.BranchContext P}
    {profile : Profile.{uState}} (source : Source ctx profile) :
    List.Sublist (route source).afterStates (route source).beforeStates :=
  source.failure.afterStates_sublist_beforeStates

/-- Stable provenance deliberately names an arithmetic handoff, not a CT. -/
def routeId : String :=
  "finite-sequential-ratio-failure->arithmetic-handoff"

end StructuralExhaustion.Routes.SequentialRatioFailureHandoff
