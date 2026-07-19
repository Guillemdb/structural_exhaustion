import StructuralExhaustion.Core.CTTransition
import StructuralExhaustion.Core.Provision

namespace StructuralExhaustion.Routes.Accumulated

universe uSource uContext uTrigger uResult uLedger uIndex uSeed

open Core.Routing

/-!
# Canonical accumulated-ledger CT transition

Some manuscript edges consume a distinguished semantic residual and therefore
use a narrower transition profile.  The remaining sequential CT edges retain
the complete proof prefix and select the next public CT context and trigger
from that prefix.  This module is the single framework implementation of that
general case.

The application supplies only the two mathematical projections in `Adapter`.
The source and target CTs determine the profile identity.  `advance` is the
only executor and its result is already the complete target-labelled ledger.
-/

/-- Stable source residual kind shared by ordinary accumulated-ledger
transitions out of one CT. -/
def sourceResidualKindId (sourceTactic : Core.CTId) : String :=
  sourceTactic.key ++ ".residual.accumulatedLedger"

/-- Stable profile identity determined entirely by the typed CT pair. -/
def transitionId (sourceTactic targetTactic : Core.CTId) : String :=
  sourceResidualKindId sourceTactic ++ "->" ++ targetTactic.key

/-- The only problem-specific input of an ordinary accumulated-ledger
transition: select the next public context and its dependent trigger from the
current mathematical output. -/
structure Adapter
    (Source : Sort uSource)
    (target : ExecutableInterface.{uContext, uTrigger, uResult} targetTactic) where
  targetContext : Source → target.Context
  trigger : (source : Source) → target.Trigger (targetContext source)

/-- The unique typed transition generated from an accumulated-ledger adapter. -/
def transition
    {sourceTactic targetTactic : Core.CTId}
    {Source : Sort uSource}
    (target : ExecutableInterface.{uContext, uTrigger, uResult} targetTactic)
    (adapter : Adapter Source target) :
    CTTransition sourceTactic targetTactic Source target :=
  CTTransition.ofTotalResidual
    (transitionId sourceTactic targetTactic)
    adapter.targetContext adapter.trigger

/-- Canonical accumulated output-ledger type when the target reads a genuine
mathematical projection of the full incoming ledger. -/
abbrev ProjectedOutputLedger
    {sourceTactic targetTactic : Core.CTId}
    {Source : Sort uSource}
    (target : ExecutableInterface.{uContext, uTrigger, uResult} targetTactic)
    (adapter : Adapter Source target)
    {Ledger : Sort uLedger}
    (current : Ledger → Source)
    (source : ResidualStage sourceTactic Ledger) :=
  (transition target adapter).OutputLedger current source

/-- Canonical output-ledger type for the common case where the accumulated
ledger itself is the current mathematical source.  Applications never spell
the identity projection. -/
abbrev OutputLedger
    {sourceTactic targetTactic : Core.CTId}
    (target : ExecutableInterface.{uContext, uTrigger, uResult} targetTactic)
    {Ledger : Sort uLedger}
    (adapter : Adapter Ledger target)
    (source : ResidualStage sourceTactic Ledger) :=
  ProjectedOutputLedger target adapter id source

/-- Execute the next CT while retaining the literal complete incoming ledger.
No application-owned predecessor handoff or bare-result chaining is exposed. -/
def advance
    {sourceTactic targetTactic : Core.CTId}
    {Source : Sort uSource}
    (target : ExecutableInterface.{uContext, uTrigger, uResult} targetTactic)
    (adapter : Adapter Source target)
    {Ledger : Sort uLedger}
    (current : Ledger → Source)
    (source : ResidualStage sourceTactic Ledger) :
    ResidualStage targetTactic
      (ProjectedOutputLedger target adapter current source) :=
  (transition target adapter).runEnabledLedgerOnLedger current source () rfl

/-- The common full-ledger case where the current mathematical source is the
accumulated ledger itself. -/
def advanceCurrent
    {sourceTactic targetTactic : Core.CTId}
    (target : ExecutableInterface.{uContext, uTrigger, uResult} targetTactic)
    {Ledger : Sort uLedger}
    (adapter : Adapter Ledger target)
    (source : ResidualStage sourceTactic Ledger) :
    ResidualStage targetTactic (OutputLedger target adapter source) :=
  advance target adapter id source

/-! ## Pointwise selected and ordinary accumulated transitions -/

/-- Execute a pointwise family of already selected specialized transitions
without exposing the Core executor in an application.  The family is the
problem's mathematical choice of local registered routes; execution and exact
predecessor retention remain framework-owned. -/
def advanceSelectedPointwise
    {sourceTactic targetTactic : Core.CTId}
    {Ledger : Sort uLedger}
    (family : PointwiseTransitionFamily sourceTactic targetTactic Ledger)
    (source : ResidualStage sourceTactic Ledger) :
    ResidualStage targetTactic (family.EnabledStage source) :=
  family.advance source

/-- Canonical output-ledger type for a pointwise family of selected
specialized transitions. -/
abbrev SelectedPointwiseOutputLedger
    {sourceTactic targetTactic : Core.CTId}
    {Ledger : Sort uLedger}
    (family : PointwiseTransitionFamily sourceTactic targetTactic Ledger)
    (source : ResidualStage sourceTactic Ledger) :=
  family.OutputLedger source

/-- The mathematical data for a pointwise family of ordinary accumulated
transitions.  Each index may select its own local source type, target
capability, context, and trigger; the complete outer ledger is shared and is
never traversed. -/
structure PointwiseAdapter
    (sourceTactic targetTactic : Core.CTId)
    (Index : Type uIndex) (Ledger : Sort uLedger) where
  Source : Index → Sort uSource
  target : (index : Index) →
    ExecutableInterface.{uContext, uTrigger, uResult} targetTactic
  adapter : (index : Index) → Adapter (Source index) (target index)
  current : (index : Index) → Ledger → Source index

/-- Generate the canonical pointwise transition family from ordinary total
residual adapters.  Unit discovery, typed transition construction, and exact
source retention are framework-owned. -/
def pointwiseFamily
    {sourceTactic targetTactic : Core.CTId}
    {Index : Type uIndex} {Ledger : Sort uLedger}
    (profile : PointwiseAdapter sourceTactic targetTactic Index Ledger) :
    PointwiseTransitionFamily sourceTactic targetTactic Ledger where
  Index := Index
  Source := profile.Source
  target := profile.target
  transition := fun index =>
    transition (profile.target index) (profile.adapter index)
  current := profile.current
  seed := fun _index _source => ()
  discovered := fun _index _source => rfl

/-- Execute an ordinary pointwise family as a dependent function while
retaining the common accumulated predecessor exactly once. -/
def advancePointwise
    {sourceTactic targetTactic : Core.CTId}
    {Index : Type uIndex} {Ledger : Sort uLedger}
    (profile : PointwiseAdapter sourceTactic targetTactic Index Ledger)
    (source : ResidualStage sourceTactic Ledger) :
    ResidualStage targetTactic
      ((pointwiseFamily profile).EnabledStage source) :=
  (pointwiseFamily profile).advance source

/-- Canonical shared output-ledger type for an ordinary pointwise CT edge. -/
abbrev PointwiseOutputLedger
    {sourceTactic targetTactic : Core.CTId}
    {Index : Type uIndex} {Ledger : Sort uLedger}
    (profile : PointwiseAdapter sourceTactic targetTactic Index Ledger)
    (source : ResidualStage sourceTactic Ledger) :=
  (pointwiseFamily profile).OutputLedger source

@[simp] theorem transition_profile_id
    {sourceTactic targetTactic : Core.CTId}
    {Source : Sort uSource}
    (target : ExecutableInterface.{uContext, uTrigger, uResult} targetTactic)
    (adapter : Adapter Source target) :
    (transition (sourceTactic := sourceTactic) target adapter).profileId =
      transitionId sourceTactic targetTactic :=
  rfl

/-- Canonical catalog contract for one ordinary typed CT pair.  Every pair
uses the same constructor and full-ledger executor; the target interface name
is recorded explicitly for declaration-level validation. -/
def transitionContract
    (sourceTactic targetTactic : Core.CTId)
    (targetExecutableInterface : String) : Core.CTTransitionProfileContract where
  profileId := transitionId sourceTactic targetTactic
  sourceTacticId := sourceTactic.key
  targetTacticId := targetTactic.key
  sourceResidualKind := sourceResidualKindId sourceTactic
  targetExecutableInterface := targetExecutableInterface
  transitionConstructor :=
    "StructuralExhaustion.Routes.Accumulated.transition"
  advanceExecutor := "StructuralExhaustion.Routes.Accumulated.advance"
  selectionClass := .forced
  semanticDiscovery := .problemSemanticAdapter
    "StructuralExhaustion.Routes.Accumulated.Adapter"
  problemSpecificInputs := [.targetCapability, .semanticDiscoveryAdapter]

end StructuralExhaustion.Routes.Accumulated
