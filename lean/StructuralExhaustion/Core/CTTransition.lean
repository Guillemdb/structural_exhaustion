import StructuralExhaustion.Core.ExactHandoff
import StructuralExhaustion.Core.Routing

namespace StructuralExhaustion.Core

universe uSource uLedger uAdded uIndex uContext uTrigger uResult uSeed

/-!
# Executable CT transitions

This module owns residual-to-trigger discovery together with the two invariants
needed by a complete CT-to-CT handoff:

* the source and target CTs are fixed by types rather than untyped name strings;
* executing the target produces an `ExactStageHandoff`, so the literal source
  residual is retained automatically with the target result.

Problem packages supply only the semantic adapter used by a framework transition
constructor and the mathematical target capability.  They never construct a
target context, trigger, predecessor equality, transition outcome, or residual
handoff.
-/

/-- Type-level identifiers for the fixed structural-exhaustion tactic set. -/
inductive CTId where
  | ct1 | ct2 | ct3 | ct4 | ct5 | ct6 | ct7 | ct8 | ct9
  | ct10 | ct11 | ct12 | ct13 | ct14 | ct15 | ct16 | ct17
  deriving Repr, DecidableEq

namespace CTId

/-- Stable catalog spelling of a type-level CT identifier. -/
def key : CTId → String
  | .ct1 => "CT1"
  | .ct2 => "CT2"
  | .ct3 => "CT3"
  | .ct4 => "CT4"
  | .ct5 => "CT5"
  | .ct6 => "CT6"
  | .ct7 => "CT7"
  | .ct8 => "CT8"
  | .ct9 => "CT9"
  | .ct10 => "CT10"
  | .ct11 => "CT11"
  | .ct12 => "CT12"
  | .ct13 => "CT13"
  | .ct14 => "CT14"
  | .ct15 => "CT15"
  | .ct16 => "CT16"
  | .ct17 => "CT17"

end CTId

namespace Routing

/-- A CT-labelled residual together with kernel evidence that its stored value
is exactly the canonical output named by the preceding stage.  All automatic
transitions consume this carrier, never an unindexed application value. -/
structure ResidualStage (tactic : CTId) (Residual : Sort uSource) where
  expected : Residual
  handoff : ExactHandoff expected

/-- One dependent extension of an accumulated ledger.  `previous` is the
literal output of the incoming residual stage; `added` is the single new
application theorem or data value indexed by that complete prior ledger. -/
structure LedgerExtension (Previous : Sort uLedger)
    (Added : Previous → Sort uAdded) where
  previous : Previous
  added : Added previous

namespace ResidualStage

/-- Seed a CT stage with its literal canonical output. -/
def exact {tactic : CTId} {Residual : Sort uSource}
    (output : Residual) : ResidualStage tactic Residual where
  expected := output
  handoff := ExactHandoff.refl output

/-- The literal residual consumed by the next framework transition. -/
def output {tactic : CTId} {Residual : Sort uSource}
    (stage : ResidualStage tactic Residual) : Residual :=
  stage.handoff.previous

@[simp] theorem output_eq_expected {tactic : CTId}
    {Residual : Sort uSource} (stage : ResidualStage tactic Residual) :
    stage.output = stage.expected :=
  stage.handoff.previousExact

@[simp] theorem exact_output {tactic : CTId} {Residual : Sort uSource}
    (output : Residual) : (exact (tactic := tactic) output).output = output :=
  rfl

/-- Attach one dependent theorem or data value while retaining the literal
complete ledger produced by the incoming stage.  The CT label is unchanged;
only a later framework transition may change it. -/
def extend {tactic : CTId} {Ledger : Sort uLedger}
    {Added : Ledger → Sort uAdded}
    (stage : ResidualStage tactic Ledger) (added : Added stage.output) :
    ResidualStage tactic (LedgerExtension Ledger Added) :=
  exact ⟨stage.output, added⟩

@[simp] theorem extend_output_previous {tactic : CTId}
    {Ledger : Sort uLedger} {Added : Ledger → Sort uAdded}
    (stage : ResidualStage tactic Ledger) (added : Added stage.output) :
    (stage.extend added).output.previous = stage.output :=
  rfl

@[simp] theorem extend_output_added {tactic : CTId}
    {Ledger : Sort uLedger} {Added : Ledger → Sort uAdded}
    (stage : ResidualStage tactic Ledger) (added : Added stage.output) :
    (stage.extend added).output.added = added :=
  rfl

end ResidualStage

/-- The single executable entry interface of an instantiated CT.  Context,
trigger, result, and public reference execution are inseparable.  Specialized
profiles are values of this structure; they do not create a second transport
mechanism. -/
structure ExecutableInterface (tactic : CTId) where
  Context : Type uContext
  Trigger : Context → Type uTrigger
  Result : (context : Context) → Trigger context → Sort uResult
  execute : (context : Context) → (trigger : Trigger context) →
    Result context trigger

/-- A pointwise family of public CT entries with one already selected context
and trigger at every local index.  `Index` is not required to be finite or
enumerable: the combined execution below is a dependent function, not a
scan. -/
structure PointwiseExecutableFamily (tactic : CTId) where
  Index : Type uIndex
  entry : Index → ExecutableInterface.{uContext, uTrigger, uResult} tactic
  context : (index : Index) → (entry index).Context
  trigger : (index : Index) →
    (entry index).Trigger (context index)

namespace PointwiseExecutableFamily

/-- Package the pointwise obligations as one ordinary executable CT entry.
Its result is the dependent function of the actual public executions.  This
defines neither an index traversal nor an alternative transition mechanism. -/
def executableInterface {tactic : CTId}
    (family : PointwiseExecutableFamily.{uIndex, uContext, uTrigger, uResult}
      tactic) : ExecutableInterface tactic where
  Context := Unit
  Trigger := fun _context => Unit
  Result := fun _context _trigger => (index : family.Index) →
    (family.entry index).Result (family.context index) (family.trigger index)
  execute := fun _context _trigger index =>
    (family.entry index).execute (family.context index) (family.trigger index)

/-- Access at one local index is definitionally the corresponding entry's
public execution. -/
@[simp] theorem executableInterface_execute_apply {tactic : CTId}
    (family : PointwiseExecutableFamily.{uIndex, uContext, uTrigger, uResult}
      tactic) (index : family.Index) :
    family.executableInterface.execute () () index =
      (family.entry index).execute (family.context index)
        (family.trigger index) :=
  rfl

end PointwiseExecutableFamily

/-- Private semantic kernel used only inside an executable transition. -/
private structure TransitionKernel
    (sourceTactic : CTId)
    (Source : Sort uSource)
    (target : ExecutableInterface.{uContext, uTrigger, uResult} targetTactic) where
  profileId : String
  targetContext : ResidualStage sourceTactic Source → target.Context
  Seed : ResidualStage sourceTactic Source → Type uSeed
  discover : (source : ResidualStage sourceTactic Source) → Discovery (Seed source)
  trigger : (source : ResidualStage sourceTactic Source) →
    Seed source → target.Trigger (targetContext source)

/-- One framework-owned CT-to-CT family.  The private kernel supplies semantic
discovery; the executable target entry supplies the only permitted target
runner.  The type parameters prevent one CT pair from being silently
presented as another pair. -/
structure CTTransition
    (sourceTactic targetTactic : CTId)
    (Source : Sort uSource)
    (target : ExecutableInterface.{uContext, uTrigger, uResult} targetTactic) where
  private mk ::
  private kernel : TransitionKernel.{uSource, uContext, uTrigger, uResult, uSeed}
    sourceTactic Source target

namespace CTTransition

variable {sourceTactic targetTactic : CTId}
variable {Source : Sort uSource}
variable {target : ExecutableInterface.{uContext, uTrigger, uResult} targetTactic}

/-- Construct the unique public transition surface from its mathematical
adapter.  The semantic kernel is private: applications can neither generate a
detached trigger nor bypass target execution. -/
def ofAdapter
    (profileId : String)
    (targetContext : Source → target.Context)
    (Seed : Source → Type uSeed)
    (discover : (source : Source) → Discovery (Seed source))
    (buildTrigger : (source : Source) →
      Seed source → target.Trigger (targetContext source)) :
    CTTransition sourceTactic targetTactic Source target :=
  .mk {
    profileId := profileId
    targetContext := fun stage => targetContext stage.output
    Seed := fun stage => Seed stage.output
    discover := fun stage => discover stage.output
    trigger := fun stage seed => buildTrigger stage.output seed
  }

/-- Framework constructor for a total residual adapter.  The problem layer
supplies only the mathematical context and trigger projections.  The framework
owns the singleton discovery seed, transition construction, exact-stage lookup, and
target execution. -/
def ofTotalResidual
    (profileId : String)
    (targetContext : Source → target.Context)
    (buildTrigger : (source : Source) → target.Trigger (targetContext source)) :
    CTTransition sourceTactic targetTactic Source target :=
  ofAdapter profileId targetContext (fun _ => Unit)
    (fun _ => .enabled ()) (fun source _ => buildTrigger source)

/-- Stable executable transition-profile identifier. -/
def profileId
    (transition : CTTransition.{uSource, uContext, uTrigger, uResult, uSeed}
      sourceTactic targetTactic Source target) : String :=
  transition.kernel.profileId

/-- Target context obtained from the exact accumulated source ledger. -/
def targetContext
    (transition : CTTransition.{uSource, uContext, uTrigger, uResult, uSeed}
      sourceTactic targetTactic Source target)
    (source : ResidualStage sourceTactic Source) : target.Context :=
  transition.kernel.targetContext source

/-- Semantic discovery seed at one exact accumulated source ledger. -/
abbrev Seed
    (transition : CTTransition.{uSource, uContext, uTrigger, uResult, uSeed}
      sourceTactic targetTactic Source target)
    (source : ResidualStage sourceTactic Source) : Type uSeed :=
  transition.kernel.Seed source

/-- Exhaustive semantic discovery at one exact accumulated source ledger. -/
def discover
    (transition : CTTransition.{uSource, uContext, uTrigger, uResult, uSeed}
      sourceTactic targetTactic Source target)
    (source : ResidualStage sourceTactic Source) : Discovery (transition.Seed source) :=
  transition.kernel.discover source

/-- The target trigger indexed by the context selected from the full ledger.
This projection is used by dependent result types; execution remains owned by
`runEnabled` and `run`. -/
def trigger
    (transition : CTTransition.{uSource, uContext, uTrigger, uResult, uSeed}
      sourceTactic targetTactic Source target)
    (source : ResidualStage sourceTactic Source)
    (seed : transition.Seed source) :
    target.Trigger (transition.targetContext source) :=
  transition.kernel.trigger source seed

/-- Precompose a local semantic transition with the current-result projection
of an arbitrary accumulated ledger.  Execution preserves the outer ledger;
the projection is used only to read the local mathematical residual. -/
def onLedger
    {Ledger : Sort uLedger}
    (transition : CTTransition.{uSource, uContext, uTrigger, uResult, uSeed}
      sourceTactic targetTactic Source target)
    (current : Ledger → Source) :
    CTTransition.{uLedger, uContext, uTrigger, uResult, uSeed}
      sourceTactic targetTactic Ledger target :=
  .mk {
    profileId := transition.profileId
    targetContext := fun ledger =>
      transition.targetContext (ResidualStage.exact (current ledger.output))
    Seed := fun ledger =>
      transition.Seed (ResidualStage.exact (current ledger.output))
    discover := fun ledger =>
      transition.discover (ResidualStage.exact (current ledger.output))
    trigger := fun ledger seed =>
      transition.trigger (ResidualStage.exact (current ledger.output)) seed
  }

/-- The complete enabled target execution at one literal source residual. -/
structure EnabledExecution
    (transition : CTTransition.{uSource, uContext, uTrigger, uResult, uSeed}
      sourceTactic targetTactic Source target)
    (source : ResidualStage sourceTactic Source) where
  seed : transition.Seed source
  discovered : transition.discover source = .enabled seed
  result : target.Result (transition.targetContext source)
    (transition.trigger source seed)

/-- The canonical next-stage residual.  It retains the exact predecessor and
stores the target execution indexed by that predecessor. -/
abbrev EnabledStage
    (transition : CTTransition.{uSource, uContext, uTrigger, uResult, uSeed}
      sourceTactic targetTactic Source target)
    (source : ResidualStage sourceTactic Source) :=
  ExactStageHandoff source transition.EnabledExecution

/-- Canonical enabled output over a full accumulated ledger.  Route and
application modules name this instead of re-expanding `onLedger` followed by
`EnabledStage`. -/
abbrev OutputLedger
    {Ledger : Sort uLedger}
    (transition : CTTransition.{uSource, uContext, uTrigger, uResult, uSeed}
      sourceTactic targetTactic Source target)
    (current : Ledger → Source)
    (source : ResidualStage sourceTactic Ledger) :=
  (transition.onLedger current).EnabledStage source

/-- Exhaustive automatic transition result.  Disabled discovery retains the
exact seed-impossibility proof; enabled discovery retains and executes the
target entry. -/
inductive Outcome
    (transition : CTTransition.{uSource, uContext, uTrigger, uResult, uSeed}
      sourceTactic targetTactic Source target)
    (source : ResidualStage sourceTactic Source) where
  | enabled (stage : transition.EnabledStage source)
  | disabled (reject : transition.Seed source → False)
      (discovered : transition.discover source = .disabled reject)

/-- Execute a semantically enabled transition and retain the entire incoming
ledger.  Forced transitions use this directly and never expose an impossible
disabled branch to applications. -/
def runEnabled
    (transition : CTTransition.{uSource, uContext, uTrigger, uResult, uSeed}
      sourceTactic targetTactic Source target)
    (source : ResidualStage sourceTactic Source)
    (seed : transition.Seed source)
    (discovered : transition.discover source = .enabled seed) :
    transition.EnabledStage source :=
  ExactStageHandoff.refl source {
    seed := seed
    discovered := discovered
    result := target.execute (transition.targetContext source)
      (transition.trigger source seed)
  }

/-- Discover, construct, and execute the target CT while retaining the literal
source residual.  This is the only operation applications need after supplying
their mathematical adapter to a framework transition constructor. -/
def run
    (transition : CTTransition.{uSource, uContext, uTrigger, uResult, uSeed}
      sourceTactic targetTactic Source target)
    (source : ResidualStage sourceTactic Source) : transition.Outcome source :=
  match discovery : transition.discover source with
  | .enabled seed =>
      .enabled <| transition.runEnabled source seed discovery
  | .disabled reject => .disabled reject discovery

/-- Execute a reusable local transition over an arbitrary accumulated ledger.
The projection reads the current local residual, while the enabled output
retains the entire outer ledger. -/
def runOnLedger
    {Ledger : Sort uLedger}
    (transition : CTTransition.{uSource, uContext, uTrigger, uResult, uSeed}
      sourceTactic targetTactic Source target)
    (current : Ledger → Source)
    (source : ResidualStage sourceTactic Ledger) :
    (transition.onLedger current).Outcome source :=
  (transition.onLedger current).run source

/-- Forced counterpart of `runOnLedger`.  Transition profiles whose semantic seed
is uniquely enabled return the complete next ledger directly. -/
def runEnabledOnLedger
    {Ledger : Sort uLedger}
    (transition : CTTransition.{uSource, uContext, uTrigger, uResult, uSeed}
      sourceTactic targetTactic Source target)
    (current : Ledger → Source)
    (source : ResidualStage sourceTactic Ledger)
    (seed : (transition.onLedger current).Seed source)
    (discovered :
      (transition.onLedger current).discover source = .enabled seed) :
    (transition.onLedger current).EnabledStage source :=
  (transition.onLedger current).runEnabled source seed discovered

/-- The source residual in every enabled stage is definitionally the value
passed to `run`. -/
@[simp] theorem EnabledStage.previous_eq
    {transition : CTTransition.{uSource, uContext, uTrigger, uResult, uSeed}
      sourceTactic targetTactic Source target}
    {source : ResidualStage sourceTactic Source}
    (stage : transition.EnabledStage source) :
    stage.previous = source :=
  stage.previousExact

/-- Read the target execution at the predecessor named by the incoming edge. -/
def EnabledStage.execution
    {transition : CTTransition.{uSource, uContext, uTrigger, uResult, uSeed}
      sourceTactic targetTactic Source target}
    {source : ResidualStage sourceTactic Source}
    (stage : transition.EnabledStage source) :
    transition.EnabledExecution source :=
  stage.stageAtExpected

/-- The literal mathematical result produced by the target runner. -/
def EnabledStage.targetResult
    {transition : CTTransition.{uSource, uContext, uTrigger, uResult, uSeed}
      sourceTactic targetTactic Source target}
    {source : ResidualStage sourceTactic Source}
    (stage : transition.EnabledStage source) :
    target.Result (transition.targetContext source)
      (transition.trigger source stage.execution.seed) :=
  stage.execution.result

/-- Canonical accumulated ledger for the next transition.  Unlike the bare
target-result projection, this residual stores the exact predecessor and the
target execution together.  Repeated use therefore builds a proof-indexed
history without application-specific `previous` fields. -/
def EnabledStage.ledgerStage
    {transition : CTTransition.{uSource, uContext, uTrigger, uResult, uSeed}
      sourceTactic targetTactic Source target}
    {source : ResidualStage sourceTactic Source}
    (stage : transition.EnabledStage source) :
    ResidualStage targetTactic (transition.EnabledStage source) :=
  ResidualStage.exact stage

@[simp] theorem EnabledStage.ledgerStage_output
    {transition : CTTransition.{uSource, uContext, uTrigger, uResult, uSeed}
      sourceTactic targetTactic Source target}
    {source : ResidualStage sourceTactic Source}
    (stage : transition.EnabledStage source) :
    stage.ledgerStage.output = stage :=
  rfl

/-- Stable source CT spelling derived from the transition type. -/
def sourceTacticId
    (_transition : CTTransition.{uSource, uContext, uTrigger, uResult, uSeed}
      sourceTactic targetTactic Source target) : String :=
  sourceTactic.key

/-- Stable target CT spelling derived from the transition type. -/
def targetTacticId
    (_transition : CTTransition.{uSource, uContext, uTrigger, uResult, uSeed}
      sourceTactic targetTactic Source target) : String :=
  targetTactic.key

end CTTransition

/-! ## Pointwise families of specialized transitions -/

/-- A pointwise family of already selected specialized CT transitions over one
shared accumulated ledger.  Each local transition may have its own semantic
source type and target entry.  The index need not be finite: `advance` below
constructs a dependent function and performs no traversal.

`seed` and `discovered` are the mathematical proof that every local profile is
enabled.  Target execution and predecessor retention remain framework-owned. -/
structure PointwiseTransitionFamily
    (sourceTactic targetTactic : CTId) (Ledger : Sort uLedger) where
  Index : Type uIndex
  Source : Index → Sort uSource
  target : (index : Index) →
    ExecutableInterface.{uContext, uTrigger, uResult} targetTactic
  transition : (index : Index) →
    CTTransition.{uSource, uContext, uTrigger, uResult, uSeed}
      sourceTactic targetTactic (Source index) (target index)
  current : (index : Index) → Ledger → Source index
  seed : (index : Index) → (source : ResidualStage sourceTactic Ledger) →
    ((transition index).onLedger (current index)).Seed source
  discovered : (index : Index) →
    (source : ResidualStage sourceTactic Ledger) →
    ((transition index).onLedger (current index)).discover source =
      .enabled (seed index source)

namespace PointwiseTransitionFamily

/-- The exact specialized enabled stage at one local index. -/
abbrev LocalStage
    (family : PointwiseTransitionFamily.{uLedger, uIndex, uSource, uContext,
      uTrigger, uResult, uSeed} sourceTactic targetTactic Ledger)
    (source : ResidualStage sourceTactic Ledger) (index : family.Index) :=
  ((family.transition index).onLedger (family.current index)).EnabledStage source

/-- All specialized transition stages, indexed pointwise and sharing one
literal predecessor. -/
structure EnabledExecution
    (family : PointwiseTransitionFamily.{uLedger, uIndex, uSource, uContext,
      uTrigger, uResult, uSeed} sourceTactic targetTactic Ledger)
    (source : ResidualStage sourceTactic Ledger) where
  localStage : (index : family.Index) → family.LocalStage source index

/-- One exact aggregate handoff.  The common predecessor is stored once; the
dependent field retains every local specialized transition and its result. -/
abbrev EnabledStage
    (family : PointwiseTransitionFamily.{uLedger, uIndex, uSource, uContext,
      uTrigger, uResult, uSeed} sourceTactic targetTactic Ledger)
    (source : ResidualStage sourceTactic Ledger) :=
  ExactStageHandoff source family.EnabledExecution

/-- Canonical shared output ledger of a specialized pointwise transition
family. -/
abbrev OutputLedger
    (family : PointwiseTransitionFamily.{uLedger, uIndex, uSource, uContext,
      uTrigger, uResult, uSeed} sourceTactic targetTactic Ledger)
    (source : ResidualStage sourceTactic Ledger) :=
  family.EnabledStage source

/-- Execute every selected local transition as a dependent function.  This is
pointwise evaluation, not enumeration of `family.Index`. -/
def advance
    (family : PointwiseTransitionFamily.{uLedger, uIndex, uSource, uContext,
      uTrigger, uResult, uSeed} sourceTactic targetTactic Ledger)
    (source : ResidualStage sourceTactic Ledger) : family.EnabledStage source :=
  ExactStageHandoff.refl source {
    localStage := fun index =>
      (family.transition index).runEnabledOnLedger
        (family.current index) source (family.seed index source)
        (family.discovered index source)
  }

/-- Canonical target-labelled ledger for the next manuscript transition. -/
def EnabledStage.ledgerStage
    {family : PointwiseTransitionFamily.{uLedger, uIndex, uSource, uContext,
      uTrigger, uResult, uSeed} sourceTactic targetTactic Ledger}
    {source : ResidualStage sourceTactic Ledger}
    (stage : family.EnabledStage source) :
    ResidualStage targetTactic (family.EnabledStage source) :=
  ResidualStage.exact stage

/-- Read one local specialized transition without reconstructing it. -/
def EnabledStage.localStage
    {family : PointwiseTransitionFamily.{uLedger, uIndex, uSource, uContext,
      uTrigger, uResult, uSeed} sourceTactic targetTactic Ledger}
    {source : ResidualStage sourceTactic Ledger}
    (stage : family.EnabledStage source) (index : family.Index) :
    family.LocalStage source index :=
  stage.stageAtExpected.localStage index

@[simp] theorem advance_localStage
    (family : PointwiseTransitionFamily.{uLedger, uIndex, uSource, uContext,
      uTrigger, uResult, uSeed} sourceTactic targetTactic Ledger)
    (source : ResidualStage sourceTactic Ledger) (index : family.Index) :
    (family.advance source).localStage index =
      (family.transition index).runEnabledOnLedger
        (family.current index) source (family.seed index source)
        (family.discovered index source) :=
  rfl

end PointwiseTransitionFamily

end Routing
end StructuralExhaustion.Core
