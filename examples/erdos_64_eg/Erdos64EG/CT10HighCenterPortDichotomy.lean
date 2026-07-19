import Erdos64EG.CT7OpenPortCompatibility
import StructuralExhaustion.Graph.HighCenterPort
import StructuralExhaustion.Routes.Accumulated

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u uLedger

/-!
# CT10: all-incident-port dichotomy at high centres

The framework profile executes pointwise on each requested centre's declared
neighbour list.  It classifies every actual incident port as open or triangular,
then combines the classification with four-cycle avoidance.  The pointwise
family is a dependent function and performs no centre-universe enumeration.
-/

abbrev HighCenterPortStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex)
    (centerHigh : 4 ≤ ctx.G.object.degree center) :=
  Graph.HighCenterPort.VerifiedStage
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline center centerHigh
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    (fourCycleFree ctx)

theorem highCenterPort_stage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex)
    (centerHigh : 4 ≤ ctx.G.object.degree center) :
    HighCenterPortStage ctx center centerHigh :=
  Graph.HighCenterPort.verifiedStage
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline center centerHigh
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    (fourCycleFree ctx)

abbrev HighCenterIndex
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  {center : ctx.G.Vertex // 4 ≤ ctx.G.object.degree center}

/- One public CT10 execution at every requested high centre.  This is a
dependent function, not an enumeration of centres or port pairs. -/
def highCenterPortFamily
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Core.Routing.PointwiseExecutableFamily .ct10 where
  Index := HighCenterIndex ctx
  entry := fun center =>
    (Graph.HighCenterPort.classificationCapability
      (fixedPackedInput ctx) ctx.G.object center.1 center.2
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx))).executableInterface
  context := fun center =>
    (Graph.HighCenterPort.classificationInput
      (fixedPackedInput ctx) ctx.G.object
      (packedStaticInput.fixedContext ctx).baseline center.1 center.2
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx))).context
  trigger := fun center =>
    ⟨(Graph.HighCenterPort.classificationInput
      (fixedPackedInput ctx) ctx.G.object
      (packedStaticInput.fixedContext ctx).baseline center.1 center.2
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx))).data⟩

def highCenterPortAdapter
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort uLedger} :
    Routes.Accumulated.Adapter Ledger
      (highCenterPortFamily ctx).executableInterface where
  targetContext := fun _ledger => ()
  trigger := fun _ledger => ()

def highCenterPortTransitionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort uLedger}
    (source : Core.Routing.ResidualStage .ct5 Ledger) :=
  Routes.Accumulated.advanceCurrent
    (highCenterPortFamily ctx).executableInterface
    (highCenterPortAdapter ctx) source

abbrev HighCenterPortTransitionLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort uLedger}
    (source : Core.Routing.ResidualStage .ct5 Ledger) :=
  Routes.Accumulated.OutputLedger
    (highCenterPortFamily ctx).executableInterface
    (highCenterPortAdapter ctx) source

abbrev HighCenterPortLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort uLedger}
    (source : Core.Routing.ResidualStage .ct5 Ledger) :=
  Core.Routing.LedgerExtension
    (HighCenterPortTransitionLedger ctx source)
    (fun _execution => ∀ center (centerHigh : 4 ≤ ctx.G.object.degree center),
      HighCenterPortStage ctx center centerHigh)

def highCenterPortLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort uLedger}
    (source : Core.Routing.ResidualStage .ct5 Ledger) :
    Core.Routing.ResidualStage .ct10 (HighCenterPortLedger ctx source) :=
  (highCenterPortTransitionStage ctx source).extend
    (highCenterPort_stage ctx)

/-- The high-centre CT10 execution extends the exact compatibility prefix.
The bounded edge remains `PUnit`; only the routed edge stores a new CT10
stage, so the large accumulated ledger is never copied into constructors. -/
noncomputable def HighCenterPortContinuation
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedOpenPortCompatibilityPrefix ctx) :=
  match previous with
  | ⟨⟨⟨_sourceLedger, .bounded _certificate⟩,
      _shoulderContinuation⟩, _compatibilityContinuation⟩ => PUnit
  | ⟨⟨⟨_sourceLedger, .routed _source⟩,
      _shoulderContinuation⟩, compatibilityContinuation⟩ =>
      Core.Routing.ResidualStage .ct10
        (HighCenterPortLedger ctx compatibilityContinuation)

abbrev VerifiedHighCenterPortDichotomyPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.LedgerExtension (VerifiedOpenPortCompatibilityPrefix ctx)
    (HighCenterPortContinuation ctx)

noncomputable def verifiedHighCenterPortDichotomyPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedOpenPortCompatibilityPrefix ctx) :
    VerifiedHighCenterPortDichotomyPrefix ctx := by
  rcases previous with
    ⟨⟨⟨sourceLedger, state⟩, shoulderContinuation⟩,
      compatibilityContinuation⟩
  cases state with
  | bounded certificate =>
      exact ⟨⟨⟨⟨sourceLedger, .bounded certificate⟩,
        shoulderContinuation⟩, compatibilityContinuation⟩, PUnit.unit⟩
  | routed source =>
      exact ⟨⟨⟨⟨sourceLedger, .routed source⟩,
        shoulderContinuation⟩, compatibilityContinuation⟩,
        highCenterPortLedgerStage ctx compatibilityContinuation⟩

theorem exists_verifiedHighCenterPortDichotomyPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedHighCenterPortDichotomyPrefix ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedOpenPortCompatibilityPrefix object baseline avoids
  exact ⟨ctx, verifiedHighCenterPortDichotomyPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
