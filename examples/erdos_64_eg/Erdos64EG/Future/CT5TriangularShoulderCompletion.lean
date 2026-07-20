import Erdos64EG.Future.CT10HighCenterPortDichotomy
import StructuralExhaustion.Graph.TriangularShoulderCompletion
import StructuralExhaustion.Routes.Accumulated

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u v

/-!
# CT5: triangular shoulder-completion bookkeeping

The framework owns the actual triangular-port shoulder sites, completion
incidences, all four structural clauses, the CT5 witness search, and its work
bound.  This module only supplies the verified Erdős graph hypotheses.
-/

def triangularShoulderSetup
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center) :
    Graph.TriangularShoulderCompletion.Setup
      (fixedPackedInput ctx) ctx.G.object
      (packedStaticInput.fixedContext ctx).baseline center where
  centerHigh := centerHigh
  threeLeMinimum := Nat.le_refl 3
  deletionCritical :=
    (fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx)
  fourFree := fourCycleFree ctx

abbrev TriangularShoulderStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center) :=
  Graph.TriangularShoulderCompletion.VerifiedStage
    (triangularShoulderSetup ctx center centerHigh)

theorem triangularShoulder_stage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center) :
    TriangularShoulderStage ctx center centerHigh :=
  Graph.TriangularShoulderCompletion.verifiedStage
    (triangularShoulderSetup ctx center centerHigh)

/-- Proof-indexed centres at which the manuscript requests one CT5 shoulder
audit.  This is a dependent function index and is never enumerated. -/
abbrev TriangularShoulderIndex
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  { center : ctx.G.Vertex // 4 ≤ ctx.G.object.degree center }

/-- One public CT5 entry at every supplied high centre. -/
noncomputable def triangularShoulderFamily
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Core.Routing.PointwiseExecutableFamily .ct5 where
  Index := TriangularShoulderIndex ctx
  entry := fun index =>
    (Graph.TriangularShoulderCompletion.capability
      (triangularShoulderSetup ctx index.1 index.2)).executableInterface
  context := fun index =>
    Graph.TriangularShoulderCompletion.context
      (fixedPackedInput ctx) ctx.G.object
      (packedStaticInput.fixedContext ctx).baseline
  trigger := fun _index => ()

/-- The CT10→CT5 edge changes no graph context; all local mathematical
inputs are fixed by the pointwise family above. -/
def triangularShoulderAdapter {Source : Sort v}
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Routes.Accumulated.Adapter Source
      (triangularShoulderFamily ctx).executableInterface where
  targetContext := fun _source => ()
  trigger := fun _source => ()

noncomputable def triangularShoulderTransitionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct10 Ledger) :=
  Routes.Accumulated.advanceCurrent
    (triangularShoulderFamily ctx).executableInterface
    (triangularShoulderAdapter ctx) source

abbrev TriangularShoulderTransitionLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct10 Ledger) :=
  Routes.Accumulated.OutputLedger
    (triangularShoulderFamily ctx).executableInterface
    (triangularShoulderAdapter ctx) source

abbrev TriangularShoulderLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct10 Ledger) :=
  Core.Routing.LedgerExtension
    (TriangularShoulderTransitionLedger ctx source)
    (fun _execution => ∀ center (centerHigh : 4 ≤ ctx.G.object.degree center),
      TriangularShoulderStage ctx center centerHigh)

/-- The real CT10→CT5 edge followed by the graph-level shoulder theorem.
The extension retains the literal pointwise CT5 execution as its predecessor. -/
noncomputable def triangularShoulderLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct10 Ledger) :
    Core.Routing.ResidualStage .ct5 (TriangularShoulderLedger ctx source) :=
  (triangularShoulderTransitionStage ctx source).extend
    (triangularShoulder_stage ctx)

/-- Literal dependent CT5 result produced by the transition. -/
noncomputable def runTriangularShoulderCT5
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct10 Ledger}
    (stage : Core.Routing.ResidualStage .ct5
      (TriangularShoulderLedger ctx source)) :=
  stage.output.previous.targetResult

/-- Graph semantics attached to that same execution ledger. -/
def triangularShoulderStageAt
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct10 Ledger}
    (stage : Core.Routing.ResidualStage .ct5
      (TriangularShoulderLedger ctx source))
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center) :
    TriangularShoulderStage ctx center centerHigh :=
  stage.output.added center centerHigh

theorem triangularShoulderTransition_profile_id
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v} :
    (Routes.Accumulated.transition (sourceTactic := .ct10)
      (Source := Ledger) (triangularShoulderFamily ctx).executableInterface
      (triangularShoulderAdapter ctx)).profileId =
        "CT10.residual.accumulatedLedger->CT5" :=
  Routes.Accumulated.transition_profile_id
    (triangularShoulderFamily ctx).executableInterface
    (triangularShoulderAdapter ctx)

noncomputable def TriangularShoulderContinuation
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedHighCenterPortDichotomyPrefix ctx) :=
  match previous with
  | ⟨⟨⟨⟨_sourceLedger, .bounded _certificate⟩,
      _shoulderContinuation⟩, _compatibilityContinuation⟩,
      _highCenterContinuation⟩ => PUnit
  | ⟨⟨⟨⟨_sourceLedger, .routed _source⟩,
      _shoulderContinuation⟩, _compatibilityContinuation⟩,
      highCenterContinuation⟩ =>
      Core.Routing.ResidualStage .ct5
        (TriangularShoulderLedger ctx highCenterContinuation)

abbrev VerifiedTriangularShoulderCompletionPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.LedgerExtension (VerifiedHighCenterPortDichotomyPrefix ctx)
    (TriangularShoulderContinuation ctx)

noncomputable def verifiedTriangularShoulderCompletionPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedHighCenterPortDichotomyPrefix ctx) :
    VerifiedTriangularShoulderCompletionPrefix ctx := by
  rcases previous with
    ⟨⟨⟨⟨sourceLedger, state⟩, shoulderContinuation⟩,
      compatibilityContinuation⟩, highCenterContinuation⟩
  cases state with
  | bounded certificate =>
      exact ⟨⟨⟨⟨⟨sourceLedger, .bounded certificate⟩,
        shoulderContinuation⟩, compatibilityContinuation⟩,
        highCenterContinuation⟩, PUnit.unit⟩
  | routed source =>
      exact ⟨⟨⟨⟨⟨sourceLedger, .routed source⟩,
        shoulderContinuation⟩, compatibilityContinuation⟩,
        highCenterContinuation⟩,
        triangularShoulderLedgerStage ctx highCenterContinuation⟩

theorem exists_verifiedTriangularShoulderCompletionPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedTriangularShoulderCompletionPrefix ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedHighCenterPortDichotomyPrefix object baseline avoids
  exact ⟨ctx, verifiedTriangularShoulderCompletionPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
