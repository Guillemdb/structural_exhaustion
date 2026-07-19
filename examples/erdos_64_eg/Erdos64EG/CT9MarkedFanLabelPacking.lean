import Erdos64EG.CT9FanLabelPacking
import StructuralExhaustion.Graph.P13MarkedFanLabelPacking

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u v

/-!
# CT9: non-singleton marked-fan strengthening

The six-slot strengthening is a pointwise CT9→CT9 transition from the exact
eight-slot fan ledger.  No marked fan or label family is enumerated.
-/

structure NonSingletonMarkedFan
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    where
  fan : MarkedFan ctx
  port : Graph.HighCenterPort.Port ctx.G.object fan.center
  first : Fin 13
  second : Fin 13
  first_mem : first ∈ fan.attachment port
  second_mem : second ∈ fan.attachment port
  positions_distinct : first ≠ second

namespace NonSingletonMarkedFan

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (marked : NonSingletonMarkedFan ctx)

noncomputable def packingProfile :
    Graph.P13MarkedFanLabelPacking.Profile marked.fan.packingProfile where
  distinguished := marked.port
  distinguished_mem :=
    (Graph.HighCenterPort.ports ctx.G.object marked.fan.center).mem_orderedValues _
  first := marked.first
  second := marked.second
  first_mem := marked.first_mem
  second_mem := marked.second_mem
  positions_distinct := marked.positions_distinct

theorem degree_le_seven : ctx.G.object.degree marked.fan.center ≤ 7 := by
  have bound := marked.packingProfile.cardinality_le_seven ctx.toBranchContext
  change (Graph.HighCenterPort.ports ctx.G.object
    marked.fan.center).orderedValues.length ≤ 7 at bound
  rw [FinEnum.orderedValues_length,
    Graph.HighCenterPort.ports_card_eq_degree] at bound
  exact bound

end NonSingletonMarkedFan

noncomputable def markedFanLabelPackingTarget
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (marked : NonSingletonMarkedFan ctx) :=
  (marked.packingProfile.capability PackedProblem.{u}).executableInterface

noncomputable def markedFanLabelPackingAdapter
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (marked : NonSingletonMarkedFan ctx) :
    Routes.Accumulated.Adapter Unit (markedFanLabelPackingTarget ctx marked) where
  targetContext := fun _source =>
    (marked.packingProfile.input ctx.toBranchContext).context
  trigger := fun _source => ⟨marked.packingProfile.otherItems⟩

noncomputable def markedFanLabelPackingTransition
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (marked : NonSingletonMarkedFan ctx) :=
  Routes.Accumulated.transition (sourceTactic := .ct9)
    (markedFanLabelPackingTarget ctx marked)
    (markedFanLabelPackingAdapter ctx marked)

noncomputable def markedFanLabelPackingPointwiseAdapter
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (Ledger : Sort v) :
    Routes.Accumulated.PointwiseAdapter .ct9 .ct9
      (NonSingletonMarkedFan ctx) Ledger where
  Source := fun _marked => Unit
  target := markedFanLabelPackingTarget ctx
  adapter := markedFanLabelPackingAdapter ctx
  current := fun _marked _ledger => ()

noncomputable def markedFanLabelPackingTransitionFamily
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (Ledger : Sort v) :=
  Routes.Accumulated.pointwiseFamily
    (markedFanLabelPackingPointwiseAdapter ctx Ledger)

noncomputable def markedFanLabelPackingTransitionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct9 Ledger) :=
  Routes.Accumulated.advancePointwise
    (markedFanLabelPackingPointwiseAdapter ctx Ledger) source

noncomputable def MarkedFanLabelPackingTransitionLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct9 Ledger) :=
  Routes.Accumulated.PointwiseOutputLedger
    (markedFanLabelPackingPointwiseAdapter ctx Ledger) source

/-- Concrete CT9 result at one request, exposed through one opaque projection
so downstream types never normalize the whole dependent family. -/
noncomputable def markedFanLabelPackingLocalResult
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct9 Ledger}
    (execution : MarkedFanLabelPackingTransitionLedger ctx source)
    (marked : NonSingletonMarkedFan ctx) :
    CT9.ExecutionResult (marked.packingProfile.capability PackedProblem.{u})
      (marked.packingProfile.input ctx.toBranchContext) :=
  (execution.localStage marked).targetResult

@[simp] theorem markedFanLabelPackingLocalResult_transition
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct9 Ledger)
    (marked : NonSingletonMarkedFan ctx) :
    markedFanLabelPackingLocalResult ctx
        (markedFanLabelPackingTransitionStage ctx source).output marked =
      CT9.run (marked.packingProfile.capability PackedProblem.{u})
        (marked.packingProfile.input ctx.toBranchContext) :=
  rfl

structure MarkedFanLabelPackingFacts
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct9 Ledger}
    (execution : MarkedFanLabelPackingTransitionLedger ctx source) : Prop where
  terminal : ∀ marked : NonSingletonMarkedFan ctx,
    (markedFanLabelPackingLocalResult ctx execution marked).terminal = .bounded
  trace : ∀ marked : NonSingletonMarkedFan ctx,
    (markedFanLabelPackingLocalResult ctx execution marked).trace =
      [.entry, .partition, .overload, .boundedTerminal]
  degreeBound : ∀ marked : NonSingletonMarkedFan ctx,
    ctx.G.object.degree marked.fan.center ≤ 7

abbrev MarkedFanLabelPackingLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct9 Ledger) :=
  Core.Routing.LedgerExtension
    (MarkedFanLabelPackingTransitionLedger ctx source)
    (MarkedFanLabelPackingFacts ctx)

noncomputable def markedFanLabelPackingFacts
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct9 Ledger) :
    MarkedFanLabelPackingFacts ctx
      (markedFanLabelPackingTransitionStage ctx source).output where
  terminal := fun marked => by
    rw [markedFanLabelPackingLocalResult_transition]
    exact CT9.run_terminal_bounded_of_bounded _ _
      (marked.packingProfile.bounded ctx.toBranchContext)
  trace := fun marked => by
    rw [markedFanLabelPackingLocalResult_transition]
    exact CT9.run_trace_bounded_of_bounded _ _
      (marked.packingProfile.bounded ctx.toBranchContext)
  degreeBound := fun marked => marked.degree_le_seven

noncomputable def markedFanLabelPackingLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct9 Ledger) :
    Core.Routing.ResidualStage .ct9
      (MarkedFanLabelPackingLedger ctx source) := by
  let execution := markedFanLabelPackingTransitionStage ctx source
  let executionStage : Core.Routing.ResidualStage .ct9
      (MarkedFanLabelPackingTransitionLedger ctx source) :=
    execution
  exact executionStage.extend (markedFanLabelPackingFacts ctx source)

noncomputable def runMarkedFanLabelPackingCT9
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct9 Ledger}
    (stage : Core.Routing.ResidualStage .ct9
      (MarkedFanLabelPackingLedger ctx source))
    (marked : NonSingletonMarkedFan ctx) :=
  markedFanLabelPackingLocalResult ctx stage.output.previous marked

theorem markedFanLabelPackingTransition_profile_id
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (marked : NonSingletonMarkedFan ctx) :
    (markedFanLabelPackingTransition ctx marked).profileId =
      "CT9.residual.accumulatedLedger->CT9" :=
  Routes.Accumulated.transition_profile_id
    (markedFanLabelPackingTarget ctx marked)
    (markedFanLabelPackingAdapter ctx marked)

noncomputable def MarkedFanLabelPackingStep
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedFanLabelPackingPrefix ctx) := by
  rcases previous with ⟨twoWindowPrefix, fanLabelStage⟩
  rcases twoWindowPrefix with ⟨directPrefix, _twoWindowStage⟩
  rcases directPrefix with ⟨hybridPrefix, _directStage⟩
  rcases hybridPrefix with ⟨massPrefix, _hybridStage⟩
  rcases massPrefix with ⟨fanPrefix, _massStage⟩
  rcases fanPrefix with ⟨crossPrefix, _fanStage⟩
  rcases crossPrefix with ⟨landingPrefix, _crossStage⟩
  rcases landingPrefix with ⟨returnPrefix, _landingContinuation⟩
  rcases returnPrefix with ⟨bridgePrefix, _returnContinuation⟩
  rcases bridgePrefix with ⟨shoulderPrefix, _bridgeContinuation⟩
  rcases shoulderPrefix with
    ⟨highCenterPrefix, _triangularShoulderContinuation⟩
  rcases highCenterPrefix with
    ⟨compatibilityPrefix, _highCenterContinuation⟩
  rcases compatibilityPrefix with
    ⟨shoulderLedgerPrefix, _compatibilityContinuation⟩
  rcases shoulderLedgerPrefix with
    ⟨responsePrefix, _shoulderContinuation⟩
  rcases responsePrefix with ⟨_sourceLedger, state⟩
  cases state with
  | routed _source =>
      exact Core.Routing.ResidualStage .ct9
        (MarkedFanLabelPackingLedger ctx fanLabelStage)
  | bounded _certificate =>
      exact PUnit

abbrev VerifiedMarkedFanLabelPackingPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.LedgerExtension (VerifiedFanLabelPackingPrefix ctx)
    (MarkedFanLabelPackingStep ctx)

noncomputable def verifiedMarkedFanLabelPackingPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedFanLabelPackingPrefix ctx) :
    VerifiedMarkedFanLabelPackingPrefix ctx :=
  ⟨previous, by
    rcases previous with ⟨twoWindowPrefix, fanLabelStage⟩
    rcases twoWindowPrefix with ⟨directPrefix, twoWindowStage⟩
    rcases directPrefix with ⟨hybridPrefix, directStage⟩
    rcases hybridPrefix with ⟨massPrefix, hybridStage⟩
    rcases massPrefix with ⟨fanPrefix, massStage⟩
    rcases fanPrefix with ⟨crossPrefix, fanStage⟩
    rcases crossPrefix with ⟨landingPrefix, crossStage⟩
    rcases landingPrefix with ⟨returnPrefix, landingContinuation⟩
    rcases returnPrefix with ⟨bridgePrefix, returnContinuation⟩
    rcases bridgePrefix with ⟨shoulderPrefix, bridgeContinuation⟩
    rcases shoulderPrefix with
      ⟨highCenterPrefix, triangularShoulderContinuation⟩
    rcases highCenterPrefix with
      ⟨compatibilityPrefix, highCenterContinuation⟩
    rcases compatibilityPrefix with
      ⟨shoulderLedgerPrefix, compatibilityContinuation⟩
    rcases shoulderLedgerPrefix with
      ⟨responsePrefix, shoulderContinuation⟩
    rcases responsePrefix with ⟨_sourceLedger, state⟩
    cases state with
    | routed _source =>
        exact markedFanLabelPackingLedgerStage ctx fanLabelStage
    | bounded _certificate =>
        exact PUnit.unit
  ⟩

theorem exists_verifiedMarkedFanLabelPackingPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedMarkedFanLabelPackingPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedFanLabelPackingPrefix object baseline avoids
  exact ⟨ctx, verifiedMarkedFanLabelPackingPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
