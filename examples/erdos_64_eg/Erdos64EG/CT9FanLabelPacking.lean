import Erdos64EG.CT1TwoWindowCycle
import StructuralExhaustion.Graph.HighCenterPort
import StructuralExhaustion.Graph.P13FanLabelPacking
import StructuralExhaustion.Routes.Accumulated

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u v

/-!
# CT9: certificate-marked fan label packing

Marked fans form a proof-indexed family of specialized CT9 capabilities.  The
framework executes the family pointwise from the complete CT1 ledger; neither
fan centres nor label families are enumerated by the application.
-/

theorem powerOfTwoLength_eight : PowerOfTwoLength 8 := by
  exact ⟨⟨3, by decide⟩, by decide, by decide⟩

structure MarkedFan
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    where
  center : ctx.G.Vertex
  attachment : Graph.HighCenterPort.Port ctx.G.object center → P13Label
  legal : ∀ port, P13Legal (attachment port)
  compatible : ∀ {left right}, left ≠ right →
    Graph.InducedPathAttachment.Compatible 13 PowerOfTwoLength 2
      (attachment left) (attachment right)

namespace MarkedFan

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (fan : MarkedFan ctx)

noncomputable def packingProfile :
    Graph.P13FanLabelPacking.Profile
      (Graph.HighCenterPort.Port ctx.G.object fan.center) where
  LengthOK := PowerOfTwoLength
  items := (Graph.HighCenterPort.ports ctx.G.object fan.center).toOrderedCollection
  attachment := fan.attachment
  nonempty := fun port => (fan.legal port).1
  compatible := fan.compatible
  acceptsFour := powerOfTwoLength_four
  acceptsEight := powerOfTwoLength_eight
  acceptsSixteen := ⟨⟨4, by decide⟩, by decide, by decide⟩

theorem degree_le_eight : ctx.G.object.degree fan.center ≤ 8 := by
  have bound := fan.packingProfile.cardinality_le_eight ctx.toBranchContext
  change (Graph.HighCenterPort.ports ctx.G.object
    fan.center).orderedValues.length ≤ 8 at bound
  rw [FinEnum.orderedValues_length,
    Graph.HighCenterPort.ports_card_eq_degree] at bound
  exact bound

end MarkedFan

noncomputable def fanLabelPackingTarget
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (fan : MarkedFan ctx) :=
  (fan.packingProfile.capability PackedProblem.{u}).executableInterface

noncomputable def fanLabelPackingAdapter
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (fan : MarkedFan ctx) :
    Routes.Accumulated.Adapter Unit (fanLabelPackingTarget ctx fan) where
  targetContext := fun _source =>
    (fan.packingProfile.input ctx.toBranchContext).context
  trigger := fun _source => ⟨fan.packingProfile.items⟩

noncomputable def fanLabelPackingTransition
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (fan : MarkedFan ctx) :=
  Routes.Accumulated.transition (sourceTactic := .ct1)
    (fanLabelPackingTarget ctx fan) (fanLabelPackingAdapter ctx fan)

noncomputable def fanLabelPackingPointwiseAdapter
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (Ledger : Sort v) :
    Routes.Accumulated.PointwiseAdapter .ct1 .ct9 (MarkedFan ctx) Ledger where
  Source := fun _fan => Unit
  target := fanLabelPackingTarget ctx
  adapter := fanLabelPackingAdapter ctx
  current := fun _fan _ledger => ()

noncomputable def fanLabelPackingTransitionFamily
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (Ledger : Sort v) :=
  Routes.Accumulated.pointwiseFamily
    (fanLabelPackingPointwiseAdapter ctx Ledger)

noncomputable def fanLabelPackingTransitionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct1 Ledger) :=
  Routes.Accumulated.advancePointwise
    (fanLabelPackingPointwiseAdapter ctx Ledger) source

abbrev FanLabelPackingTransitionLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct1 Ledger) :=
  Routes.Accumulated.PointwiseOutputLedger
    (fanLabelPackingPointwiseAdapter ctx Ledger) source

structure FanLabelPackingFacts
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (fan : MarkedFan ctx)
    (execution : CT9.ExecutionResult
      (fan.packingProfile.capability PackedProblem.{u})
      (fan.packingProfile.input ctx.toBranchContext)) : Prop where
  terminal : execution.terminal = .bounded
  trace : execution.trace = [.entry, .partition, .overload, .boundedTerminal]
  degreeBound : ctx.G.object.degree fan.center ≤ 8

abbrev FanLabelPackingLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct1 Ledger) :=
  Core.Routing.LedgerExtension (FanLabelPackingTransitionLedger ctx source)
    (fun execution => ∀ fan : MarkedFan ctx,
      FanLabelPackingFacts ctx fan (execution.localStage fan).targetResult)

noncomputable def fanLabelPackingLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct1 Ledger) :
    Core.Routing.ResidualStage .ct9 (FanLabelPackingLedger ctx source) := by
  let execution := fanLabelPackingTransitionStage ctx source
  exact execution.extend (fun fan => {
    terminal := by
      change (CT9.run (fan.packingProfile.capability PackedProblem.{u})
        (fan.packingProfile.input ctx.toBranchContext)).terminal = .bounded
      exact CT9.run_terminal_bounded_of_bounded _ _
        (fan.packingProfile.bounded ctx.toBranchContext)
    trace := by
      change (CT9.run (fan.packingProfile.capability PackedProblem.{u})
        (fan.packingProfile.input ctx.toBranchContext)).trace = _
      exact CT9.run_trace_bounded_of_bounded _ _
        (fan.packingProfile.bounded ctx.toBranchContext)
    degreeBound := fan.degree_le_eight
  })

noncomputable def runFanLabelPackingCT9
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct1 Ledger}
    (stage : Core.Routing.ResidualStage .ct9
      (FanLabelPackingLedger ctx source))
    (fan : MarkedFan ctx) :=
  (stage.output.previous.localStage fan).targetResult

theorem fanLabelPackingTransition_profile_id
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (fan : MarkedFan ctx) :
    (fanLabelPackingTransition ctx fan).profileId =
      "CT1.residual.accumulatedLedger->CT9" :=
  Routes.Accumulated.transition_profile_id
    (fanLabelPackingTarget ctx fan) (fanLabelPackingAdapter ctx fan)

noncomputable def FanLabelPackingStep
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedTwoWindowCyclePrefix ctx) := by
  rcases previous with ⟨directPrefix, twoWindowStage⟩
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
        (FanLabelPackingLedger ctx twoWindowStage)
  | bounded _certificate =>
      exact PUnit

abbrev VerifiedFanLabelPackingPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.LedgerExtension (VerifiedTwoWindowCyclePrefix ctx)
    (FanLabelPackingStep ctx)

noncomputable def verifiedFanLabelPackingPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedTwoWindowCyclePrefix ctx) :
    VerifiedFanLabelPackingPrefix ctx :=
  ⟨previous, by
    rcases previous with ⟨directPrefix, twoWindowStage⟩
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
      ⟨responsePrefix, compatibilityContinuation⟩
    rcases responsePrefix with ⟨sourceLedger, state⟩
    rcases sourceLedger with ⟨openPortPairLedger, openPortState⟩
    cases openPortState with
    | routed source =>
        exact fanLabelPackingLedgerStage ctx twoWindowStage
    | bounded certificate =>
        exact PUnit.unit
  ⟩

theorem exists_verifiedFanLabelPackingPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedFanLabelPackingPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedTwoWindowCyclePrefix object baseline avoids
  exact ⟨ctx, verifiedFanLabelPackingPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
