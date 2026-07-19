import Erdos64EG.CT1FanWindowCycle
import StructuralExhaustion.Graph.TwoWindowCycle

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u v

/-!
# CT1: direct cycles through two packed windows

The preceding CT1 avoiding execution already proves that the selected graph
contains no target cycle.  The two-window constructor is therefore a same-CT
theorem extension of that exact ledger, not a second CT1 run.
-/

structure TwoWindowCycleFacts
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  directFree : ∀ {firstOrder secondOrder : Nat}
    {firstPath : SimpleGraph.pathGraph firstOrder ↪g ctx.G.object.graph}
    {secondPath : SimpleGraph.pathGraph secondOrder ↪g ctx.G.object.graph}
    (data : Graph.TwoWindowCycle.Data firstPath secondPath),
    Graph.TwoWindowCycle.DirectCycleFree PowerOfTwoLength data

abbrev TwoWindowCycleLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct1 Ledger) :=
  Core.Routing.LedgerExtension Ledger (fun _previous => TwoWindowCycleFacts ctx)

def twoWindowCycleLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct1 Ledger) :
    Core.Routing.ResidualStage .ct1 (TwoWindowCycleLedger ctx source) :=
  source.extend {
    directFree := Graph.TwoWindowCycle.directCycleFree_of_avoids
      PowerOfTwoLength (packedStaticInput.fixedContext ctx).avoids
  }

theorem packedTwoWindow_directCycleFree
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct1 Ledger}
    (stage : Core.Routing.ResidualStage .ct1
      (TwoWindowCycleLedger ctx source))
    {firstOrder secondOrder : Nat}
    {firstPath : SimpleGraph.pathGraph firstOrder ↪g ctx.G.object.graph}
    {secondPath : SimpleGraph.pathGraph secondOrder ↪g ctx.G.object.graph}
    (data : Graph.TwoWindowCycle.Data firstPath secondPath) :
    Graph.TwoWindowCycle.DirectCycleFree PowerOfTwoLength data :=
  stage.output.added.directFree data

noncomputable def TwoWindowCycleStep
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedDirectFanWindowPrefix ctx) := by
  rcases previous with ⟨hybridPrefix, directStage⟩
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
      exact Core.Routing.ResidualStage .ct1
        (TwoWindowCycleLedger ctx directStage)
  | bounded _certificate =>
      exact PUnit

abbrev VerifiedTwoWindowCyclePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.LedgerExtension (VerifiedDirectFanWindowPrefix ctx)
    (TwoWindowCycleStep ctx)

noncomputable def verifiedTwoWindowCyclePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedDirectFanWindowPrefix ctx) :
    VerifiedTwoWindowCyclePrefix ctx :=
  ⟨previous, by
    rcases previous with ⟨hybridPrefix, directStage⟩
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
        exact twoWindowCycleLedgerStage ctx directStage
    | bounded certificate =>
        exact PUnit.unit
  ⟩

theorem exists_verifiedTwoWindowCyclePrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedTwoWindowCyclePrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedDirectFanWindowPrefix object baseline avoids
  exact ⟨ctx, verifiedTwoWindowCyclePrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
