import Erdos64EG.CT9FanLabelPacking
import StructuralExhaustion.Graph.P13MarkedFanLabelPacking

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT9: non-singleton marked-fan strengthening

This file completes the second packing clause of `lem:fan-certificate`.
The application identifies one actual fan port whose already certified legal
label contains two distinct positions. The graph framework removes that port,
blocks two exact CT9 slots, proves the remaining six-slot capacity bound, and
returns `degree center ≤ 7`.
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

noncomputable def run : CT9.BoundedRun
    (marked.packingProfile.capability PackedProblem.{u})
    (marked.packingProfile.input ctx.toBranchContext) :=
  marked.packingProfile.run ctx.toBranchContext

theorem run_terminal : marked.run.execution.terminal = .bounded :=
  marked.run.terminal_eq

theorem run_trace : marked.run.execution.trace =
    [.entry, .partition, .overload, .boundedTerminal] :=
  marked.run.trace_eq

theorem degree_le_seven : ctx.G.object.degree marked.fan.center ≤ 7 := by
  have bound := marked.packingProfile.cardinality_le_seven ctx.toBranchContext
  change (Graph.HighCenterPort.ports ctx.G.object
    marked.fan.center).orderedValues.length ≤ 7 at bound
  rw [FinEnum.orderedValues_length,
    Graph.HighCenterPort.ports_card_eq_degree] at bound
  exact bound

end NonSingletonMarkedFan

structure VerifiedMarkedFanLabelPackingPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedFanLabelPackingPrefix ctx
  degreeBound : ∀ marked : NonSingletonMarkedFan ctx,
    ctx.G.object.degree marked.fan.center ≤ 7
  terminal : ∀ marked : NonSingletonMarkedFan ctx,
    marked.run.execution.terminal = .bounded
  trace : ∀ marked : NonSingletonMarkedFan ctx,
    marked.run.execution.trace =
      [.entry, .partition, .overload, .boundedTerminal]

noncomputable def verifiedMarkedFanLabelPackingPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedFanLabelPackingPrefix ctx) :
    VerifiedMarkedFanLabelPackingPrefix ctx where
  previous := previous
  degreeBound := fun marked => marked.degree_le_seven
  terminal := fun marked => marked.run_terminal
  trace := fun marked => marked.run_trace

theorem exists_verifiedMarkedFanLabelPackingPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedMarkedFanLabelPackingPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedFanLabelPackingPrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedMarkedFanLabelPackingPrefix ctx previous⟩

end Erdos64EG.Internal
