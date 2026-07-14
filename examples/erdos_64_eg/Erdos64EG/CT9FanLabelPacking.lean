import Erdos64EG.CT1TwoWindowCycle
import StructuralExhaustion.Graph.HighCenterPort
import StructuralExhaustion.Graph.P13FanLabelPacking

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT9: certificate-marked fan label packing

This file implements the first, degree-cap clause of
`lem:fan-certificate`. A marked fan supplies exactly the manuscript's
certificate map on the actual incident ports: every label is legal and every
two distinct labels are compatible at scale two. The framework chooses
representatives, executes the eight-fibre CT9 profile, and derives the degree
bound. No label code or label family is enumerated here.
-/

theorem powerOfTwoLength_eight : PowerOfTwoLength 8 := by
  exact ⟨⟨3, by decide⟩, by decide, by decide⟩

/-- Application contract corresponding exactly to a certificate-marked fan.
The incident ports are the actual neighbours in the finite object's declared
order; `legal` and `compatible` are the two mathematical clauses in the
manuscript definition, not conclusions of this stage. -/
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

/-- Thin instantiation of the graph-owned representative-packing profile. -/
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
  acceptsSixteen := by
    exact ⟨⟨4, by decide⟩, by decide, by decide⟩

/-- Exact CT9 bounded execution on the actual incident-port collection. -/
noncomputable def run : CT9.BoundedRun
    (fan.packingProfile.capability PackedProblem.{u})
    (fan.packingProfile.input ctx.toBranchContext) :=
  fan.packingProfile.run ctx.toBranchContext

theorem run_terminal : fan.run.execution.terminal = .bounded :=
  fan.run.terminal_eq

theorem run_trace : fan.run.execution.trace =
    [.entry, .partition, .overload, .boundedTerminal] :=
  fan.run.trace_eq

/-- The structural label-packing cap, derived from the CT9 certificate rather
than stored in the marked-fan contract. -/
theorem degree_le_eight : ctx.G.object.degree fan.center ≤ 8 := by
  have bound := fan.packingProfile.cardinality_le_eight
    ctx.toBranchContext
  change (Graph.HighCenterPort.ports ctx.G.object fan.center).orderedValues.length ≤
    8 at bound
  rw [FinEnum.orderedValues_length,
    Graph.HighCenterPort.ports_card_eq_degree] at bound
  exact bound

end MarkedFan

/-- Prefix extension retaining the previous graph and exporting the verified
conditional contract for every certificate-marked fan on that graph. -/
structure VerifiedFanLabelPackingPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedTwoWindowCyclePrefix ctx
  degreeBound : ∀ fan : MarkedFan ctx, ctx.G.object.degree fan.center ≤ 8
  terminal : ∀ fan : MarkedFan ctx, fan.run.execution.terminal = .bounded
  trace : ∀ fan : MarkedFan ctx, fan.run.execution.trace =
    [.entry, .partition, .overload, .boundedTerminal]

noncomputable def verifiedFanLabelPackingPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedTwoWindowCyclePrefix ctx) :
    VerifiedFanLabelPackingPrefix ctx where
  previous := previous
  degreeBound := fun fan => fan.degree_le_eight
  terminal := fun fan => fan.run_terminal
  trace := fun fan => fan.run_trace

theorem exists_verifiedFanLabelPackingPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedFanLabelPackingPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedTwoWindowCyclePrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedFanLabelPackingPrefix ctx previous⟩

end Erdos64EG.Internal
