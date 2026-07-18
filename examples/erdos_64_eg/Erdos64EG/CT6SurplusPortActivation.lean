import Erdos64EG.CT12SparseEnvelope
import StructuralExhaustion.Graph.SurplusPortActivation

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT6: surplus-port activation

This is the problem-specific instantiation of the framework activation used at
manuscript nodes `[127]`--`[128]`.  It consumes the same selected packed graph,
the verified sparse envelope at `[126]`, and the same CT6 surplus residual
retained in that prefix.  Every
surplus slot receives its exact port support, deleted-root-edge return, and
open or triangular response.  Open responses are consequences of suppression
and packed minimality; no response witness is an input to this stage.

The local activation results below do not by themselves prove the node-`[125]`
statement that the graph survives every named sparse exit.  The separate
`SparsePressureActivationRoute` module preserves the literal node-`[125]`
scale residual through node `[126]`; the sparse-exit-survival producer remains
an obligation of node `[125]`.
-/

/-- The framework hypotheses specialized to the Erdős--Gyárfás target. -/
def surplusPortActivationSetup
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.SurplusPortActivation.Setup packedStaticInput ctx where
  minimumDegree_eq_three := rfl
  fourFree := Graph.HighCenterStructure.fourFree_of_targetAvoiding
    (fixedPackedInput ctx) ctx.G.object powerOfTwoLength_four
    (packedStaticInput.fixedContext ctx).avoids

abbrev ActiveSurplusSlot
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.SurplusPortActivation.Slot (surplusPortActivationSetup ctx)

abbrev ActiveSurplusDemand
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (slot : ActiveSurplusSlot ctx) :=
  Graph.SurplusPortActivation.ActiveDemand
    (surplusPortActivationSetup ctx) slot

/-- Unconditional framework execution of the complete activation block. -/
noncomputable def activatedSurplusStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.SurplusPortActivation.VerifiedActivatedStage packedStaticInput ctx
      (surplusPortActivationSetup ctx) :=
  Graph.SurplusPortActivation.verifiedActivatedStageFromMinimality
    packedStaticInput ctx (surplusPortActivationSetup ctx)

/-- Every selected excess slot carries a verified active demand. -/
noncomputable def activeSurplusDemand
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (slot : ActiveSurplusSlot ctx) : ActiveSurplusDemand ctx slot :=
  (activatedSurplusStage ctx).demand slot

/-- The activated family is the actual CT6 schedule, with cardinality equal
to the exact degree-surplus residual on the selected graph. -/
theorem activatedSurplusSchedule_length_eq_sigma
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (Graph.SurplusPortActivation.activatedSchedule
      (surplusPortActivationSetup ctx)
      (activatedSurplusStage ctx).run.residual).length =
        (ctx.G.object.input.vertices.orderedValues.map
          (fun center => ctx.G.object.degree center - 3)).sum := by
  rw [(activatedSurplusStage ctx).scheduleLength]
  rw [(activatedSurplusStage ctx).run_eq]
  exact Graph.SurplusPortActivity.run_total_eq_surplus
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    (surplusPortActivationSetup ctx).deletionCritical

/-- The actual node-[128] slot/path ledger is cubic.  It reads only the
selected surplus-slot schedule and the simple path certificates already
carried by each active demand. -/
theorem activatedSurplusWork_le_cubic
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (activatedSurplusStage ctx).activationChecks ≤
      ctx.G.object.input.vertices.card ^ 2 *
        (2 * ctx.G.object.input.vertices.card + 1) :=
  (activatedSurplusStage ctx).activationChecks_le_cubic

/-- In the open branch, the framework predecessor-accepted response has the
exact Mersenne length asserted in the manuscript. -/
theorem openResponse_has_mersenne_length
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (slot : ActiveSurplusSlot ctx)
    (isOpen : Graph.SurplusPortActivity.portType ctx.G.object
      (surplusPortActivationSetup ctx).deletionCritical slot = .open)
    (response : Graph.SurplusPortActivation.OpenResponse
      (surplusPortActivationSetup ctx) slot isOpen) :
    ∃ exponent : Nat, 2 ≤ exponent ∧
      response.path.length = 2 ^ exponent - 1 := by
  obtain ⟨exponent, lower, successorLength⟩ :=
    (powerOfTwoLength_iff (response.path.length + 1)).mp
      response.predecessorAccepted
  refine ⟨exponent, lower, ?_⟩
  omega

/-- Verified local activation prefix through nodes `[127]`--`[128]`, assuming
the exact node-`[126]` sparse-envelope prefix. -/
structure VerifiedSurplusPortActivationPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedSparseEnvelopePrefix ctx
  activated : ∀ slot : ActiveSurplusSlot ctx,
    Nonempty (ActiveSurplusDemand ctx slot)
  scheduleLength :
    (Graph.SurplusPortActivation.activatedSchedule
      (surplusPortActivationSetup ctx)
      (activatedSurplusStage ctx).run.residual).length =
        (ctx.G.object.input.vertices.orderedValues.map
          (fun center => ctx.G.object.degree center - 3)).sum
  work : (activatedSurplusStage ctx).activationChecks ≤
      ctx.G.object.input.vertices.card ^ 2 *
        (2 * ctx.G.object.input.vertices.card + 1)

noncomputable def verifiedSurplusPortActivationPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSparseEnvelopePrefix ctx) :
    VerifiedSurplusPortActivationPrefix ctx where
  previous := previous
  activated := fun slot ↦ ⟨activeSurplusDemand ctx slot⟩
  scheduleLength := activatedSurplusSchedule_length_eq_sigma ctx
  work := activatedSurplusWork_le_cubic ctx

theorem exists_verifiedSurplusPortActivationPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedSurplusPortActivationPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedSparseEnvelopePrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedSurplusPortActivationPrefix ctx previous⟩

end Erdos64EG.Internal
