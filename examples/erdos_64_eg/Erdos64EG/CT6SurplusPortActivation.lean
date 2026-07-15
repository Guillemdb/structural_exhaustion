import Erdos64EG.CT12SparseEnvelope
import StructuralExhaustion.Graph.SurplusPortActivation

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT6: full surplus-port activation

This is the problem-specific instantiation of the framework activation at
manuscript nodes `[127]`--`[128]`.  It consumes the same selected packed graph,
the verified sparse envelope at `[126]`, and the same CT6 surplus residual
retained in that prefix.  Every
surplus slot receives its exact port support, deleted-root-edge return, and
open or triangular response.  Open responses are consequences of suppression
and packed minimality; no response witness is an input to this stage.
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

/-- Exact verified prefix through the full `[125]`--`[128]` CT block. -/
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

noncomputable def verifiedSurplusPortActivationPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSparseEnvelopePrefix ctx) :
    VerifiedSurplusPortActivationPrefix ctx where
  previous := previous
  activated := fun slot ↦ ⟨activeSurplusDemand ctx slot⟩
  scheduleLength := activatedSurplusSchedule_length_eq_sigma ctx

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
