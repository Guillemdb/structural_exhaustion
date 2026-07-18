import Erdos64EG.SparsePressureEnvelopeRoute
import Erdos64EG.CT6SurplusPortActivation

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Part-X pressure-to-activation connector

This file is a topology-neutral connector on the original edges
`[125] → [126] → [127]`.  It lives after the independent scale/envelope and
activation modules to avoid an import cycle.  It preserves the literal strict
node-`[20]` residual and the identical selected graph.  It deliberately does
not claim that node `[125]` has survived every named sparse exit; that producer
is a separate, currently missing node-[125] obligation.
-/

structure VerifiedSurplusPortActivationFromPressure
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) where
  previous : VerifiedSparseEnvelopeFromPressure ctx
  activation : VerifiedSurplusPortActivationPrefix ctx

noncomputable def verifiedSurplusPortActivationFromPressure
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : SparsePressureEntryResidual ctx) :
    VerifiedSurplusPortActivationFromPressure ctx where
  previous := verifiedSparseEnvelopeFromPressure ctx previous
  activation := verifiedSurplusPortActivationPrefix ctx
    (verifiedSparseEnvelopeFromPressure ctx previous).envelope

theorem verifiedSurplusPortActivationFromPressure_sameEnvelope
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : SparsePressureEntryResidual ctx) :
    (verifiedSurplusPortActivationFromPressure ctx previous).activation.previous =
      (verifiedSurplusPortActivationFromPressure ctx previous).previous.envelope :=
  rfl

theorem verifiedSurplusPortActivationFromPressure_sameNode20
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : SparsePressureEntryResidual ctx) :
    (verifiedSurplusPortActivationFromPressure ctx previous).previous.previous =
      previous :=
  rfl

end Erdos64EG.Internal
