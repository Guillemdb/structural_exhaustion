import Erdos64EG.CT14DegreeFourTypeBLedger
import Erdos64EG.CT14TypeBPostLedger

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact degree-four B1/B2 routing

This is the executable branch interface for diagram nodes `[81]`--`[83]`.
It consumes the literal degree-four and assigned-certificate output of node
`[80]`.  A missing certificate cannot be replaced later: it is proved to be
an unresolved center.  Otherwise the finite local-entry resolution and CT12
completion return exactly one of a nonnegative assigned ledger, a remaining
negative core, or a minimal overlap obstruction.

The scan is over the actual high-center schedule and the actual candidate
fibres.  No graph family, subset family, or product of local choices is
materialized.
-/

namespace TypeBSupportScope

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (scope : TypeBSupportScope ctx)

/-- The successful node-[82] branch, retaining the exact CT12 choice and its
literal nonnegative graph charge. -/
structure B2Nonnegative (noHigher : scope.NoHigherCenter) : Type u where
  resolution : scope.FullResolution
  choice : (scope.assignedSupport resolution).completionProfile.FullChoice
  nonnegative :
    0 ≤ (scope.assignedSupport resolution).assignedChargeProfile.netQuarterCharge

/-- The explicit residual left by the node-[82] statement's phrase
"outside route 8".  It is a negative charge on the literal remaining core,
not a Boolean flag or an assumed future closure. -/
structure B2RemainingNegative (noHigher : scope.NoHigherCenter) : Type u where
  resolution : scope.FullResolution
  choice : (scope.assignedSupport resolution).completionProfile.FullChoice
  negative : (scope.assignedSupport resolution).remainingQuarterCharge choice < 0

/-- The node-[83] output with its proof-carrying minimal CT12 obstruction. -/
structure B2MinimalOverlap (noHigher : scope.NoHigherCenter) : Type u where
  resolution : scope.FullResolution
  obstruction : (scope.assignedSupport resolution).MinimalOverlap

/-- Complete outcome type for nodes `[81]`--`[83]`.  The unresolved branch is
the exact negative local-entry residual routed to the later fan-mass ledger;
the other three constructors are the exhaustive B2 outcomes. -/
inductive DegreeFourB2Route (noHigher : scope.NoHigherCenter) : Prop
  | unresolved (residual : scope.UnresolvedCenter)
  | nonnegative (result : scope.B2Nonnegative noHigher)
  | remainingNegative (result : scope.B2RemainingNegative noHigher)
  | minimalOverlap (result : scope.B2MinimalOverlap noHigher)

/-- Literal node-[80] no-certificate data feeds the unresolved constructor;
there is no intervening author hypothesis. -/
theorem certificateResidual_is_unresolved
    (noHigher : scope.NoHigherCenter) (center : scope.Center)
    (residual : scope.FanCertificateResidualCenter noHigher center) :
    scope.UnresolvedCenter := by
  apply scope.unresolved_of_certificate_none center
  apply (scope.certificateAt_eq_none_iff center).2
  exact residual.assignedMarkedFan_eq_none

/-- Every resolved entry uses exactly the certificate assigned at node `[80]`
and is one of the two manuscript local ledgers. -/
theorem fullResolution_entry_provenance (resolution : scope.FullResolution)
    (center : scope.Center) :
    let entry := (resolution.witness center).1
    (Nonempty (CertificateClosedMarkedFan ctx) ∨
      Nonempty (PositiveDeficitMarkedFan ctx)) ∧
      ∃ certificate : scope.CertificateAt center,
        scope.certificateAt center = some certificate ∧
          entry.fan = certificate.1 := by
  let entry := (resolution.witness center).1
  have provenance := (resolution.witness center).2.2.2.2
  refine ⟨?_, provenance⟩
  cases entry with
  | certificate marked => exact Or.inl ⟨marked⟩
  | positive positive => exact Or.inr ⟨positive⟩

/-- Exact total routing through nodes `[81]`--`[83]`. -/
theorem degreeFourB2Route (noHigher : scope.NoHigherCenter) :
    scope.DegreeFourB2Route noHigher := by
  rcases scope.unresolved_or_fullChoice_or_minimalOverlap with
    unresolved | resolved
  · exact .unresolved unresolved
  · rcases resolved with ⟨resolution, choiceOrOverlap⟩
    rcases choiceOrOverlap with choice | overlap
    · let selected := Classical.choice choice
      rcases (scope.assignedSupport resolution).netQuarterCharge_nonnegative_or_remaining_negative
          selected with nonnegative | negative
      · exact .nonnegative ⟨resolution, selected, nonnegative⟩
      · exact .remainingNegative ⟨resolution, selected, negative⟩
    · exact .minimalOverlap ⟨resolution, Classical.choice overlap⟩

/-- The full-choice side of node `[81]` proves node `[82]` exactly: either
the assigned charge is nonnegative or the literal remaining core is the
route-8 residual. -/
theorem fullChoice_nonnegative_or_remainingNegative
    (resolution : scope.FullResolution)
    (choice : (scope.assignedSupport resolution).completionProfile.FullChoice) :
    0 ≤ (scope.assignedSupport resolution).assignedChargeProfile.netQuarterCharge ∨
      (scope.assignedSupport resolution).remainingQuarterCharge choice < 0 :=
  (scope.assignedSupport resolution).netQuarterCharge_nonnegative_or_remaining_negative
    choice

end TypeBSupportScope

/-- Verified, predecessor-linked endpoint for diagram nodes `[81]`--`[83]`. -/
structure VerifiedDegreeFourB2RoutingPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedDegreeFourTypeBLedgerPrefix ctx
  route : ∀ (scope : TypeBSupportScope ctx)
    (noHigher : scope.NoHigherCenter),
      scope.DegreeFourB2Route noHigher
  certificateFailure : ∀ (scope : TypeBSupportScope ctx)
    (noHigher : scope.NoHigherCenter) (center : scope.Center),
      scope.FanCertificateResidualCenter noHigher center →
        scope.UnresolvedCenter

noncomputable def verifiedDegreeFourB2RoutingPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedDegreeFourTypeBLedgerPrefix ctx) :
    VerifiedDegreeFourB2RoutingPrefix ctx where
  previous := previous
  route := fun scope noHigher => scope.degreeFourB2Route noHigher
  certificateFailure := fun scope noHigher center residual =>
    scope.certificateResidual_is_unresolved noHigher center residual

theorem exists_verifiedDegreeFourB2RoutingPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedDegreeFourB2RoutingPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedDegreeFourTypeBLedgerPrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedDegreeFourB2RoutingPrefix ctx previous⟩

end Erdos64EG.Internal
