import Erdos64EG.Future.CT12TypeBOverlapSupport
import Erdos64EG.Future.TypeBSupportScope
import StructuralExhaustion.Core.FiniteResolution

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact resolution split for every high center in a Type B scope

The earlier `TypeBSupportScope` supplies the literal support and its optional
assigned fan certificates.  This later stage asks a different question:
whether every actual center has a certificate-closed or verified positive-B1
local entry.  The common finite-resolution theorem proves the exhaustive
split:

* one actual high center has no such local entry; or
* every actual high center has one, yielding the concrete dependent CT12
  family and therefore a full disjoint choice or a minimal obstruction.

The local-entry predicate is deliberately distinct from assigned-certificate
presence at diagram node `[80]`.
-/

namespace TypeBSupportScope

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (scope : TypeBSupportScope ctx)

/-- Exact later local-entry proposition at one derived center.  The final
clause is the provenance link to node `[80]`: the local B1/B2 datum must use
the very certificate assigned by the preceding finite marking scan. -/
def LocalEntryAt (center : scope.Center) :=
  {entry : TypeBLocalEntry ctx //
    entry.center = center.1 ∧
      (∀ carrier, entry.Assigned carrier ↔ scope.Assigned carrier) ∧
        entry.CoreCompatible scope.coreVertices ∧
          ∃ certificate : scope.CertificateAt center,
            scope.certificateAt center = some certificate ∧
              entry.fan = certificate.1}

noncomputable def resolutionProfile : Core.FiniteResolution.Profile scope.Center where
  Witness := scope.LocalEntryAt
  sites := scope.centers

abbrev FullResolution := scope.resolutionProfile.FullResolution

/-- Absence of a verified local B1/B2 entry.  This is not absence of the
assigned `MarkedFan` field tested at node `[80]`. -/
def UnresolvedCenter : Prop :=
  ∃ center : scope.Center, ¬Nonempty (scope.LocalEntryAt center)

noncomputable def assignedSupport (resolution : scope.FullResolution) :
    TypeBAssignedSupport ctx where
  vertices := scope.coreVertices
  vertices_remainder := scope.coreVertices_subset_remainder
  assignedCarriers := scope.assignedCarriers
  centers := scope.highCenters
  centers_exact := rfl
  entry := fun center => (resolution.witness center).1
  entry_center := fun center => (resolution.witness center).2.1
  entry_assigned := fun center carrier => (resolution.witness center).2.2.1 carrier
  entry_coreCompatible := fun center => (resolution.witness center).2.2.2.1
  baseReserve := scope.reserve

/-- A literal node-[80] certificate failure is automatically an unresolved
node-[81] center.  No replacement certificate can enter through the later
local-entry interface. -/
theorem unresolved_of_certificate_none (center : scope.Center)
    (missing : scope.certificateAt center = none) :
    scope.UnresolvedCenter := by
  refine ⟨center, ?_⟩
  intro resolved
  rcases resolved with ⟨entry⟩
  rcases entry.2.2.2.2 with ⟨certificate, assigned, _sameFan⟩
  rw [missing] at assigned
  simp at assigned

theorem unresolved_or_fullChoice_or_minimalOverlap :
    scope.UnresolvedCenter ∨
      ∃ resolution : scope.FullResolution,
        let assigned := scope.assignedSupport resolution
        Nonempty assigned.completionProfile.FullChoice ∨
          Nonempty assigned.MinimalOverlap := by
  rcases scope.resolutionProfile.fullResolution_or_unresolved with
    resolved | unresolved
  · right
    let resolution := Classical.choice resolved
    refine ⟨resolution, ?_⟩
    let assigned := scope.assignedSupport resolution
    rcases assigned.full_choice_or_minimal_obstruction with choice | obstruction
    · exact Or.inl choice
    · exact Or.inr ⟨⟨obstruction.choose, obstruction.choose_spec.1,
          obstruction.choose_spec.2⟩⟩
  · exact Or.inl unresolved

end TypeBSupportScope

/-- Same-CT12 theorem extension of the exact completion ledger. -/
abbrev VerifiedTypeBResolutionPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.LedgerExtension (VerifiedTypeBOverlapSupportPrefix ctx)
    (fun _previous => ∀ scope : TypeBSupportScope ctx,
      scope.UnresolvedCenter ∨
        ∃ resolution : scope.FullResolution,
          let assigned := scope.assignedSupport resolution
          Nonempty assigned.completionProfile.FullChoice ∨
            Nonempty assigned.MinimalOverlap)

noncomputable def verifiedTypeBResolutionPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedTypeBOverlapSupportPrefix ctx) :
    VerifiedTypeBResolutionPrefix ctx :=
  ⟨previous, fun scope => scope.unresolved_or_fullChoice_or_minimalOverlap⟩

theorem exists_verifiedTypeBResolutionPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedTypeBResolutionPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedTypeBOverlapSupportPrefix object baseline avoids
  exact ⟨ctx, verifiedTypeBResolutionPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
