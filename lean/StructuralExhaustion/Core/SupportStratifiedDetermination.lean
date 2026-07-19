import StructuralExhaustion.Core.WorkBudget
import StructuralExhaustion.Core.ZeroWorkBudget

namespace StructuralExhaustion.Core.SupportStratifiedDetermination

universe uCoordinate uSupport uContext uBoundary uRepresentative

/-!
# Determinations evaluated at nested support interfaces

A quotient determination can be valid at its final connected carrier without
already being valid at the smaller atom from which it arose.  This profile
keeps those two context universes distinct.  It also owns the support,
boundary, minimality, quotient-code, and representative plumbing needed by the
standard defect/compression/enlargement trichotomy.
-/

/-- Reusable semantics for coordinates carried by nested supports. -/
structure Profile where
  Coordinate : Type uCoordinate
  Support : Type uSupport
  Context : Support → Type uContext
  BoundaryProfile : Type uBoundary
  Representative : Support → Type uRepresentative
  supportLe : Support → Support → Prop
  originalEligible : Support → Prop
  connected : Support → Prop
  carries : Support → Coordinate → Prop
  determines : Support → Coordinate → Coordinate → Prop
  boundaryProfile : Support → BoundaryProfile
  response : (support : Support) → Coordinate → Context support → Bool

namespace Profile

variable (profile : Profile)

/-- Strict support growth in the manuscript's inclusion order. -/
def SupportLt (left right : profile.Support) : Prop :=
  profile.supportLe left right ∧ left ≠ right

/-- A functional singleton determination with its inclusion-minimal connected
carrier.  `carrierUniversal` is deliberately indexed by `carrier`; it says
nothing about the distinct context type belonging to `original`. -/
structure Certificate where
  original : profile.Support
  carrier : profile.Support
  original_eligible : profile.originalEligible original
  original_le_carrier : profile.supportLe original carrier
  carrier_connected : profile.connected carrier
  determined : profile.Coordinate
  basisCoordinate : profile.Coordinate
  distinct : basisCoordinate ≠ determined
  original_carries_determined : profile.carries original determined
  original_carries_basis : profile.carries original basisCoordinate
  carrier_carries_determined : profile.carries carrier determined
  carrier_carries_basis : profile.carries carrier basisCoordinate
  carrier_determines : profile.determines carrier basisCoordinate determined
  quotientCode : profile.Coordinate → Nat
  identified : quotientCode basisCoordinate = quotientCode determined
  carrierBoundary : profile.BoundaryProfile
  carrierBoundary_eq : carrierBoundary = profile.boundaryProfile carrier
  originalBoundary : profile.BoundaryProfile
  originalBoundary_eq : originalBoundary = profile.boundaryProfile original
  originalQuotientCode : profile.Coordinate → Nat
  quotientRestriction : originalQuotientCode = quotientCode
  originalIdentified :
    originalQuotientCode basisCoordinate = originalQuotientCode determined
  carrierUniversal : ∀ context : profile.Context carrier,
    profile.response carrier basisCoordinate context =
      profile.response carrier determined context
  representative : profile.Representative carrier
  minimal : ∀ support : profile.Support,
    profile.connected support →
    profile.determines support basisCoordinate determined →
    profile.supportLe support carrier →
    profile.supportLe carrier support

namespace Certificate

variable {profile : Profile}

/-- The original atom sees either one concrete distinguishing context or
universal equality in its own context universe. -/
inductive OriginalContextAudit (certificate : profile.Certificate) where
  | defective
      (context : profile.Context certificate.original)
      (mismatch :
        profile.response certificate.original certificate.basisCoordinate context ≠
          profile.response certificate.original certificate.determined context)
  | universal
      (allContexts : ∀ context : profile.Context certificate.original,
        profile.response certificate.original certificate.basisCoordinate context =
          profile.response certificate.original certificate.determined context)

/-- Proof-level exhaustive context audit.  No context collection is
materialized or scanned. -/
noncomputable def auditOriginal (certificate : profile.Certificate) :
    certificate.OriginalContextAudit := by
  classical
  by_cases universal : ∀ context : profile.Context certificate.original,
      profile.response certificate.original certificate.basisCoordinate context =
        profile.response certificate.original certificate.determined context
  · exact .universal universal
  · have existsMismatch : ∃ context : profile.Context certificate.original,
        profile.response certificate.original certificate.basisCoordinate context ≠
          profile.response certificate.original certificate.determined context :=
      Classical.not_forall.mp universal
    let context := Classical.choose existsMismatch
    exact .defective context (Classical.choose_spec existsMismatch)

/-- Exact support-location split after the original-interface audit. -/
inductive Location (certificate : profile.Certificate) where
  | atOriginal (equal : certificate.carrier = certificate.original)
  | enlarged (strict : profile.SupportLt certificate.original certificate.carrier)

/-- Equality of the two support values or strict growth along the already
proved inclusion. -/
noncomputable def location (certificate : profile.Certificate) :
    certificate.Location := by
  classical
  by_cases equal : certificate.carrier = certificate.original
  · exact .atOriginal equal
  · exact .enlarged ⟨certificate.original_le_carrier, fun reverse => equal reverse.symm⟩

/-- Transport the carrier representative only on the literal at-atom edge. -/
def originalRepresentative (certificate : profile.Certificate)
    (equal : certificate.carrier = certificate.original) :
    profile.Representative certificate.original :=
  Eq.mp (congrArg profile.Representative equal) certificate.representative

/-- The three outcomes used throughout the manuscript.  These are existing
mathematical branches, not new diagram cases. -/
inductive Routed (certificate : profile.Certificate) where
  | targetDefect
      (context : profile.Context certificate.original)
      (mismatch :
        profile.response certificate.original certificate.basisCoordinate context ≠
          profile.response certificate.original certificate.determined context)
  | atAtom
      (equal : certificate.carrier = certificate.original)
      (representative : profile.Representative certificate.original)
  | enlarged
      (strict : profile.SupportLt certificate.original certificate.carrier)

/-- Execute the context audit before the support-location split, matching the
manuscript's order. -/
noncomputable def route (certificate : profile.Certificate) :
    certificate.Routed := by
  cases certificate.auditOriginal with
  | defective context mismatch => exact .targetDefect context mismatch
  | universal _ =>
      cases certificate.location with
      | atOriginal equal =>
          exact .atAtom equal (certificate.originalRepresentative equal)
      | enlarged strict => exact .enlarged strict

theorem route_total (certificate : profile.Certificate) :
    Nonempty certificate.Routed :=
  ⟨certificate.route⟩

/-- Routing is proof-only; all inspected mathematical data are already stored
in the certificate. -/
def routeBudget (_certificate : profile.Certificate) :
    PolynomialCheckBudget Unit :=
  PolynomialCheckBudget.zero (fun _ => 1)

theorem route_polynomial (certificate : profile.Certificate) :
    certificate.routeBudget.checks () ≤
      certificate.routeBudget.coefficient *
        (certificate.routeBudget.size () + 1) ^
          certificate.routeBudget.degree :=
  certificate.routeBudget.bounded ()

end Certificate

end Profile

end StructuralExhaustion.Core.SupportStratifiedDetermination
