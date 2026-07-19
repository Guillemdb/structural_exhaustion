import StructuralExhaustion.CT15.CertifiedDeterminationRank
import StructuralExhaustion.Core.SupportStratifiedDetermination

namespace StructuralExhaustion.CT15.SupportStratifiedRank

open StructuralExhaustion

universe uCoordinate uSupport uContext uBoundary uRepresentative

/-!
# CT15 rank over support-stratified determination certificates

This adapter makes the candidate inspected by CT15 the complete determination
certificate.  A strict rank loss therefore retains the original atom, final
carrier, their distinct context universes, the quotient proposal, and the
representative.  Later routing never has to reconstruct or silently widen any
of those data.
-/

variable (supportProfile :
  Core.SupportStratifiedDetermination.Profile.{uCoordinate, uSupport,
    uContext, uBoundary, uRepresentative})

/-- A raw functional quotient proposal together with a support-stratified
certificate for every nontrivial collision it creates.  This is the exact
proof-carrying candidate universe over which target rank is computed. -/
structure Candidate where
  quotientCode : supportProfile.Coordinate → Nat
  carrier : supportProfile.Support
  certify : ∀ (basisCoordinate determined : supportProfile.Coordinate),
    basisCoordinate ≠ determined →
    quotientCode basisCoordinate = quotientCode determined →
      supportProfile.Certificate
  certify_code : ∀ basisCoordinate determined distinct identified,
    (certify basisCoordinate determined distinct identified).quotientCode =
      quotientCode
  certify_basis : ∀ basisCoordinate determined distinct identified,
    (certify basisCoordinate determined distinct identified).basisCoordinate =
      basisCoordinate
  certify_determined : ∀ basisCoordinate determined distinct identified,
    (certify basisCoordinate determined distinct identified).determined =
      determined
  certify_carrier : ∀ basisCoordinate determined distinct identified,
    (certify basisCoordinate determined distinct identified).carrier = carrier

/-- The quotient code is the only certificate field visible to the generic
rank computation. -/
@[reducible] def system : CertifiedDeterminationRank.System where
  Coordinate := supportProfile.Coordinate
  Candidate := Candidate supportProfile
  code := fun candidate => candidate.quotientCode

/-- Rank profile generated from a support-aware certificate family and the
declared coordinate enumeration. -/
def profile (coordinates : FinEnum supportProfile.Coordinate) :
    CertifiedDeterminationRank.Profile (system supportProfile) where
  coordinates := coordinates

namespace Profile

variable {supportProfile :
  Core.SupportStratifiedDetermination.Profile.{uCoordinate, uSupport,
    uContext, uBoundary, uRepresentative}}
variable (rankProfile : CertifiedDeterminationRank.Profile (system supportProfile))

/-- The exact support-aware certificate retained by a rank-drop circuit. -/
def certificate (circuit : rankProfile.PairCircuit) : supportProfile.Certificate :=
  circuit.candidate.certify circuit.basisCoordinate circuit.determined
    circuit.distinct circuit.identified

theorem certificate_identifies (circuit : rankProfile.PairCircuit) :
    (certificate rankProfile circuit).quotientCode circuit.basisCoordinate =
      (certificate rankProfile circuit).quotientCode circuit.determined := by
  unfold certificate
  rw [circuit.candidate.certify_code circuit.basisCoordinate
    circuit.determined circuit.distinct circuit.identified]
  exact circuit.identified

theorem certificate_coordinates (circuit : rankProfile.PairCircuit) :
    (certificate rankProfile circuit).basisCoordinate = circuit.basisCoordinate ∧
      (certificate rankProfile circuit).determined = circuit.determined := by
  /- Candidate certification requires the rank circuit to use the two
  coordinates named by the certificate.  This equality is deliberately not
  derivable from the quotient code alone and is therefore supplied by the
  proof-carrying candidate family. -/
  exact ⟨circuit.candidate.certify_basis _ _ _ _,
    circuit.candidate.certify_determined _ _ _ _⟩

/-- Route the same certificate selected by CT15 through the original-context
audit and support-location split. -/
noncomputable def route (circuit : rankProfile.PairCircuit) :
    (certificate rankProfile circuit).Routed :=
  (certificate rankProfile circuit).route

end Profile

end StructuralExhaustion.CT15.SupportStratifiedRank
