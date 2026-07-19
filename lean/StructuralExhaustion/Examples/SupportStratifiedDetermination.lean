import StructuralExhaustion.Core.SupportStratifiedDetermination

namespace StructuralExhaustion.Examples.SupportStratifiedDetermination

open StructuralExhaustion

inductive Support where
  | atom
  | carrier
deriving DecidableEq

def profile : Core.SupportStratifiedDetermination.Profile where
  Coordinate := Bool
  Support := Support
  Context
    | .atom => Bool
    | .carrier => Unit
  BoundaryProfile := Unit
  Representative := fun _ => Unit
  supportLe left right := left = right ∨ (left = .atom ∧ right = .carrier)
  originalEligible := fun support => support = .atom
  connected := fun _ => True
  carries := fun _ _ => True
  determines support _ _ := support = .carrier
  boundaryProfile := fun _ => ()
  response support coordinate context :=
    match support with
    | .atom => coordinate != context
    | .carrier => true

def enlargedCertificate : profile.Certificate where
  original := .atom
  carrier := .carrier
  original_eligible := rfl
  original_le_carrier := Or.inr ⟨rfl, rfl⟩
  carrier_connected := trivial
  determined := true
  basisCoordinate := false
  distinct := by simp
  original_carries_determined := trivial
  original_carries_basis := trivial
  carrier_carries_determined := trivial
  carrier_carries_basis := trivial
  carrier_determines := rfl
  quotientCode := fun _ => 0
  identified := rfl
  carrierBoundary := ()
  carrierBoundary_eq := rfl
  originalBoundary := ()
  originalBoundary_eq := rfl
  originalQuotientCode := fun _ => 0
  quotientRestriction := rfl
  originalIdentified := rfl
  carrierUniversal := by intro context; cases context; rfl
  representative := ()
  minimal := by
    intro support _ determines _support_le
    cases support with
    | atom => cases determines
    | carrier => exact Or.inl rfl

/-- Carrier-level universality does not collapse the smaller atom's context
audit: the fixture takes the concrete defect branch. -/
theorem enlargedCertificate_routes_defect :
    ∃ context : profile.Context enlargedCertificate.original,
      profile.response enlargedCertificate.original
          enlargedCertificate.basisCoordinate context ≠
        profile.response enlargedCertificate.original
          enlargedCertificate.determined context := by
  exact ⟨false, by decide⟩

theorem enlargedCertificate_work :
    enlargedCertificate.routeBudget.checks () ≤
      enlargedCertificate.routeBudget.coefficient *
        (enlargedCertificate.routeBudget.size () + 1) ^
          enlargedCertificate.routeBudget.degree :=
  enlargedCertificate.route_polynomial

end StructuralExhaustion.Examples.SupportStratifiedDetermination
