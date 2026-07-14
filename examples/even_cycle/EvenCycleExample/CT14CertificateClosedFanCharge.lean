import EvenCycleExample.Problem
import StructuralExhaustion.Graph.CertificateClosedFanCharge
import StructuralExhaustion.Graph.CertificateClosedFanCandidate

namespace EvenCycleExample.CertificateClosedFanCharge

open StructuralExhaustion

/-! Non-Erdős transfer of the exact CT14 fan-charge ledger. -/

def profile : Graph.CertificateClosedFanCharge.Profile (Fin 4) where
  members := inferInstance
  Closed := fun _member => False
  closedDecidable := fun _member => inferInstance
  quarterCharge := fun _member => 3
  closedQuarterCharge := by simp
  openQuarterChargeLower := by simp

theorem certificateClosed (context : Core.BranchContext (problem Unit)) :
    4 * profile.closedCount context + profile.members.card ≤ 11 := by
  simp [Graph.CertificateClosedFanCharge.Profile.closedCount,
    CT14.lowerMass, profile,
    Graph.CertificateClosedFanCharge.Profile.capability,
    Graph.CertificateClosedFanCharge.Profile.closedMass]

def run (context : Core.BranchContext (problem Unit)) :=
  profile.run context

theorem terminal (context : Core.BranchContext (problem Unit)) :
    (run context).terminal = .capacity :=
  profile.run_terminal context

theorem charge_nonnegative (context : Core.BranchContext (problem Unit)) :
    0 ≤ profile.neighborhoodQuarterChargeLower context :=
  profile.neighborhoodQuarterChargeLower_nonnegative context
    (certificateClosed context)

def vertex (member : Fin 4) : Fin 5 :=
  ⟨member.val, by omega⟩

def reserve : Graph.CertificateClosedFanCandidate.VertexReserve (Fin 5) where
  Used := fun _vertex => False
  usedDecidable := fun _vertex => inferInstance

def candidateProfile :=
  Graph.CertificateClosedFanCandidate.Profile.selectionProfile profile
    (inferInstance : DecidableEq (Fin 5)) (4 : Fin 5) vertex reserve

noncomputable def candidate (context : Core.BranchContext (problem Unit)) :
    candidateProfile.Candidate :=
  Graph.CertificateClosedFanCandidate.Profile.allItemsCandidate profile
    (inferInstance : DecidableEq (Fin 5)) (4 : Fin 5) vertex reserve context
    (charge_nonnegative context) (by simp [reserve])

theorem candidate_pays (context : Core.BranchContext (problem Unit)) :
    0 ≤ Graph.CertificateClosedFanCandidate.Profile.centerQuarterCharge profile +
      ∑ member ∈ (candidate context).1,
        profile.quarterCharge member :=
  Graph.CertificateClosedFanCandidate.Profile.Candidate.charge_nonnegative
    profile (inferInstance : DecidableEq (Fin 5)) (4 : Fin 5) vertex reserve
    (candidate context)

end EvenCycleExample.CertificateClosedFanCharge
