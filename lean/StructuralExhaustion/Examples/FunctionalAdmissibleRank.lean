import StructuralExhaustion.CT15.FunctionalAdmissibleRank

namespace StructuralExhaustion.Examples.FunctionalAdmissibleRankExample

open StructuralExhaustion

open CT15.FunctionalAdmissibleRank

def family : Family where
  Coordinate := Bool
  Carrier := Unit
  Proposal := fun _ ↦ Bool → Nat
  code := fun proposal ↦ proposal
  Admissible := fun _ ↦ True
  Realization := fun _ _ ↦ Unit
  ImageValue := fun _ _ ↦ Nat
  qImage := fun proposal _ coordinate ↦ proposal coordinate
  identifiedImages := by
    intro _carrier proposal left right identified _realization
    exact identified

def profile : Profile family where
  coordinates := Core.Enumeration.bool

def constantProposal : family.Proposal () := fun _ ↦ 0

theorem constantProposal_functional :
    profile.Functional constantProposal :=
  profile.functional_of_identified_images constantProposal

def constantCandidate : profile.Candidate where
  carrier := ()
  proposal := constantProposal
  admissible := trivial
  functional := constantProposal_functional

theorem constantCandidate_determines_true_from_false :
    Profile.Determines constantProposal {false} true :=
  Profile.determines_singleton_of_identified constantProposal rfl

#print axioms constantProposal_functional
#print axioms constantCandidate_determines_true_from_false

end StructuralExhaustion.Examples.FunctionalAdmissibleRankExample
