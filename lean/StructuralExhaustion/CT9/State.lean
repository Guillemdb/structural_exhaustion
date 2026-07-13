import StructuralExhaustion.CT9.Capability

namespace StructuralExhaustion.CT9

universe uAmbient uBranch uItem uLabel

variable {P : Core.Problem.{uAmbient, uBranch}}
variable (capability : Capability.{uAmbient, uBranch, uItem, uLabel} P)
variable (input : Input capability)

/-- First exact label whose fibre exceeds its declared capacity. -/
structure OverloadResidual where
  label : capability.Label
  overloaded : capability.capacity label < fibreCount capability input label

/-- Two distinct active items in one exact label fibre. -/
structure SameLabelPair (label : capability.Label) where
  first : capability.Item
  second : capability.Item
  first_mem : first ∈ input.items.values
  second_mem : second ∈ input.items.values
  distinct : first ≠ second
  first_label : capability.label first = label
  second_label : capability.label second = label

namespace SameLabelPair

theorem labels_eq {label : capability.Label}
    (pair : SameLabelPair capability input label) :
    capability.label pair.first = capability.label pair.second :=
  pair.first_label.trans pair.second_label.symm

end SameLabelPair

/-- Complete bounded-multiplicity certificate over the exact label universe. -/
structure BoundedCertificate : Prop where
  bounded : ∀ label : capability.Label,
    fibreCount capability input label ≤ capability.capacity label

end StructuralExhaustion.CT9
