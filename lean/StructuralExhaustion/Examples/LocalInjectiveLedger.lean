import StructuralExhaustion.Core.LocalInjectiveLedger

namespace StructuralExhaustion.Examples.LocalInjectiveLedger

open StructuralExhaustion.Core.LocalInjectiveLedger

def profile : Profile Bool Nat Nat where
  indices := [false, true]
  entries
    | false => [0, 1]
    | true => [2, 3]
  entriesNodup := by
    intro index
    fin_cases index <;> native_decide
  label := fun _ entry => entry
  localInjective := by
    intro index left right _ _ equal
    exact equal
  separated := by
    intro leftIndex rightIndex distinct left right leftMem rightMem equal
    fin_cases leftIndex <;> fin_cases rightIndex <;>
      simp_all <;> omega

theorem labels_exact : profile.labels = [0, 1, 2, 3] := rfl

theorem labels_nodup : profile.labels.Nodup :=
  profile.labels_nodup (by native_decide)

theorem aggregate_lower : 2 * profile.indices.length ≤
    profile.labels.length := by
  apply profile.threshold_mul_indices_le_labels_length 2
  intro index member
  fin_cases index <;> native_decide

end StructuralExhaustion.Examples.LocalInjectiveLedger
