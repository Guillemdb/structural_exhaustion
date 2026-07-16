import StructuralExhaustion.Core.LocalBinaryMajority

namespace StructuralExhaustion.Examples.LocalBinaryMajority

open StructuralExhaustion.Core.LocalBinaryMajority

def entries : List Bool := [true, false, true, true, false]

def result : Outcome entries (fun entry => entry = true) 3 :=
  decideOdd entries (fun entry => entry = true) 2 (by native_decide)

theorem result_is_left :
    ∃ large : 3 ≤ (leftEntries entries
        (fun entry => entry = true)).length,
      result = Outcome.leftMajority large := by
  refine ⟨by native_decide, ?_⟩
  rfl

theorem exact_partition :
    (leftEntries entries (fun entry => entry = true)).length +
        (rightEntries entries (fun entry => entry = true)).length = 5 := by
  native_decide

end StructuralExhaustion.Examples.LocalBinaryMajority
