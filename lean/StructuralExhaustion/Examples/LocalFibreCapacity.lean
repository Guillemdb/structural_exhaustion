import StructuralExhaustion.Core.LocalFibreCapacity

namespace StructuralExhaustion.Examples.LocalFibreCapacity

open StructuralExhaustion.Core.LocalFibreCapacity

def fixture : Profile (Fin 4) Bool where
  items := [0, 1, 2, 3]
  itemsNodup := by decide
  owners := [false, true]
  ownersNodup := by decide
  owner item := item.val % 2 = 1
  sameOwner left right := decide (left = right)
  sameOwner_true := by decide
  owner_mem := by decide

example : fixture.items.length ≤ 2 * fixture.owners.length := by
  apply fixture.items_length_le_mul_owners_length 2
  intro owner ownerMember
  fin_cases owner <;> decide

end StructuralExhaustion.Examples.LocalFibreCapacity
