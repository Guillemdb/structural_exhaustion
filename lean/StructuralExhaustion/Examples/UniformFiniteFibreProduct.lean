import StructuralExhaustion.Core.UniformFiniteFibreProduct

namespace StructuralExhaustion.Examples.UniformFiniteFibreProduct

open StructuralExhaustion.Core

def coordinates : OrderedCollection (Fin 4) where
  values := [0, 1, 2, 3]
  nodup := by decide
  decEq := inferInstance

def owner (coordinate : Fin 4) : Bool := coordinate.1 % 2 = 1

def weight : Bool → Nat
  | false => 2
  | true => 3

theorem owner_count_exact : ∀ index,
    (coordinates.values.map owner).count index = 2 := by
  intro index
  cases index <;> decide

/-- Two owners, each occurring twice, contribute `(2 * 3)^2`. -/
example :
    (coordinates.values.map (fun coordinate => weight (owner coordinate))).prod =
      (Core.Enumeration.bool.orderedValues.map weight).prod ^ 2 := by
  exact Core.UniformFiniteFibreProduct.mapped_prod_eq_finEnum_prod_pow
    coordinates Core.Enumeration.bool owner weight 2 owner_count_exact

end StructuralExhaustion.Examples.UniformFiniteFibreProduct
