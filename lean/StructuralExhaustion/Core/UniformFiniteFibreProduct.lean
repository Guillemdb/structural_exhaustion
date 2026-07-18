import StructuralExhaustion.Core.Enumeration
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic

namespace StructuralExhaustion.Core.UniformFiniteFibreProduct

universe uCoordinate uIndex uValue

/-!
# Products over uniformly repeated finite fibres

This lemma turns an exact multiplicity ledger into the corresponding product
identity.  It reasons only about the supplied coordinate list and the exact
finite index enumeration; it does not enumerate a Cartesian product.
-/

/-- If every member of an exactly enumerated finite index type occurs exactly
`multiplicity` times in the owner list, then multiplying an index weight over
the owner list is the product of all index weights raised to that
multiplicity. -/
theorem mapped_prod_eq_finEnum_prod_pow
    {Coordinate : Type uCoordinate} {Index : Type uIndex}
    {Value : Type uValue} [BEq Index] [LawfulBEq Index] [CommMonoid Value]
    (coordinates : Core.OrderedCollection Coordinate)
    (indices : FinEnum Index)
    (owner : Coordinate → Index)
    (weight : Index → Value)
    (multiplicity : Nat)
    (countExact : ∀ index,
      (coordinates.values.map owner).count index = multiplicity) :
    (coordinates.values.map (fun coordinate => weight (owner coordinate))).prod =
      (indices.orderedValues.map weight).prod ^ multiplicity := by
  let expanded : List Index :=
    (List.replicate multiplicity indices.orderedValues).flatten
  have expandedCount : ∀ index, expanded.count index = multiplicity := by
    intro index
    have countOne : indices.orderedValues.count index = 1 :=
      List.count_eq_one_of_mem indices.nodup_orderedValues
        (indices.mem_orderedValues index)
    have repeatedCount : ∀ copies : Nat,
        ((List.replicate copies indices.orderedValues).flatten).count index =
          copies := by
      intro copies
      induction copies with
      | zero => simp
      | succ copies ih => simp [List.replicate_succ, countOne, ih, Nat.add_comm]
    simpa [expanded] using repeatedCount multiplicity
  have ownersPerm : List.Perm (coordinates.values.map owner) expanded :=
    List.perm_iff_count.mpr fun index => (countExact index).trans (expandedCount index).symm
  have weightedPerm :
      List.Perm
        (coordinates.values.map (fun coordinate => weight (owner coordinate)))
        (expanded.map weight) := by
    simpa [List.map_map, Function.comp_def] using ownersPerm.map weight
  calc
    (coordinates.values.map (fun coordinate => weight (owner coordinate))).prod =
        (expanded.map weight).prod := weightedPerm.prod_eq
    _ = (indices.orderedValues.map weight).prod ^ multiplicity := by
      simp [expanded, List.prod_replicate]

end StructuralExhaustion.Core.UniformFiniteFibreProduct
