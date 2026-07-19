import StructuralExhaustion.Core.EnumerationCombinators
import StructuralExhaustion.Core.EnumerationArithmetic
import StructuralExhaustion.Core.ListPosition
import StructuralExhaustion.Core.Parity

namespace StructuralExhaustion.Examples.EnumerationCombinators

open Core

@[implicit_reducible]
def bools : FinEnum Bool := Enumeration.bool

example : Enumeration.unit.orderedValues = [()] := rfl

example : Enumeration.bool.orderedValues = [false, true] := rfl

example : (Enumeration.prod bools bools).orderedValues =
    [(false, false), (false, true), (true, false), (true, true)] := rfl

def BoolFibre : Bool → Type
  | false => Fin 1
  | true => Fin 3

@[implicit_reducible]
def boolFibreEnumeration : (value : Bool) → FinEnum (BoolFibre value)
  | false => (inferInstance : FinEnum (Fin 1))
  | true => (inferInstance : FinEnum (Fin 3))

example : (Enumeration.sigma bools boolFibreEnumeration).card = 4 := by
  native_decide

example :
    (Enumeration.sigmaOrderedDistinctPairs bools boolFibreEnumeration).card = 3 := by
  native_decide

example :
    (Enumeration.sigmaOrderedDistinctPairs bools boolFibreEnumeration).card ≤
      bools.card * 3 ^ 2 :=
  Enumeration.sigmaOrderedDistinctPairs_card_le_mul_square
    bools boolFibreEnumeration 3 (by
      intro value
      cases value <;>
        simp [BoolFibre, FinEnum.card_eq_fintypeCard])

@[implicit_reducible]
def trueBools : FinEnum {value : Bool // value = true} :=
  Enumeration.subtype bools (fun value => value = true)
    (fun value => Bool.decEq value true)

example : trueBools.orderedValues.map Subtype.val = [true] := rfl

example : trueBools.card = 1 := by
  rw [trueBools, Enumeration.subtype_card_eq_filter]
  decide

example : Nat.card Bool = bools.card :=
  Enumeration.natCard_eq bools

example : ({true} : Finset Bool).card ≤ bools.card :=
  Enumeration.finset_card_le bools {true}

example : bools.card ≤ (Enumeration.prod bools bools).card :=
  Enumeration.card_le_of_injective bools (Enumeration.prod bools bools)
    (fun value => (value, false)) (fun _left _right equal =>
      congrArg Prod.fst equal)

example (values : List (Set.powersetCard Bool 1))
    (nodup : values.Nodup) :
    values.length ≤ Nat.choose bools.card 1 :=
  Enumeration.powersetCard_list_length_le bools 1 values nodup

example :
    (Enumeration.finsetSubtype bools ({true} : Finset Bool)).card = 1 := by
  rw [Enumeration.finsetSubtype_card]
  decide

example :
    (@Finset.univ {value // value ∈ ({false, true} : Finset Bool)}
      (@FinEnum.instFintype _
        (Enumeration.finsetSubtype bools {false, true}))).sum
        (fun value => if value.1 then 2 else 1) = 3 := by
  calc
    _ = ({false, true} : Finset Bool).sum
        (fun value => if value then 2 else 1) :=
      Enumeration.finsetSubtype_sum_val_eq bools {false, true} _
    _ = 3 := by decide

example : (Enumeration.distinctPairs (inferInstance : FinEnum (Fin 4))).card = 6 := by
  rw [Enumeration.distinctPairs_card]
  decide

example : (Enumeration.distinctPairs (inferInstance : FinEnum (Fin 4))).card ≤
    (inferInstance : FinEnum (Fin 4)).card ^ 2 :=
  Enumeration.distinctPairs_card_le_square _

example (value : {value : Bool // value = true}) : value ∈ trueBools.orderedValues :=
  trueBools.mem_orderedValues value

@[implicit_reducible]
def boolListsUpToTwo : FinEnum (BoundedList Bool 2) :=
  Enumeration.boundedList bools 2

example : boolListsUpToTwo.orderedValues.map Subtype.val =
    [[], [false], [false, false], [false, true],
      [true], [true, false], [true, true]] := rfl

example (xs : BoundedList Bool 2) : xs ∈ boolListsUpToTwo.orderedValues :=
  boolListsUpToTwo.mem_orderedValues xs

example : boolListsUpToTwo.orderedValues.Nodup :=
  boolListsUpToTwo.nodup_orderedValues

example : [false].length ≤ Fintype.card Bool :=
  List.Nodup.length_le_card (by decide)

example : (bools.orderedValues.map fun value => if value then 4 else 6).sum + 1 + 2 =
    (bools.orderedValues.map fun value => if value then 5 else 8).sum := by
  apply Enumeration.sum_map_add_two_updates bools true false (by decide)
  · rfl
  · rfl
  · intro value notTrue notFalse
    cases value <;> simp_all

example : [true, false].length ≤ bools.orderedValues.length :=
  Enumeration.length_le_elems_of_nodup bools (by decide)

def reversedBools : BoundedList Bool bools.orderedValues.length :=
  Enumeration.boundedListOfNodup bools [true, false] (by decide)

example : reversedBools.1 = [true, false] := rfl

example : Enumeration.empty.orderedValues = [] := rfl

def everyBoolClassifiedDecidable :
    Decidable (∀ value : Bool, value = false ∨ value = true) :=
  Enumeration.forallDecidable bools
    (fun value => value = false ∨ value = true) (fun _ => inferInstance)

example :
    @decide (∀ value : Bool, value = false ∨ value = true)
      everyBoolClassifiedDecidable = true :=
  rfl

example : [false, true].idxOf true = 1 := rfl

example : [false, true][[false, true].idxOf true]'(by decide) = true :=
  Core.ListPosition.getElem_idxOf_of_mem (by simp)

def locatedBoolPair :
    Core.ListPosition.LocatedDistinctPair [false, true] false true :=
  Core.ListPosition.locateDistinctPair (by simp) (by simp) (by decide)

example : locatedBoolPair.left = 0 := rfl
example : locatedBoolPair.right = 1 := rfl
example : locatedBoolPair.left ≠ locatedBoolPair.right :=
  locatedBoolPair.positions_distinct

def locatedInDuplicateList :
    Core.ListPosition.LocatedDistinctPair [false, true, false] false true :=
  Core.ListPosition.locateDistinctPair (by simp) (by simp) (by decide)

example : locatedInDuplicateList.left = 0 := rfl
example : locatedInDuplicateList.right = 1 := rfl
example : locatedInDuplicateList.left ≠ locatedInDuplicateList.right :=
  locatedInDuplicateList.positions_distinct

example : Core.Parity.label 4 = Core.Parity.label 8 := rfl

example : 4 % 2 = 8 % 2 :=
  Core.Parity.mod_two_eq_of_label_eq rfl

end StructuralExhaustion.Examples.EnumerationCombinators
