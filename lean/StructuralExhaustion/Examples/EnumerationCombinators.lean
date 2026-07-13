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

@[implicit_reducible]
def trueBools : FinEnum {value : Bool // value = true} :=
  Enumeration.subtype bools (fun value => value = true)
    (fun value => Bool.decEq value true)

example : trueBools.orderedValues.map Subtype.val = [true] := rfl

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
