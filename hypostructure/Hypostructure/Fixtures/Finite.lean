import Hypostructure.Core.Finite.Accounting

/-!
# Finite enumeration and search fixtures

These fixtures use small explicit schedules so every branch and work count is
kernel-reducible.  They intentionally avoid any Graph or PDE specialization.
-/

namespace Hypostructure.Fixtures.Finite

open Hypostructure.Core
open Hypostructure.Core.Finite

def fourNaturals : Enumeration Nat :=
  Enumeration.ofNodupList [1, 2, 3, 4] (by decide)

def equalsThree (value : Nat) : Prop :=
  value = 3

def equalsThreeDecidable (value : Nat) : Decidable (equalsThree value) :=
  by
    unfold equalsThree
    infer_instance

def hitExecution : Search.Execution fourNaturals equalsThree :=
  Search.run fourNaturals equalsThree equalsThreeDecidable

theorem hit_index_exact : hitExecution.index? = some 2 := by
  decide

theorem hit_value_exact : hitExecution.value? = some 3 := by
  decide

theorem hit_value_sound : 3 ∈ fourNaturals.values ∧ equalsThree 3 :=
  Search.value_sound fourNaturals equalsThree equalsThreeDecidable
    hit_value_exact

theorem hit_route_preserves_execution :
    (Search.route hitExecution).previous = hitExecution :=
  Search.route_previous hitExecution

def greaterThanTen (value : Nat) : Prop :=
  10 < value

def greaterThanTenDecidable (value : Nat) :
    Decidable (greaterThanTen value) :=
  by
    unfold greaterThanTen
    infer_instance

def missExecution : Search.Execution fourNaturals greaterThanTen :=
  Search.run fourNaturals greaterThanTen greaterThanTenDecidable

theorem miss_exact : missExecution.hit? = none := by
  decide

theorem miss_avoids_every_index :
    Search.Avoids fourNaturals greaterThanTen :=
  missExecution.exhaustive miss_exact

theorem miss_avoids_every_member :
    forall value, value ∈ fourNaturals.values -> Not (greaterThanTen value) :=
  (Search.hit?_eq_none_iff fourNaturals greaterThanTen
    greaterThanTenDecidable).mp miss_exact

def booleans : Enumeration Bool :=
  Enumeration.ofNodupList [false, true] (by decide)

def threeNaturals : Enumeration Nat :=
  Enumeration.ofNodupList [0, 1, 2] (by decide)

def productSchedule : Enumeration (Bool × Nat) :=
  booleans.product threeNaturals

theorem product_order_exact : productSchedule.values =
    [(false, 0), (false, 1), (false, 2),
      (true, 0), (true, 1), (true, 2)] := by
  rfl

theorem product_card_exact : productSchedule.card = 6 := by
  decide

def productPredicate (value : Bool × Nat) : Prop :=
  value = (true, 1)

def productPredicateDecidable (value : Bool × Nat) :
    Decidable (productPredicate value) :=
  by
    unfold productPredicate
    infer_instance

def productExecution : Search.Execution productSchedule productPredicate :=
  Search.run productSchedule productPredicate productPredicateDecidable

theorem product_first_index : productExecution.index? = some 4 := by
  decide

def evenPredicate (value : Nat) : Prop :=
  value % 2 = 0

def evenPredicateDecidable (value : Nat) : Decidable (evenPredicate value) :=
  by
    unfold evenPredicate
    infer_instance

def evenSchedule : Enumeration {value // evenPredicate value} :=
  fourNaturals.subtype evenPredicate evenPredicateDecidable

theorem subtype_values_exact :
    evenSchedule.values.map Subtype.val = [2, 4] := by
  decide

theorem subtype_members_are_original
    (value : {value // evenPredicate value})
    (member : value ∈ evenSchedule.values) : value.1 ∈ fourNaturals.values :=
  (Enumeration.mem_subtype_values fourNaturals evenPredicate
    evenPredicateDecidable value).mp member

def subtypePredicate (value : {value // evenPredicate value}) : Prop :=
  value.1 = 4

def subtypePredicateDecidable
    (value : {value // evenPredicate value}) :
    Decidable (subtypePredicate value) :=
  by
    unfold subtypePredicate
    infer_instance

def subtypeExecution : Search.Execution evenSchedule subtypePredicate :=
  Search.run evenSchedule subtypePredicate subtypePredicateDecidable

theorem subtype_first_index : subtypeExecution.index? = some 1 := by
  decide

def Fibre : Bool -> Type
  | false => Fin 2
  | true => Fin 3

def fibreSchedule : (index : Bool) -> Enumeration (Fibre index)
  | false => by
      change Enumeration (Fin 2)
      exact Enumeration.ofNodupList [0, 1] (by decide)
  | true => by
      change Enumeration (Fin 3)
      exact Enumeration.ofNodupList [0, 1, 2] (by decide)

def dependentSchedule : DependentEnumeration Bool Fibre where
  indices := booleans
  fibres := fibreSchedule

theorem dependent_card_exact : dependentSchedule.flatten.card = 5 := by
  decide

def dependentPredicate : (index : Bool) -> Fibre index -> Prop
  | false, _value => False
  | true, value => value = (2 : Fin 3)

def dependentPredicateDecidable :
    (index : Bool) -> (value : Fibre index) ->
      Decidable (dependentPredicate index value)
  | false, _value => by
      simp only [dependentPredicate]
      infer_instance
  | true, value => by
      change Decidable (value = (2 : Fin 3))
      exact if equalValue : value.val = 2 then
        isTrue (Fin.ext equalValue)
      else
        isFalse (fun equal => equalValue (congrArg Fin.val equal))

def dependentExecution :=
  Search.runDependent dependentSchedule dependentPredicate
    dependentPredicateDecidable

theorem dependent_first_index : dependentExecution.index? = some 4 := by
  decide

theorem exact_hit_checks :
    Accounting.executionChecks hitExecution = 3 := by
  decide

theorem exact_miss_checks :
    Accounting.executionChecks missExecution = 4 := by
  decide

theorem exact_product_checks :
    Accounting.executionChecks productExecution = 5 := by
  decide

theorem count_even_exact :
    Accounting.countWhere fourNaturals evenPredicate
      evenPredicateDecidable = 2 := by
  decide

theorem hit_work_is_bounded :
    (Accounting.firstHitWorkBudget fourNaturals equalsThree).checks
        hitExecution <=
      (Accounting.firstHitWorkBudget fourNaturals equalsThree).coefficient *
        ((Accounting.firstHitWorkBudget fourNaturals equalsThree).size
          hitExecution + 1) ^
          (Accounting.firstHitWorkBudget fourNaturals equalsThree).degree :=
  (Accounting.firstHitWorkBudget fourNaturals equalsThree).bounded hitExecution

theorem dependent_work_total :
    dependentSchedule.flatten.card =
      (dependentSchedule.indices.values.map fun index =>
        (dependentSchedule.fibres index).card).sum :=
  Accounting.dependent_exhaustive_checks dependentSchedule

#print axioms hit_index_exact
#print axioms hit_value_sound
#print axioms hit_route_preserves_execution
#print axioms miss_avoids_every_index
#print axioms miss_avoids_every_member
#print axioms product_order_exact
#print axioms product_first_index
#print axioms subtype_values_exact
#print axioms subtype_members_are_original
#print axioms dependent_first_index
#print axioms exact_hit_checks
#print axioms exact_miss_checks
#print axioms count_even_exact
#print axioms hit_work_is_bounded
#print axioms dependent_work_total

end Hypostructure.Fixtures.Finite
