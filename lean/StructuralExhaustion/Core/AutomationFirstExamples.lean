import StructuralExhaustion.Core.AutomationFirst

namespace StructuralExhaustion.Core.AutomationFirstExamples

open FiniteSearch

@[implicit_reducible]
def bools : FinEnum Bool :=
  Enumeration.bool

def trueSearch : Result (fun value : Bool => value = true) :=
  search bools (fun value => value = true) (fun _ => inferInstance)

#eval trueSearch.value?

example : trueSearch.value? = some true := rfl

def noSearch : Result (fun _ : Bool => False) :=
  search bools (fun _ => False) (fun _ => inferInstance)

#eval noSearch.value?

example : noSearch.value? = none := rfl

def firstTrue : FirstResult bools.orderedValues (fun value : Bool => value = true) :=
  first bools (fun value => value = true) (fun _ => inferInstance)

#eval firstTrue.value?
#eval firstTrue.before?

example : firstTrue.value? = some true := rfl
example : firstTrue.before? = some [false] := rfl

def dependentBools : DependentEnumeration Bool (fun _ => Bool) where
  indices := bools
  fibres := fun _ => bools

def dependentTrue : DependentResult (fun index value : Bool =>
    index = true ∧ value = true) :=
  dependentSearch dependentBools
    (fun index value => index = true ∧ value = true)
    (fun _ _ => inferInstance)

#eval dependentTrue.index?

example : dependentTrue.index? = some true := rfl

def comparisonTag : Nat :=
  match ResponseComparison.compare bools id (fun _ => false) with
  | .equal _ => 0
  | .different false _ => 1
  | .different true _ => 2

#eval comparisonTag

example : comparisonTag = 2 := rfl

end StructuralExhaustion.Core.AutomationFirstExamples
