import StructuralExhaustion.Graph.TypeADeclaredContinuationCoordinate

namespace StructuralExhaustion.Examples.TypeADeclaredContinuationCoordinate

open StructuralExhaustion

universe u v w x y

variable {V : Type u} (object : Graph.FiniteObject V)
variable (profile : Graph.TypeACanonicalReceiverTrace.SupportProfile object)
variable (port : Graph.TypeAAnchoredReturnCoordinate.Port object profile)
variable (Label : Type v) (SupportDatum : Type w) (Value : Type x) (Fibre : Type y)

abbrev FamilyData := Graph.TypeADeclaredContinuationCoordinate.Family
  object profile port Label SupportDatum Value Fibre

/-- Non-Erdős transfer fixture: arbitrary finite response data attached to
stored local connector paths is classified by the same raw graph method. -/
def classifySupplied
    (family : FamilyData object profile port Label SupportDatum Value Fibre) :
    Graph.TypeADeclaredContinuationCoordinate.Family.Outcome
      object profile port family :=
  Graph.TypeADeclaredContinuationCoordinate.Family.classify
    object profile port family

theorem supplied_work_bound [DecidableEq V]
    (family : FamilyData object profile port Label SupportDatum Value Fibre) :
    Graph.TypeADeclaredContinuationCoordinate.Family.classificationChecks
        object profile port family ≤
      Graph.TypeADeclaredContinuationCoordinate.Family.totalStoredPrefixLength
        object profile port family := by
  exact Graph.TypeADeclaredContinuationCoordinate.Family.classificationChecks_le_totalStoredPrefixLength
    object profile port family

theorem supplied_separator_global_first
    (family : FamilyData object profile port Label SupportDatum Value Fibre)
    (separator : Graph.TypeADeclaredContinuationCoordinate.Family.Separator
      object profile port family) :
    ∀ a ∈ family.coordinates, ∀ b ∈ family.coordinates,
      ∀ j (aBound : j < (a.tail object profile port).length)
        (bBound : j < (b.tail object profile port).length),
        j < separator.branch.index →
        (a.tail object profile port).get ⟨j, aBound⟩ =
          (b.tail object profile port).get ⟨j, bBound⟩ :=
  separator.noEarlierAnyPair object profile port

end StructuralExhaustion.Examples.TypeADeclaredContinuationCoordinate
