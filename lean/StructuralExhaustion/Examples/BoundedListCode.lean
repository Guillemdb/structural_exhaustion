import StructuralExhaustion.Core.BoundedListCode
import StructuralExhaustion.Core.FiniteStructuralCutState

namespace StructuralExhaustion.Examples.BoundedListCode

open StructuralExhaustion.Core

abbrev ThreeBits := Core.BoundedListCode.BoundedList Bool 3

def left : ThreeBits := ⟨[true, false], by decide⟩
def right : ThreeBits := ⟨[true, false, true], by decide⟩

example : Core.BoundedListCode.encode left ≠
    Core.BoundedListCode.encode right := by decide

example {first second : ThreeBits}
    (equal : Core.BoundedListCode.encode first =
      Core.BoundedListCode.encode second) : first = second :=
  Core.BoundedListCode.encode_injective equal

example : Fintype.card (Core.BoundedListCode.Code Bool 3) = 27 := by
  rw [Core.BoundedListCode.code_card]
  decide

noncomputable example :
    Function.Injective
      (Core.BoundedListCode.codeEquivFinOfEquiv (Fintype.equivFin Bool) 3) :=
  Core.BoundedListCode.codeEquivFinOfEquiv_injective (Fintype.equivFin Bool) 3

noncomputable example :
    Function.Injective
      (Core.FiniteStructuralCutState.stateEquivFinOfEquiv
        (Fintype.equivFin Bool) (Equiv.refl (Fin 3))
        (Fintype.equivFin Bool) (Fintype.equivFin Unit)
        (Fintype.equivFin Empty) (Fintype.equivFin PUnit)) :=
  Core.FiniteStructuralCutState.stateEquivFinOfEquiv_injective
    (Fintype.equivFin Bool) (Equiv.refl (Fin 3))
    (Fintype.equivFin Bool) (Fintype.equivFin Unit)
    (Fintype.equivFin Empty) (Fintype.equivFin PUnit)

noncomputable def smallStateEncoding :=
  Core.FiniteStructuralCutState.stateEncodingOfEquiv
    (Fintype.equivFin Bool) (Equiv.refl (Fin 3))
    (Fintype.equivFin Bool) (Fintype.equivFin Unit)
    (Fintype.equivFin Empty) (Fintype.equivFin PUnit)

example : smallStateEncoding.finite.bound = smallStateEncoding.productCard :=
  smallStateEncoding.bound_eq_productCard

example : smallStateEncoding.finite.bound + 1 ≤
    smallStateEncoding.finite.exchangeWith 2 :=
  smallStateEncoding.finite.add_le_exchangeWith_of_le (by decide)

noncomputable example :
    Function.Injective smallStateEncoding.encodeToProduct :=
  smallStateEncoding.encodeToProduct_injective

noncomputable def boolColumn :=
  Core.FiniteObservedColumn.Encoding.ofFintype Bool

noncomputable def unitColumn :=
  Core.FiniteObservedColumn.Encoding.ofFintype Unit

noncomputable def emptyColumn :=
  Core.FiniteObservedColumn.Encoding.ofFintype Empty

noncomputable def punitColumn :=
  Core.FiniteObservedColumn.Encoding.ofFintype PUnit

noncomputable def smallColumns :=
  Core.FiniteObservedColumn.FourEncoding.ofFintype Bool Unit Empty PUnit

example : smallColumns.qCols =
    boolColumn.codeCard * unitColumn.codeCard *
      emptyColumn.codeCard * punitColumn.codeCard := rfl

example : boolColumn.encodeNodup [true, false] (by decide) =
    Core.BoundedListCode.encode (⟨[true, false], by decide⟩ :
      Core.BoundedListCode.BoundedList Bool 2) := rfl

/-- A non-Erdős fixture for the canonical column-propagation path. -/
noncomputable def columnStateEncoding :=
  Core.FiniteStructuralCutState.stateEncodingOfColumnBundle
    (Fintype.equivFin Bool) (Equiv.refl (Fin 3))
    smallColumns

example : columnStateEncoding.finite.bound =
    columnStateEncoding.productCard :=
  columnStateEncoding.bound_eq_productCard

example : columnStateEncoding.qCols = smallColumns.qCols := rfl

example : columnStateEncoding.productCard =
    4 ^ 2 * Fintype.card Bool ^ 2 * 3 ^ 2 * columnStateEncoding.qCols :=
  Core.FiniteStructuralCutState.stateEncodingOfColumnBundle_productCard
    (Fintype.equivFin Bool) (Equiv.refl (Fin 3)) smallColumns

noncomputable example :
    Function.Injective columnStateEncoding.finite.encode :=
  columnStateEncoding.finite.encode_injective

end StructuralExhaustion.Examples.BoundedListCode
