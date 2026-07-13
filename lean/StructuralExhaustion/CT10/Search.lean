import StructuralExhaustion.CT10.State

namespace StructuralExhaustion.CT10

universe uAmbient uBranch uDatum uClass uPromotion
variable {P : Core.Problem.{uAmbient, uBranch}}
variable (capability : Capability.{uAmbient, uBranch, uDatum, uClass, uPromotion} P)
variable (input : Input capability)

theorem datum_mem_own_row (datum : capability.Datum) (member : datum ∈ input.data.values) :
    datum ∈ row capability input (capability.classOf datum) := by
  simp [row, member]

inductive DirectDecision where
  | found (residual : DirectResidual capability)
  | absent (state : DirectAbsent capability)

def analyzeDirect : DirectDecision capability :=
  match Core.FiniteSearch.search capability.classes capability.Direct
      capability.directDecidable with
  | .found cls direct => .found ⟨cls, direct⟩
  | .absent absent => .absent ⟨absent⟩

inductive MissingDecision where
  | promoted (residual : PromotedResidual capability input)
  | exhaustive (certificate : ExhaustiveCertificate capability input)

def rowEmptyDecidable (cls : capability.Class) :
    Decidable (row capability input cls = []) :=
  letI : DecidableEq capability.Datum := input.data.decEq
  inferInstance

def analyzeMissing (directAbsent : DirectAbsent capability) :
    MissingDecision capability input :=
  match Core.FiniteSearch.search capability.classes
      (fun cls => row capability input cls = [])
      (rowEmptyDecidable capability input) with
  | .found cls empty => .promoted {
      directAbsent := directAbsent
      missing := ⟨cls, empty⟩
      promotion := capability.promote cls
      exact := rfl
    }
  | .absent noEmpty => .exhaustive {
      directAbsent := directAbsent
      populated := fun cls => List.exists_mem_of_ne_nil _ (noEmpty cls)
    }

theorem direct_sound :
    match analyzeDirect capability with
    | .found residual => capability.Direct residual.cls
    | .absent _ => ∀ cls, ¬ capability.Direct cls := by
  cases analyzeDirect capability with
  | found residual => exact residual.direct
  | absent state => exact state.absent

theorem missing_sound (directAbsent : DirectAbsent capability) :
    match analyzeMissing capability input directAbsent with
    | .promoted residual => row capability input residual.missing.cls = []
    | .exhaustive _ => ∀ cls, ∃ datum, datum ∈ row capability input cls := by
  cases analyzeMissing capability input directAbsent with
  | promoted residual => exact residual.missing.empty
  | exhaustive certificate => exact certificate.populated

end StructuralExhaustion.CT10
