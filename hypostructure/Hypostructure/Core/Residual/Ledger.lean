import Hypostructure.Core.Prelude

/-!
# Accumulated residual ledgers

The root ledger stores one residual.  Every later ledger is a dependent
extension that retains its complete predecessor literally and adds one new
proof or data value.  Extensions cannot replace the residual carrier.
-/

namespace Hypostructure.Core.Residual

universe uResidual uStage uPrevious uAdded

/-- A stage with one stable residual carrier.  The residual type is an
`outParam` so it is inferred from the stage throughout a predecessor chain. -/
class HasResidual (Stage : Sort uStage)
    (Residual : outParam (Type uResidual)) where
  residual : Stage -> Residual

/-- Read the stable residual carried by a ledger stage. -/
def residualOf {Stage : Sort uStage} {Residual : Type uResidual}
    [HasResidual Stage Residual] (stage : Stage) : Residual :=
  HasResidual.residual stage

/-- The root of an accumulated ledger.  It is the only operation that chooses
the residual value. -/
structure Ledger (Residual : Type uResidual) where
  private mk ::
  residual : Residual

namespace Ledger

/-- Start an empty accumulated ledger at one literal residual. -/
def initial (residual : Residual) : Ledger Residual :=
  .mk residual

instance : HasResidual (Ledger Residual) Residual where
  residual := Ledger.residual

@[simp] theorem residualOf_initial (residual : Residual) :
    residualOf (initial residual) = residual :=
  rfl

/-- One no-copy ledger extension.  `previous` is the literal complete incoming
stage; `added` is the sole new value and may depend on that exact stage. -/
structure Extension (Previous : Sort uPrevious)
    (Added : Previous -> Sort uAdded) where
  private mk ::
  previous : Previous
  added : Added previous

/-- Extend a ledger stage with exactly one dependent proof or data value. -/
def extend {Previous : Sort uPrevious} {Added : Previous -> Sort uAdded}
    (previous : Previous) (added : Added previous) :
    Extension Previous Added :=
  .mk previous added

instance {Previous : Sort uPrevious} {Added : Previous -> Sort uAdded}
    {Residual : Type uResidual} [HasResidual Previous Residual] :
    HasResidual (Extension Previous Added) Residual where
  residual extension := residualOf extension.previous

@[simp] theorem extend_previous
    {Previous : Sort uPrevious} {Added : Previous -> Sort uAdded}
    (previous : Previous) (added : Added previous) :
    (extend previous added).previous = previous :=
  rfl

@[simp] theorem extend_added
    {Previous : Sort uPrevious} {Added : Previous -> Sort uAdded}
    (previous : Previous) (added : Added previous) :
    (extend previous added).added = added :=
  rfl

/-- Every extension is canonically reconstructed from its retained
predecessor and its one added value.  The constructor remains private; this
theorem is the public equality API for ledger reconstruction. -/
theorem extend_eta (stage : Extension Previous Added) :
    extend stage.previous stage.added = stage := by
  cases stage
  rfl

@[simp] theorem residualOf_extend
    {Previous : Sort uPrevious} {Added : Previous -> Sort uAdded}
    {Residual : Type uResidual} [HasResidual Previous Residual]
    (previous : Previous) (added : Added previous) :
    residualOf (extend previous added) = residualOf previous :=
  rfl

end Ledger

end Hypostructure.Core.Residual
