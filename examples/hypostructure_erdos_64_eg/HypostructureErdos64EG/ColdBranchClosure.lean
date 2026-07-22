import Hypostructure.CT3.SameInterface

/-!
# Framework-owned cold-branch closure

The cold branch is a finite CT3 schedule followed by same-interface
registration.  The application supplies the schedule semantics and the
verified package constructor; CT3 owns classification, witness extraction,
package registration, and predecessor routing.

This facade intentionally replaces a chain of bookkeeping nodes.  Those
nodes remain useful as manuscript references, but they are not separate
residual transitions in the executable proof.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe uPrevious uItem uGood uResidual

structure ColdBranchContract (Previous : Sort uPrevious) where
  focus : Core.Residual.Focus.Profile Previous
  schedule :
    CT3.Schedule.FocusedContract.{uPrevious, uItem} focus
  package : CT3.SameInterface.PackageContract.{uPrevious, uItem, uGood, uResidual}
    schedule

abbrev ColdBranchStage
    {Previous : Sort uPrevious} (contract : ColdBranchContract Previous) :=
  (contract.package.verifiedSameInterfaceContract).Stage

/-! The complete cold branch is one framework-owned execution. -/
noncomputable def closeColdBranch
    {Previous : Sort uPrevious} (contract : ColdBranchContract Previous)
    (previous : Previous) : ColdBranchStage contract :=
  contract.package.registerClassified previous

@[simp] theorem closeColdBranch_previous
    {Previous : Sort uPrevious} (contract : ColdBranchContract Previous)
    (previous : Previous) :
    (closeColdBranch contract previous).previous.previous = previous := by
  exact contract.package.registerClassified_source_previous previous

end HypostructureErdos64EG
