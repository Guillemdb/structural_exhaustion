import Hypostructure.Core.Residual.Decision

/-!
# Continued-decision fixture

This fixture advances a binary decision twice.  The second step receives the
first yes-arm payload from the literal predecessor, while Core retains the no
arm and constructs the new branch-indexed extension.
-/

namespace Hypostructure.Fixtures.Decision

open Hypostructure.Core

abbrev Root := Residual.Ledger Nat

def Positive (root : Root) : Prop :=
  0 < Residual.residualOf root

def NotPositive (root : Root) : Prop :=
  Not (Positive root)

def decision : Residual.Decision.Node Root Positive NotPositive :=
  Residual.Decision.Node.complement Positive fun root => by
    unfold Positive
    infer_instance

abbrev FirstYes (_root : Root) (_positive : Positive _root) := Nat

abbrev FirstStage :=
  Residual.Decision.YesContinuationStage
    (Yes := Positive) (No := NotPositive) FirstYes

noncomputable def first (root : Root) : FirstStage :=
  Residual.Decision.continueYes (decision.run root)
    fun _positive => (7 : Nat)

abbrev SecondYes (_root : Root) (_positive : Positive _root)
    (_current : FirstYes _root _positive) := Nat

abbrev SecondStage :=
  Residual.Decision.YesContinuationSuccessorStage
    (Yes := Positive) (No := NotPositive)
    (CurrentYes := FirstYes)
    (CurrentNo := fun _root _notPositive => PUnit)
    SecondYes

noncomputable def second (root : Root) : SecondStage :=
  Residual.Decision.continueYesBranch (first root)
    fun _positive current => current + 1

def positiveRoot : Root :=
  Residual.Ledger.initial 3

def zeroRoot : Root :=
  Residual.Ledger.initial 0

theorem second_retains_first (root : Root) :
    (second root).previous = first root :=
  rfl

theorem second_retains_root_residual (root : Root) :
    Residual.residualOf (second root) = Residual.residualOf root :=
  rfl

theorem positive_is_positive : Positive positiveRoot := by
  change 0 < 3
  decide

theorem zero_is_not_positive : NotPositive zeroRoot := by
  change Not (0 < 0)
  decide

#print axioms second_retains_first
#print axioms second_retains_root_residual
#print axioms positive_is_positive
#print axioms zero_is_not_positive

end Hypostructure.Fixtures.Decision
