import StructuralExhaustion.Core.GracefulDegradation

namespace StructuralExhaustion.Examples.GracefulDegradation

open StructuralExhaustion

abbrev Residual := Nat
abbrev Bypass (_ : Residual) := PUnit
abbrev Active (_ : Residual) := PUnit
abbrev OuterYes (_ : Residual) (_ : PUnit) : Prop := True
abbrev OuterNo (_ : Residual) (_ : PUnit) : Prop := True
abbrev OuterOutput (_ : Residual) (_ : PUnit) (_ : True) := PUnit
abbrev InnerYes (residual : Residual) (_ : PUnit) (_ : True) : Prop :=
  residual = 0
abbrev InnerNo (residual : Residual) (_ : PUnit) (_ : True) : Prop :=
  residual = 0
abbrev Terminal (_ : Residual) (_ : PUnit) (_ : True) (_ : PUnit) := PUnit
abbrev Guard (residual : Residual) (_ : PUnit) (_ : True)
    (_ : residual = 0) : Prop := residual = 1

abbrev Source :=
  Core.ResidualRefinement.State.FocusedBranchYesContinuationNoDecision
    Bypass Active OuterYes OuterNo OuterOutput InnerYes InnerNo

abbrev Split :=
  Core.ResidualRefinement.State.GuardedDegradation
    Bypass Active OuterYes OuterNo OuterOutput InnerYes InnerNo Terminal Guard

abbrev AlternateOutput (_ : Residual)
    (_ : Core.ResidualRefinement.State.FocusedBranchNestedNoActive
      Active OuterNo InnerNo 0) := PUnit

abbrev Continued :=
  Core.ResidualRefinement.State.GuardedDegradationAlternateContinuation
    Bypass Active OuterYes OuterNo OuterOutput InnerYes InnerNo Terminal Guard
    (fun _ _ => PUnit)

abbrev Next (_ : Residual) (_ : PUnit) := Nat

abbrev Merged :=
  Core.ResidualRefinement.State.GuardedDegradationMerged
    Bypass Active OuterYes OuterNo OuterOutput InnerYes InnerNo Terminal Guard
    (fun _ _ => PUnit) Next

noncomputable def splitNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available Source) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts) Split :=
  Core.ResidualRefinement.State.StageNode.terminalizeGuardOrDegrade
    (terminal := fun _ _ _ _ => PUnit.unit)
    (decideGuard := fun _ _ _ _ => inferInstance)
    (close := fun residual _ _ equal one => by
      change residual = 0 at equal
      change residual = 1 at one
      exact Nat.zero_ne_one (equal.symm.trans one))

noncomputable def continueNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available Split) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts) Continued :=
  Core.ResidualRefinement.State.StageNode.continueGuardedDegradationAlternate
    fun _ _ => PUnit.unit

noncomputable def mergeNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available Continued) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts) Merged :=
  Core.ResidualRefinement.State.StageNode.mergeGuardedDegradation
    fun residual _ => residual + 7

private def sourceState (source : Source 0) :
    Core.ResidualRefinement.State Residual
      [Core.ResidualRefinement.State.Available Source] :=
  (Core.ResidualRefinement.State.initial 0).add
    (Core.ResidualRefinement.State.Available Source) ⟨source⟩

noncomputable def degradedRun :=
  mergeNode.run (continueNode.run (splitNode.run
    (sourceState (.innerYesBranch PUnit.unit True.intro rfl))))

noncomputable def alternateRun :=
  mergeNode.run (continueNode.run (splitNode.run
    (sourceState (.innerNoBranch PUnit.unit True.intro rfl))))

noncomputable def terminalRun :=
  splitNode.run
    (sourceState (.outerYesBranch PUnit.unit True.intro PUnit.unit))

theorem degraded_run_reaches_merged :
    Core.ResidualRefinement.State.Available Merged degradedRun.residual :=
  degradedRun.latest

theorem alternate_run_reaches_merged :
    Core.ResidualRefinement.State.Available Merged alternateRun.residual :=
  alternateRun.latest

theorem terminal_run_accumulates_split :
    Core.ResidualRefinement.State.Available Split terminalRun.residual :=
  terminalRun.require
    (property := Core.ResidualRefinement.State.Available Split)

#print axioms degraded_run_reaches_merged
#print axioms alternate_run_reaches_merged
#print axioms terminal_run_accumulates_split

end StructuralExhaustion.Examples.GracefulDegradation
