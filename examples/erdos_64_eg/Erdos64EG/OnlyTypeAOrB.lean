import Erdos64EG.Node63
import Erdos64EG.Node164

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Framework frontier theorem: only Type A or Type B remains

This file introduces no new residual, family, handoff, or routing object.
It only exposes the already-built framework carriers:

* the cold Part-XI interface has no untyped leaf: its focused decisions are
  either bypassed, routed through the G2 hot handoff, or continued through the
  G3 same-interface compression interface;
* after the Part-V split, the only live counterexample frontier constructors
  are the Type-B high-surplus handoff and the Type-A no-high handoff.
-/

/-- The node-[156] cold split has only the framework-prescribed alternatives:
bypass, G2 event, or G3 silent continuation. -/
theorem cold_g2_or_g3_framework_exhaustive {V : Type u}
    {residual : InitialResidual V} (stage : Node156DecisionStage residual) :
    (∃ (bypass : Node156Bypass V residual),
        stage = Core.ResidualRefinement.State.FocusedBranchDecision.bypass
          bypass) ∨
    (∃ (active : Node156Active V residual),
      ∃ (g2 : Node156G2Event active),
        stage = Core.ResidualRefinement.State.FocusedBranchDecision.yesBranch
          active g2) ∨
    (∃ (active : Node156Active V residual),
      ∃ (g3 : Node156G3Silent active),
        stage = Core.ResidualRefinement.State.FocusedBranchDecision.noBranch
          active g3) := by
  cases stage with
  | bypass data =>
      exact Or.inl ⟨data, rfl⟩
  | yesBranch active g2 =>
      exact Or.inr (Or.inl ⟨active, g2, rfl⟩)
  | noBranch active g3 =>
      exact Or.inr (Or.inr ⟨active, g3, rfl⟩)

/-- The node-[164] G3 endpoint has only the framework-prescribed alternatives:
bypass, same-interface finite replacement, or the retained CT3-residual leaf. -/
theorem cold_g3_same_interface_framework_exhaustive {V : Type u}
    {residual : InitialResidual V} (stage : Node164Stage residual) :
    (∃ (bypass : Node160Bypass V residual),
        stage =
          Core.ResidualRefinement.State.FocusedBranchDecisionYesContinuation.bypass
            bypass) ∨
    (∃ (active : Node160Active V residual),
      ∃ (allGood : Node160AllCompressionOrKnown active),
      ∃ (output : Node164FiniteSameInterfaceReplacementOutput active allGood),
        stage =
          Core.ResidualRefinement.State.FocusedBranchDecisionYesContinuation.activeYes
            active allGood output) ∨
    (∃ (active : Node160Active V residual),
      ∃ (residualBranch : Node160HasCT3Residual active),
        stage =
          Core.ResidualRefinement.State.FocusedBranchDecisionYesContinuation.noBranch
            active residualBranch) := by
  cases stage with
  | bypass data =>
      exact Or.inl ⟨data, rfl⟩
  | activeYes active allGood output =>
      exact Or.inr (Or.inl ⟨active, allGood, output, rfl⟩)
  | noBranch active residualBranch =>
      exact Or.inr (Or.inr ⟨active, residualBranch, rfl⟩)

/-- After nodes [57]--[64], any available counterexample frontier is exactly
one of the two original-paper continuations: Type B on the high-surplus edge
or Type A on the no-high edge.  This is only a destructor for the
framework-owned `Node63Stage`; it adds no application-owned route. -/
theorem only_type_A_or_B {V : Type u} {residual : InitialResidual V}
    (stage : Node63Stage residual) :
    (∃ (node61 : Node61Stage residual),
      ∃ (high : Node62HighSurplus node61),
      ∃ (output : Node64Output (residual := residual) node61 high),
        stage =
          Core.ResidualRefinement.State.DependentDecisionNoAfterYes.yesBranch
            node61 high output) ∨
    (∃ (node61 : Node61Stage residual),
      ∃ (noHigh : Node62NoHighSurplus node61),
      ∃ (output : Node63Output (residual := residual) node61 noHigh),
        stage =
          Core.ResidualRefinement.State.DependentDecisionNoAfterYes.noBranch
            node61 noHigh output) := by
  cases stage with
  | yesBranch previous high output =>
      exact Or.inl ⟨previous, high, output, rfl⟩
  | noBranch previous noHigh output =>
      exact Or.inr ⟨previous, noHigh, output, rfl⟩

end Erdos64EG.Internal
