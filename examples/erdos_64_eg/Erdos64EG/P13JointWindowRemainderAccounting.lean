import Erdos64EG.P13HighEntropyRemainderBits
import StructuralExhaustion.Core.ExactHandoff
import StructuralExhaustion.Core.FiniteJointCapacity

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Node [52]: conditional joint window--remainder accounting support

The current predecessors do not prove that node `[24]`'s commuting window
choices and node `[48]`'s exact remainder states admit one injective labelled
skeleton code.  This file retains the exact realization payload and its local
capacity theorem as conditional support.  It deliberately exposes no outcome
or absence constructor: the original diagram has only `[51] -> [52] -> [54]`.
-/

/-- A genuine joint accounting realization.  Every pair is interpreted by
node `[24]`'s actual graph-completion gluing, and both coordinates are
recoverable from that completion.  The final code lands in node `[48]`'s
literal labelled edge-set skeleton. -/
structure P13Node52JointAccountingRealization
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24DensityHandoff ctx node21)
    (realized : P13CurvatureProductCostRealization ctx node21 node24)
    (node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized)
    (node50 : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49)
    (node51 : VerifiedP13Node51HighEntropyBits
      ctx node21 node24 realized node49 node50) : Type (u + 1)
    extends Core.ExactHandoff node51 where
  WindowState : Type u
  windowStates : Core.OrderedCollection WindowState
  LocalCompletion : SelectedP13Window ctx → Type u
  GlobalCompletion : Type u
  choices : WindowState → realized.State →
    ∀ window, LocalCompletion window
  glue : (∀ window, LocalCompletion window) → GlobalCompletion
  recoverWindow : GlobalCompletion → WindowState
  recoverRemainder : GlobalCompletion → realized.State
  recoverWindow_glue : ∀ windowState remainderState,
    recoverWindow (glue (choices windowState remainderState)) = windowState
  recoverRemainder_glue : ∀ windowState remainderState,
    recoverRemainder (glue (choices windowState remainderState)) = remainderState
  skeletonCode : GlobalCompletion → P13BaselineSkeleton ctx
  skeletonCodes : FinEnum (P13BaselineSkeleton ctx)
  jointCodeInjective : Function.Injective (fun pair : WindowState × realized.State ↦
    skeletonCode (glue (choices pair.1 pair.2)))
  rightScheduleExact : realized.states =
    (p13RemainderStateEntropyProfile realized).states

/-- Compatibility spelling; exact handoff storage is framework-owned. -/
theorem P13Node52JointAccountingRealization.exactPrevious
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    {realized : P13CurvatureProductCostRealization ctx node21 node24}
    {node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized}
    {node50 : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49}
    {node51 : VerifiedP13Node51HighEntropyBits
      ctx node21 node24 realized node49 node50}
    (joint : P13Node52JointAccountingRealization
      ctx node21 node24 realized node49 node50 node51) :
    joint.previous = node51 :=
  joint.previousExact

/-- Core-owned capacity profile on the two exact supplied schedules. -/
noncomputable def p13Node52JointCapacityProfile
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    {realized : P13CurvatureProductCostRealization ctx node21 node24}
    {node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized}
    {node50 : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49}
    {node51 : VerifiedP13Node51HighEntropyBits
      ctx node21 node24 realized node49 node50}
    (joint : P13Node52JointAccountingRealization
      ctx node21 node24 realized node49 node50 node51) :
    Core.FiniteJointCapacity.Profile where
  Left := joint.WindowState
  Right := realized.State
  Code := P13BaselineSkeleton ctx
  left := joint.windowStates
  right := realized.states
  codes := joint.skeletonCodes
  encode := fun windowState remainderState =>
    joint.skeletonCode (joint.glue (joint.choices windowState remainderState))
  encodeInjectiveOnSchedules := by
    intro left₁ left₂ right₁ right₂ _ _ _ _ equal
    have pairEqual : (left₁, right₁) = (left₂, right₂) :=
      joint.jointCodeInjective equal
    exact ⟨congrArg Prod.fst pairEqual, congrArg Prod.snd pairEqual⟩

/-- A realized node `[52]` obtains the exact joint product-capacity inequality
without constructing or scanning the Cartesian product. -/
theorem p13Node52_jointCapacity
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    {realized : P13CurvatureProductCostRealization ctx node21 node24}
    {node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized}
    {node50 : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49}
    {node51 : VerifiedP13Node51HighEntropyBits
      ctx node21 node24 realized node49 node50}
    (joint : P13Node52JointAccountingRealization
      ctx node21 node24 realized node49 node50 node51) :
    joint.windowStates.values.length * realized.states.values.length ≤
      joint.skeletonCodes.card :=
  (p13Node52JointCapacityProfile joint).left_mul_right_le_codeCard

end Erdos64EG.Internal
