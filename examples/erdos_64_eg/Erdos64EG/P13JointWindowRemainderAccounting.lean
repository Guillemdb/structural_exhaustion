import Erdos64EG.P13HighEntropyRemainderBits
import StructuralExhaustion.Core.FiniteJointCapacity

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Node [52]: joint window--remainder accounting frontier

The current predecessors do not prove that node `[24]`'s commuting window
choices and node `[48]`'s exact remainder states admit one injective labelled
skeleton code.  Node `[52]` therefore records the manuscript-faithful
realized/open dichotomy for precisely that same-context producer.  It does not
assert the sharper density cap or close node `[54]`.
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
      ctx node21 node24 realized node49 node50) : Type (u + 1) where
  previous : VerifiedP13Node51HighEntropyBits
    ctx node21 node24 realized node49 node50
  exactPrevious : previous = node51
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

/-- Exact missing semantic producers named by the open node-[52] residual. -/
inductive P13Node52OpenProducer
  | multiscaleWindowStates
  | jointWindowRemainderCommutation
  | injectiveBaselineEncoding
  | finiteCapArithmetic
  deriving DecidableEq

structure P13Node52JointAccountingRequirement
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24DensityHandoff ctx node21)
    (realized : P13CurvatureProductCostRealization ctx node21 node24)
    (node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized)
    (node50 : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49)
    (node51 : VerifiedP13Node51HighEntropyBits
      ctx node21 node24 realized node49 node50) : Type (u + 1) where
  previous : VerifiedP13Node51HighEntropyBits
    ctx node21 node24 realized node49 node50
  exactPrevious : previous = node51
  openProducers : List P13Node52OpenProducer
  openProducersExact : openProducers =
    [.multiscaleWindowStates, .jointWindowRemainderCommutation,
      .injectiveBaselineEncoding, .finiteCapArithmetic]
  absent : ¬Nonempty (P13Node52JointAccountingRealization
    ctx node21 node24 realized node49 node50 node51)

/-- The open branch has only a conditional same-context consumer.  It cannot
manufacture the independent node-[55] strict-quarter budget. -/
structure P13Node52OpenLargeBudgetHandoff
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24DensityHandoff ctx node21)
    (realized : P13CurvatureProductCostRealization ctx node21 node24)
    (node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized)
    (node50 : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49)
    (node51 : VerifiedP13Node51HighEntropyBits
      ctx node21 node24 realized node49 node50) : Type (u + 1) where
  previous : P13Node52JointAccountingRequirement
    ctx node21 node24 realized node49 node50 node51
  consume : P13QuarterNetBudget ctx (node21 := node21) node24.coverage →
    P13QuarterNetDeficiencyHandoff ctx node21 node24.coverage

noncomputable def p13Node52OpenLargeBudgetHandoff
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    {realized : P13CurvatureProductCostRealization ctx node21 node24}
    {node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized}
    {node50 : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49}
    {node51 : VerifiedP13Node51HighEntropyBits
      ctx node21 node24 realized node49 node50}
    (requirement : P13Node52JointAccountingRequirement
      ctx node21 node24 realized node49 node50 node51) :
    P13Node52OpenLargeBudgetHandoff
      ctx node21 node24 realized node49 node50 node51 where
  previous := requirement
  consume := fun budget =>
    p13QuarterNetDeficiencyHandoff node24.globalRankPrefix budget

inductive P13Node52Outcome
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24DensityHandoff ctx node21)
    (realized : P13CurvatureProductCostRealization ctx node21 node24)
    (node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized)
    (node50 : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49)
    (node51 : VerifiedP13Node51HighEntropyBits
      ctx node21 node24 realized node49 node50) : Type (u + 2)
  | realized (payload : P13Node52JointAccountingRealization
      ctx node21 node24 realized node49 node50 node51)
  | openRequirement
      (requirement : P13Node52JointAccountingRequirement
        ctx node21 node24 realized node49 node50 node51)

/-- Proof-level split only; no graph, state, product, or Boolean universe is
evaluated. -/
noncomputable def runP13Node52
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    {realized : P13CurvatureProductCostRealization ctx node21 node24}
    {node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized}
    {node50 : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49}
    (node51 : VerifiedP13Node51HighEntropyBits
      ctx node21 node24 realized node49 node50) :
    P13Node52Outcome ctx node21 node24 realized node49 node50 node51 := by
  by_cases available : Nonempty (P13Node52JointAccountingRealization
      ctx node21 node24 realized node49 node50 node51)
  · exact .realized (Classical.choice available)
  · exact .openRequirement {
      previous := node51
      exactPrevious := rfl
      openProducers := [.multiscaleWindowStates,
        .jointWindowRemainderCommutation, .injectiveBaselineEncoding,
        .finiteCapArithmetic]
      openProducersExact := rfl
      absent := available
    }

theorem runP13Node52_exhaustive
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    {realized : P13CurvatureProductCostRealization ctx node21 node24}
    {node49 : VerifiedP13Node49FiniteEntropy ctx node21 node24 realized}
    {node50 : VerifiedP13Node50EntropyScaleSplit
      ctx node21 node24 realized node49}
    (node51 : VerifiedP13Node51HighEntropyBits
      ctx node21 node24 realized node49 node50) :
    (∃ payload, runP13Node52 node51 = .realized payload) ∨
      (∃ requirement, runP13Node52 node51 = .openRequirement requirement) := by
  cases outcome : runP13Node52 node51 with
  | realized payload => exact Or.inl ⟨payload, rfl⟩
  | openRequirement requirement => exact Or.inr ⟨requirement, rfl⟩

def p13Node52Checks : Nat := 0

theorem p13Node52Checks_eq_zero : p13Node52Checks = 0 := rfl

end Erdos64EG.Internal
