import Erdos64EG.Future.P13FixedSkeletonWindowMajority
import Erdos64EG.Future.P13FixedSkeletonCrossWindowIncidencePairs
import StructuralExhaustion.Core.LocalInjectiveLedger

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Core.LocalInjectiveLedger

universe u

/-!
# Aggregate oriented-incidence ledger for cross-heavy windows

This stage consumes exactly the cross-heavy side of the local `7`-of-`13`
split.  It filters the already selected ambient-cubic windows, aggregates only
their actual cross-window branch-excess entries, and labels each entry by its
literal oriented window token.  Local duplicate-freeness and distinct window
owners make the aggregate label list injective.

The ledger deliberately remains oriented.  Passing to unordered edges would
require an additional factor-two/reverse-closure argument, and interpreting
the edges as commuting completion data would require the still-open gluing
semantics.  Neither claim is made here.
-/

private theorem p13BranchExcessCorridor_token_injective
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {window : P13AmbientCubicWindow ctx} :
    Function.Injective (fun corridor : P13BranchExcessCorridor ctx window =>
      corridor.stub.token) := by
  intro left right equal
  cases left with
  | mk leftStub leftSelected leftResult leftExact =>
    cases right with
    | mk rightStub rightSelected rightResult rightExact =>
      dsimp at equal
      have stubEqual : leftStub = rightStub := by
        cases leftStub with
        | mk leftToken leftCubic =>
          cases rightStub with
          | mk rightToken rightCubic =>
            dsimp at equal
            subst rightToken
            rfl
      subst rightStub
      have resultEqual : leftResult = rightResult :=
        leftExact.trans rightExact.symm
      cases resultEqual
      congr

private theorem p13WindowBranchExcessCorridors_nodup
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13AmbientCubicWindow ctx) :
    (p13WindowBranchExcessCorridors ctx window).Nodup := by
  unfold p13WindowBranchExcessCorridors
  apply List.Nodup.map
  · intro left right equal
    apply Subtype.ext
    exact congrArg P13BranchExcessCorridor.stub equal
  · exact (InducedPathColdBranchExcess.branchExcessStubs_nodup
      ctx.G.object window.1 window.2).attach

private theorem p13WindowBranchExcessComponentEntries_nodup
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13AmbientCubicWindow ctx) :
    (p13WindowBranchExcessComponentEntries ctx window).Nodup := by
  unfold p13WindowBranchExcessComponentEntries
  apply List.Nodup.map
  · intro left right equal
    have sourceEqual := congrArg P13BranchExcessComponentEntry.source equal
    exact eq_of_heq (Sigma.mk.inj_iff.mp sourceEqual).2
  · exact p13WindowBranchExcessCorridors_nodup ctx window

theorem p13WindowCrossWindowEntries_nodup
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13AmbientCubicWindow ctx) :
    (p13WindowCrossWindowEntries ctx window).Nodup := by
  unfold p13WindowCrossWindowEntries
  exact (p13WindowBranchExcessComponentEntries_nodup ctx window).filter _

theorem p13WindowCrossWindowToken_injective
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (window : P13AmbientCubicWindow ctx)
    {left right : P13BranchExcessComponentEntry ctx}
    (leftMem : left ∈ p13WindowCrossWindowEntries ctx window)
    (rightMem : right ∈ p13WindowCrossWindowEntries ctx window)
    (equal : left.source.2.stub.token = right.source.2.stub.token) :
    left = right := by
  have leftFull := (mem_p13WindowCrossWindowEntries_iff.mp leftMem).1
  have rightFull := (mem_p13WindowCrossWindowEntries_iff.mp rightMem).1
  rw [p13WindowBranchExcessComponentEntries, List.mem_map] at leftFull rightFull
  rcases leftFull with ⟨leftSource, _leftSourceMem, rfl⟩
  rcases rightFull with ⟨rightSource, _rightSourceMem, rfl⟩
  have sourceEqual := p13BranchExcessCorridor_token_injective equal
  change leftSource = rightSource at sourceEqual
  cases sourceEqual
  rfl

/-- Exact selected-window sublist on the cross-heavy side of the computed
local majority split. -/
noncomputable def p13CrossHeavyWindows
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    List (P13AmbientCubicWindow ctx) :=
  (p13AmbientCubicWindows ctx).orderedValues.filter fun window =>
    7 ≤ (p13WindowCrossWindowEntries ctx window).length

theorem p13CrossHeavyWindows_nodup
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13CrossHeavyWindows ctx).Nodup := by
  unfold p13CrossHeavyWindows
  exact (p13AmbientCubicWindows ctx).nodup_orderedValues.filter _

theorem p13CrossHeavyWindow_large
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {window : P13AmbientCubicWindow ctx}
    (member : window ∈ p13CrossHeavyWindows ctx) :
    7 ≤ (p13WindowCrossWindowEntries ctx window).length := by
  rw [p13CrossHeavyWindows, List.mem_filter] at member
  exact of_decide_eq_true member.2

/-- The literal source token of one retained cross-window entry. -/
def p13CrossHeavyToken
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (_window : P13AmbientCubicWindow ctx)
    (entry : P13BranchExcessComponentEntry ctx) :
    InducedPathWindowLedger.Token ctx.G.object :=
  entry.source.2.stub.token

theorem p13WindowCrossWindowTokens_separated
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {leftWindow rightWindow : P13AmbientCubicWindow ctx}
    (distinct : leftWindow ≠ rightWindow)
    {left right : P13BranchExcessComponentEntry ctx}
    (leftMem : left ∈ p13WindowCrossWindowEntries ctx leftWindow)
    (rightMem : right ∈ p13WindowCrossWindowEntries ctx rightWindow) :
    p13CrossHeavyToken leftWindow left ≠
      p13CrossHeavyToken rightWindow right := by
  intro equal
  apply distinct
  apply Subtype.ext
  have leftOwner :=
    p13WindowBranchExcessComponentEntry_sourceWindow
      (mem_p13WindowCrossWindowEntries_iff.mp leftMem).1
  have rightOwner :=
    p13WindowBranchExcessComponentEntry_sourceWindow
      (mem_p13WindowCrossWindowEntries_iff.mp rightMem).1
  calc
    leftWindow.1 = left.source.1.1 := congrArg Subtype.val leftOwner.symm
    _ = left.source.2.stub.window := left.source.2.sameWindow.symm
    _ = right.source.2.stub.window := congrArg Sigma.fst equal
    _ = right.source.1.1 := right.source.2.sameWindow
    _ = rightWindow.1 := congrArg Subtype.val rightOwner

/-- Reusable aggregate-ledger instance on the exact cross-heavy residual. -/
noncomputable def p13CrossHeavyProfile
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Profile (P13AmbientCubicWindow ctx)
      (P13BranchExcessComponentEntry ctx)
      (InducedPathWindowLedger.Token ctx.G.object) where
  indices := p13CrossHeavyWindows ctx
  entries := p13WindowCrossWindowEntries ctx
  entriesNodup := p13WindowCrossWindowEntries_nodup ctx
  label := p13CrossHeavyToken
  localInjective := by
    intro window left right leftMem rightMem equal
    exact p13WindowCrossWindowToken_injective window leftMem rightMem equal
  separated := by
    intro leftWindow rightWindow distinct left right leftMem rightMem equal
    exact p13WindowCrossWindowTokens_separated distinct leftMem rightMem equal

/-- No oriented selected-window incidence occurs twice in the complete
cross-heavy ledger. -/
theorem p13CrossHeavyLabels_nodup
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13CrossHeavyProfile ctx).labels.Nodup :=
  (p13CrossHeavyProfile ctx).labels_nodup (p13CrossHeavyWindows_nodup ctx)

/-- The same ledger exposed without unfolding the generic profile. -/
noncomputable def p13CrossHeavyOrientedTokens
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    List (InducedPathWindowLedger.Token ctx.G.object) :=
  (p13CrossHeavyWindows ctx).flatMap fun window =>
    (p13WindowCrossWindowEntries ctx window).map
      (p13CrossHeavyToken window)

theorem p13CrossHeavyOrientedTokens_nodup
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13CrossHeavyOrientedTokens ctx).Nodup := by
  rw [p13CrossHeavyOrientedTokens, List.nodup_flatMap]
  constructor
  · intro window _member
    apply List.Nodup.map_on
    · intro left leftMem right rightMem equal
      exact p13WindowCrossWindowToken_injective window
        leftMem rightMem equal
    · exact p13WindowCrossWindowEntries_nodup ctx window
  · apply (List.nodup_iff_pairwise_ne.mp
      (p13CrossHeavyWindows_nodup ctx)).imp
    intro leftWindow rightWindow distinct
    change List.Disjoint
      ((p13WindowCrossWindowEntries ctx leftWindow).map
        (p13CrossHeavyToken leftWindow))
      ((p13WindowCrossWindowEntries ctx rightWindow).map
        (p13CrossHeavyToken rightWindow))
    rw [List.disjoint_left]
    intro token leftMem rightMem
    rw [List.mem_map] at leftMem rightMem
    rcases leftMem with ⟨left, leftMember, rfl⟩
    rcases rightMem with ⟨right, rightMember, equal⟩
    exact p13WindowCrossWindowTokens_separated distinct
      leftMember rightMember equal.symm

private theorem seven_mul_localWindows_le_sum
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (windows : List (P13AmbientCubicWindow ctx))
    (large : ∀ window ∈ windows,
      7 ≤ (p13WindowCrossWindowEntries ctx window).length) :
    7 * windows.length ≤
      (windows.map fun window =>
        (p13WindowCrossWindowEntries ctx window).length).sum := by
  induction windows with
  | nil => simp
  | cons window rest ih =>
      have head := large window (by simp)
      have tail : ∀ other ∈ rest,
          7 ≤ (p13WindowCrossWindowEntries ctx other).length := by
        intro other member
        exact large other (by simp [member])
      have restBound := ih tail
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      rw [Nat.mul_add, Nat.mul_one, Nat.add_comm (7 * rest.length) 7]
      exact Nat.add_le_add head restBound

/-- Summing the exact local cross-heavy lower bounds gives seven distinct
oriented incidences per retained window. -/
theorem seven_mul_p13CrossHeavyWindows_le_orientedIncidences
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    7 * (p13CrossHeavyWindows ctx).length ≤
      (p13CrossHeavyOrientedTokens ctx).length := by
  rw [p13CrossHeavyOrientedTokens, List.length_flatMap]
  simp only [List.length_map]
  exact seven_mul_localWindows_le_sum (p13CrossHeavyWindows ctx)
    (fun _window member => p13CrossHeavyWindow_large member)

theorem p13CrossHeavyVisibleChecks_exact
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13CrossHeavyProfile ctx).visibleChecks =
      (p13CrossHeavyProfile ctx).labels.length := rfl

namespace VerifiedP13BranchExcessComponentPrefix

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

noncomputable def crossHeavyLedger
    (_prefix : VerifiedP13BranchExcessComponentPrefix ctx node21) :=
  p13CrossHeavyProfile ctx

theorem crossHeavyLedger_nodup
    (_prefix : VerifiedP13BranchExcessComponentPrefix ctx node21) :
    (p13CrossHeavyProfile ctx).labels.Nodup :=
  p13CrossHeavyLabels_nodup ctx

theorem crossHeavyLedger_lower
    (_prefix : VerifiedP13BranchExcessComponentPrefix ctx node21) :
    7 * (p13CrossHeavyWindows ctx).length ≤
      (p13CrossHeavyOrientedTokens ctx).length :=
  seven_mul_p13CrossHeavyWindows_le_orientedIncidences ctx

end VerifiedP13BranchExcessComponentPrefix

end Erdos64EG.Internal
