import Erdos64EG.Future.P13FixedSkeletonCrossHeavyLedger
import StructuralExhaustion.Core.FiniteReverseClosure

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Core.FiniteReverseClosure

universe u

abbrev P13CrossHeavyOccurrence
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Sigma fun window : P13AmbientCubicWindow ctx =>
    {entry : P13BranchExcessComponentEntry ctx //
      entry ∈ p13WindowCrossWindowEntries ctx window}

noncomputable def p13CrossHeavyOccurrences
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    List (P13CrossHeavyOccurrence ctx) :=
  (p13CrossHeavyWindows ctx).flatMap fun window =>
    (p13WindowCrossWindowEntries ctx window).attach.map fun entry =>
      ⟨window, entry⟩

def P13CrossHeavyOccurrence.token
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (occurrence : P13CrossHeavyOccurrence ctx) :
    InducedPathWindowLedger.Token ctx.G.object :=
  occurrence.2.1.source.2.stub.token

theorem crossWindowRoute_exists
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (entry : P13BranchExcessComponentEntry ctx)
    (cross : entry.tag = .crossWindow) :
    ∃ residual, entry.route = .crossWindow residual := by
  cases entry with
  | mk source route routeExact =>
      cases route with
      | component boundary boundaryExact input inputExact =>
          simp [P13BranchExcessComponentEntry.tag] at cross
      | crossWindow residual => exact ⟨residual, rfl⟩

noncomputable def P13CrossHeavyOccurrence.residual
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (occurrence : P13CrossHeavyOccurrence ctx) :
    InducedPathBranchExcessComponentEntry.CrossWindowResidual
      occurrence.2.1.source.2.stub :=
  Classical.choose (crossWindowRoute_exists occurrence.2.1
    (mem_p13WindowCrossWindowEntries_iff.mp occurrence.2.2).2)

noncomputable def P13CrossHeavyOccurrence.incidencePair
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (occurrence : P13CrossHeavyOccurrence ctx) :=
  Routes.InducedPathCrossWindowIncidencePair.route
    occurrence.2.1.source.2.stub occurrence.residual

noncomputable def P13CrossHeavyOccurrence.reverseToken
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (occurrence : P13CrossHeavyOccurrence ctx) :
    InducedPathWindowLedger.Token ctx.G.object :=
  occurrence.incidencePair.rightToken

theorem P13CrossHeavyOccurrence.reverse_ne
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (occurrence : P13CrossHeavyOccurrence ctx) :
    occurrence.reverseToken ≠ occurrence.token := by
  change occurrence.incidencePair.rightToken ≠ occurrence.token
  have leftExact : occurrence.incidencePair.leftToken = occurrence.token := by
    simpa [P13CrossHeavyOccurrence.token] using
      occurrence.incidencePair.leftTokenExact
  intro equal
  exact occurrence.incidencePair.tokensDistinct (leftExact.trans equal.symm)

def P13CrossHeavyTokenSource
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (token : InducedPathWindowLedger.Token ctx.G.object) :=
  {occurrence : P13CrossHeavyOccurrence ctx //
    occurrence ∈ p13CrossHeavyOccurrences ctx ∧ occurrence.token = token}

theorem p13CrossHeavyTokenSource_exists
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {token : InducedPathWindowLedger.Token ctx.G.object}
    (member : token ∈ p13CrossHeavyOrientedTokens ctx) :
    Nonempty (P13CrossHeavyTokenSource token) := by
  unfold p13CrossHeavyOrientedTokens at member
  rw [List.mem_flatMap] at member
  rcases member with ⟨window, windowMem, member⟩
  rw [List.mem_map] at member
  rcases member with ⟨entry, entryMem, tokenExact⟩
  let occurrence : P13CrossHeavyOccurrence ctx :=
    ⟨window, ⟨entry, entryMem⟩⟩
  refine ⟨⟨occurrence, ?_, ?_⟩⟩
  · unfold p13CrossHeavyOccurrences
    rw [List.mem_flatMap]
    refine ⟨window, windowMem, ?_⟩
    rw [List.mem_map]
    exact ⟨⟨entry, entryMem⟩, by simp, rfl⟩
  · change entry.source.2.stub.token = token
    exact tokenExact

noncomputable def p13CrossHeavyReverseToken
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (token : InducedPathWindowLedger.Token ctx.G.object) :
    InducedPathWindowLedger.Token ctx.G.object := by
  classical
  exact if source : Nonempty (P13CrossHeavyTokenSource token) then
    Classical.choice source |>.1.reverseToken
  else token

theorem p13CrossHeavyReverseToken_ne
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {token : InducedPathWindowLedger.Token ctx.G.object}
    (member : token ∈ p13CrossHeavyOrientedTokens ctx) :
    p13CrossHeavyReverseToken token ≠ token := by
  rw [p13CrossHeavyReverseToken, dif_pos (p13CrossHeavyTokenSource_exists member)]
  let source : P13CrossHeavyTokenSource token :=
    Classical.choice (p13CrossHeavyTokenSource_exists member)
  change source.1.reverseToken ≠ token
  intro equal
  exact source.1.reverse_ne (equal.trans source.2.2.symm)

noncomputable def p13CrossHeavyReverseProfile
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Profile (InducedPathWindowLedger.Token ctx.G.object)
      (InducedPathWindowLedger.Token ctx.G.object) where
  items := p13CrossHeavyOrientedTokens ctx
  nodup := p13CrossHeavyOrientedTokens_nodup ctx
  key := id
  reverse := p13CrossHeavyReverseToken
  keyDecidableEq := Classical.decEq _
  keyInjective := by intro left right _ _ equal; exact equal
  reverse_ne := by
    intro token member
    exact p13CrossHeavyReverseToken_ne member

noncomputable def runP13CrossHeavyReverseClosure
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  (p13CrossHeavyReverseProfile ctx).run

theorem p13CrossHeavyClosed_factorTwo
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13CrossHeavyReverseProfile ctx).closedItems.length ≤
      2 * (p13CrossHeavyReverseProfile ctx).pairLabels.length :=
  (p13CrossHeavyReverseProfile ctx).closedItems_le_two_mul_pairLabels

/-- Either every actual oriented token has its constructed reverse in the same
selected subschedule, or the runner retains the first concrete missing token. -/
theorem p13CrossHeavyReverseClosure_exhaustive
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (∀ token ∈ p13CrossHeavyOrientedTokens ctx,
      (p13CrossHeavyReverseProfile ctx).reversePresent token) ∨
      (∃ hit : Core.FiniteSearch.FirstHit (p13CrossHeavyOrientedTokens ctx)
        (fun token =>
          ¬ (p13CrossHeavyReverseProfile ctx).reversePresent token), True) :=
  (p13CrossHeavyReverseProfile ctx).run_exhaustive

end Erdos64EG.Internal
