import Erdos64EG.P13FixedSkeletonCrossHeavyReverseClosure
import StructuralExhaustion.Core.LocalPrefixTail

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathColdBranchExcess

universe u

/-!
# Exact consumer for a missing cross-heavy reverse

The reverse incidence is first located in its destination owner's literal
fifteen-token order.  The first two positions are retained as transit.  In the
remaining thirteen positions, either the owner is not cross-heavy, which
forces the local component-heavy alternative, or the precise local selection
mismatch is retained.  No reverse-closure assumption is used.
-/

noncomputable def P13CrossHeavyOccurrence.reverseOwner
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (occurrence : P13CrossHeavyOccurrence ctx) : P13AmbientCubicWindow ctx :=
  ⟨occurrence.incidencePair.rightSlot.window,
    occurrence.incidencePair.rightSlot.cubic⟩

inductive P13CrossHeavyMissingReverseOutcome
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (occurrence : P13CrossHeavyOccurrence ctx)
    (missing : occurrence.reverseToken ∉ p13CrossHeavyOrientedTokens ctx) :
    Type (u + 1) where
  | transit
      (member : occurrence.incidencePair.rightLocalToken ∈
        (windowTokens ctx.G.object occurrence.reverseOwner.1).orderedValues.take 2)
  | ownerComponentHeavy
      (ownerNotCrossHeavy :
        occurrence.reverseOwner ∉ p13CrossHeavyWindows ctx)
      (componentHeavy :
        7 ≤ (p13WindowComponentEntries ctx occurrence.reverseOwner).length)
  | selectionMismatch
      (ownerCrossHeavy : occurrence.reverseOwner ∈ p13CrossHeavyWindows ctx)
      (branchExcess : occurrence.incidencePair.rightLocalToken ∈
        branchExcessTokens ctx.G.object occurrence.reverseOwner.1)
      (reverseMissing :
        occurrence.reverseToken ∉ p13CrossHeavyOrientedTokens ctx)

noncomputable def classifyP13CrossHeavyMissingReverse
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (occurrence : P13CrossHeavyOccurrence ctx)
    (missing : occurrence.reverseToken ∉ p13CrossHeavyOrientedTokens ctx) :
    P13CrossHeavyMissingReverseOutcome occurrence missing := by
  let schedule :=
    (windowTokens ctx.G.object occurrence.reverseOwner.1).orderedValues
  have fullMember : occurrence.incidencePair.rightLocalToken ∈ schedule :=
    (windowTokens ctx.G.object occurrence.reverseOwner.1).mem_orderedValues _
  cases Core.LocalPrefixTail.run schedule 2
      occurrence.incidencePair.rightLocalToken fullMember with
  | inPrefix member =>
      exact .transit member
  | inTail member =>
      have branchExcess : occurrence.incidencePair.rightLocalToken ∈
          branchExcessTokens ctx.G.object occurrence.reverseOwner.1 := by
        exact member
      by_cases ownerCrossHeavy :
          occurrence.reverseOwner ∈ p13CrossHeavyWindows ctx
      · exact .selectionMismatch ownerCrossHeavy branchExcess missing
      · have componentHeavy :
            7 ≤ (p13WindowComponentEntries ctx occurrence.reverseOwner).length := by
          rcases p13WindowComponentCrossWindowMajority_exhaustive ctx
              occurrence.reverseOwner with componentHeavy | crossHeavy
          · exact componentHeavy
          · exfalso
            apply ownerCrossHeavy
            rw [p13CrossHeavyWindows, List.mem_filter]
            exact ⟨(p13AmbientCubicWindows ctx).mem_orderedValues _,
              decide_eq_true crossHeavy⟩
        exact P13CrossHeavyMissingReverseOutcome.ownerComponentHeavy
          ownerCrossHeavy componentHeavy

theorem p13CrossHeavyTransitCapacity
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (occurrence : P13CrossHeavyOccurrence ctx) :
    ((windowTokens ctx.G.object occurrence.reverseOwner.1).orderedValues.take 2).length ≤
      2 :=
  Core.LocalPrefixTail.prefix_length_le _ 2

/-- A reverse token in the destination owner's branch-excess tail is selected
by the cross-window ledger whenever that owner is cross-heavy. -/
theorem p13CrossHeavyBranchExcessReverse_mem
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (occurrence : P13CrossHeavyOccurrence ctx)
    (ownerCrossHeavy : occurrence.reverseOwner ∈ p13CrossHeavyWindows ctx)
    (branchExcess : occurrence.incidencePair.rightLocalToken ∈
      branchExcessTokens ctx.G.object occurrence.reverseOwner.1) :
    occurrence.reverseToken ∈ p13CrossHeavyOrientedTokens ctx := by
  classical
  let reverseStub : InducedPathColdCorridor.CubicStub ctx.G.object :=
    toCubicStub occurrence.reverseOwner.2
      occurrence.incidencePair.rightLocalToken
  have reverseStubSelected : reverseStub ∈
      branchExcessStubs ctx.G.object occurrence.reverseOwner.1
        occurrence.reverseOwner.2 := by
    rw [branchExcessStubs, List.mem_map]
    exact ⟨occurrence.incidencePair.rightLocalToken, branchExcess, rfl⟩
  let reverseCorridor : P13BranchExcessCorridor ctx occurrence.reverseOwner := {
    stub := reverseStub
    selected := reverseStubSelected
    result := InducedPathColdCorridor.runFirstFailure
      (p13SelectedWindowCorridorProducer ctx)
      PowerOfTwoLength powerOfTwoLengthDecidable reverseStub
    resultExact := rfl
  }
  have reverseCorridorMember : reverseCorridor ∈
      p13WindowBranchExcessCorridors ctx occurrence.reverseOwner := by
    unfold p13WindowBranchExcessCorridors
    rw [List.mem_map]
    exact ⟨⟨reverseStub, reverseStubSelected⟩, by simp, rfl⟩
  have endpointDeleted : reverseStub.neighbor ∈
      InducedPathColdSkeleton.deletedWindowVertices ctx.G.object := by
    change occurrence.incidencePair.rightLocalToken.2.1 ∈
      InducedPathColdSkeleton.deletedWindowVertices ctx.G.object
    rw [occurrence.incidencePair.rightLocalTokenNeighbor]
    simp only [InducedPathColdSkeleton.deletedWindowVertices,
      Finset.mem_biUnion]
    refine ⟨occurrence.2.1.source.2.stub.window, Finset.mem_univ _, ?_⟩
    simp [occurrence.2.1.source.2.stub.cubic,
      InducedPathPacking.mem_support_iff]
  obtain ⟨reverseResidual, reverseRouteExact⟩ :=
    InducedPathBranchExcessComponentEntry.route_crossWindow_of_endpointDeleted
      (p13SelectedWindowCorridorProducer ctx) reverseStub endpointDeleted
  let reverseEntry : P13BranchExcessComponentEntry ctx := {
    source := ⟨occurrence.reverseOwner, reverseCorridor⟩
    route := InducedPathBranchExcessComponentEntry.route
      (p13SelectedWindowCorridorProducer ctx) reverseStub
    routeExact := rfl
  }
  have reverseEntryMember : reverseEntry ∈
      p13WindowBranchExcessComponentEntries ctx occurrence.reverseOwner := by
    unfold p13WindowBranchExcessComponentEntries
    rw [List.mem_map]
    exact ⟨reverseCorridor, reverseCorridorMember, rfl⟩
  have reverseEntryCross : reverseEntry.tag = .crossWindow :=
    reverseEntry.tag_crossWindow_of_route_eq reverseRouteExact
  unfold p13CrossHeavyOrientedTokens
  rw [List.mem_flatMap]
  refine ⟨occurrence.reverseOwner, ownerCrossHeavy, ?_⟩
  rw [List.mem_map]
  refine ⟨reverseEntry,
    mem_p13WindowCrossWindowEntries_iff.mpr
      ⟨reverseEntryMember, reverseEntryCross⟩, ?_⟩
  change reverseStub.token = occurrence.reverseToken
  change toToken occurrence.incidencePair.rightLocalToken =
    occurrence.incidencePair.rightToken
  exact occurrence.incidencePair.rightTokenExact.symm

/-- After the exact local selection-equivalence proof, a missing reverse has
only the transit and non-cross-heavy/component-heavy outcomes. -/
inductive P13CrossHeavyResolvedMissingReverseOutcome
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (occurrence : P13CrossHeavyOccurrence ctx)
    (missing : occurrence.reverseToken ∉ p13CrossHeavyOrientedTokens ctx) :
    Type (u + 1) where
  | transit
      (member : occurrence.incidencePair.rightLocalToken ∈
        (windowTokens ctx.G.object occurrence.reverseOwner.1).orderedValues.take 2)
  | ownerComponentHeavy
      (ownerNotCrossHeavy : occurrence.reverseOwner ∉ p13CrossHeavyWindows ctx)
      (componentHeavy :
        7 ≤ (p13WindowComponentEntries ctx occurrence.reverseOwner).length)

noncomputable def resolveP13CrossHeavyMissingReverse
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {occurrence : P13CrossHeavyOccurrence ctx}
    {missing : occurrence.reverseToken ∉ p13CrossHeavyOrientedTokens ctx}
    (outcome : P13CrossHeavyMissingReverseOutcome occurrence missing) :
    P13CrossHeavyResolvedMissingReverseOutcome occurrence missing := by
  cases outcome with
  | transit member => exact .transit member
  | ownerComponentHeavy ownerNotCrossHeavy componentHeavy =>
      exact .ownerComponentHeavy ownerNotCrossHeavy componentHeavy
  | selectionMismatch ownerCrossHeavy branchExcess reverseMissing =>
      exact False.elim (reverseMissing
        (p13CrossHeavyBranchExcessReverse_mem occurrence
          ownerCrossHeavy branchExcess))

noncomputable def p13CrossHeavyFirstMissingSource
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (hit : Core.FiniteSearch.FirstHit (p13CrossHeavyOrientedTokens ctx)
      (fun token =>
        ¬ (p13CrossHeavyReverseProfile ctx).reversePresent token)) :
    P13CrossHeavyTokenSource hit.value :=
  Classical.choice (p13CrossHeavyTokenSource_exists hit.member)

theorem p13CrossHeavyFirstMissing_exact
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (hit : Core.FiniteSearch.FirstHit (p13CrossHeavyOrientedTokens ctx)
      (fun token =>
        ¬ (p13CrossHeavyReverseProfile ctx).reversePresent token)) :
    (p13CrossHeavyFirstMissingSource hit).1.reverseToken ∉
      p13CrossHeavyOrientedTokens ctx := by
  have missingDeclared : p13CrossHeavyReverseToken hit.value ∉
      p13CrossHeavyOrientedTokens ctx := by
    simpa [Core.FiniteReverseClosure.Profile.reversePresent,
      Core.FiniteReverseClosure.Profile.keys,
      p13CrossHeavyReverseProfile] using hit.holds
  have reverseExact : p13CrossHeavyReverseToken hit.value =
      (p13CrossHeavyFirstMissingSource hit).1.reverseToken := by
    rw [p13CrossHeavyReverseToken,
      dif_pos (p13CrossHeavyTokenSource_exists hit.member)]
    rfl
  rwa [reverseExact] at missingDeclared

noncomputable def consumeP13CrossHeavyFirstMissing
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (hit : Core.FiniteSearch.FirstHit (p13CrossHeavyOrientedTokens ctx)
      (fun token =>
        ¬ (p13CrossHeavyReverseProfile ctx).reversePresent token)) :=
  resolveP13CrossHeavyMissingReverse
    (classifyP13CrossHeavyMissingReverse
      (p13CrossHeavyFirstMissingSource hit).1
      (p13CrossHeavyFirstMissing_exact hit))

end Erdos64EG.Internal
