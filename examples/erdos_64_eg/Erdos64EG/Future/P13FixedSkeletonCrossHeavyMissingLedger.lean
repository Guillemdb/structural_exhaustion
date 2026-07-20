import Erdos64EG.Future.P13FixedSkeletonCrossHeavyMissingReverse
import StructuralExhaustion.Core.LocalFiniteCapacity
import StructuralExhaustion.Core.LocalFibreCapacity

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathColdBranchExcess

universe u

/-! # Exact aggregate ledger for missing cross-heavy reverses -/

abbrev P13CrossHeavyMissingToken
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  {token : InducedPathWindowLedger.Token ctx.G.object //
    token ∈ (p13CrossHeavyReverseProfile ctx).missingItems}

noncomputable def P13CrossHeavyMissingToken.source
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (item : P13CrossHeavyMissingToken ctx) :
    P13CrossHeavyTokenSource item.1 :=
  Classical.choice (p13CrossHeavyTokenSource_exists
    (List.mem_of_mem_filter item.2))

noncomputable def P13CrossHeavyMissingToken.occurrence
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (item : P13CrossHeavyMissingToken ctx) : P13CrossHeavyOccurrence ctx :=
  item.source.1

theorem P13CrossHeavyMissingToken.reverseMissing
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (item : P13CrossHeavyMissingToken ctx) :
    item.occurrence.reverseToken ∉ p13CrossHeavyOrientedTokens ctx := by
  have missingPresent :
      ¬ (p13CrossHeavyReverseProfile ctx).reversePresent item.1 :=
    ((p13CrossHeavyReverseProfile ctx).mem_missingItems_iff item.1).mp item.2 |>.2
  have missingDeclared : p13CrossHeavyReverseToken item.1 ∉
      p13CrossHeavyOrientedTokens ctx := by
    simpa [Core.FiniteReverseClosure.Profile.reversePresent,
      Core.FiniteReverseClosure.Profile.keys,
      p13CrossHeavyReverseProfile] using missingPresent
  have reverseExact : p13CrossHeavyReverseToken item.1 =
      item.occurrence.reverseToken := by
    rw [p13CrossHeavyReverseToken,
      dif_pos (p13CrossHeavyTokenSource_exists
        (List.mem_of_mem_filter item.2))]
    rfl
  rwa [reverseExact] at missingDeclared

noncomputable def P13CrossHeavyMissingToken.outcome
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (item : P13CrossHeavyMissingToken ctx) :=
  resolveP13CrossHeavyMissingReverse
    (classifyP13CrossHeavyMissingReverse item.occurrence item.reverseMissing)

noncomputable def P13CrossHeavyMissingToken.isTransit
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (item : P13CrossHeavyMissingToken ctx) : Bool :=
  match item.outcome with
  | .transit _ => true
  | .ownerComponentHeavy _ _ => false

def P13CrossHeavyMissingToken.IsTransit
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (item : P13CrossHeavyMissingToken ctx) : Prop := item.isTransit = true

theorem P13CrossHeavyMissingToken.transitMember
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (item : P13CrossHeavyMissingToken ctx) (transit : item.IsTransit) :
    item.occurrence.incidencePair.rightLocalToken ∈
      (windowTokens ctx.G.object
        item.occurrence.reverseOwner.1).orderedValues.take 2 := by
  cases equation : item.outcome with
  | transit member => exact member
  | ownerComponentHeavy ownerNotCrossHeavy componentHeavy =>
      simp [P13CrossHeavyMissingToken.IsTransit,
        P13CrossHeavyMissingToken.isTransit, equation] at transit

theorem P13CrossHeavyMissingToken.nonTransit_componentHeavy
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (item : P13CrossHeavyMissingToken ctx) (notTransit : ¬ item.IsTransit) :
    item.occurrence.reverseOwner ∉ p13CrossHeavyWindows ctx ∧
      7 ≤ (p13WindowComponentEntries ctx
        item.occurrence.reverseOwner).length := by
  have isFalse : item.isTransit = false := by
    cases equation : item.isTransit
    · rfl
    · exfalso
      apply notTransit
      exact equation
  cases equation : item.outcome with
  | transit member =>
      simp [P13CrossHeavyMissingToken.isTransit, equation] at isFalse
  | ownerComponentHeavy ownerNotCrossHeavy componentHeavy =>
      exact ⟨ownerNotCrossHeavy, componentHeavy⟩

theorem P13CrossHeavyMissingToken.isTransitFalse_componentHeavy
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (item : P13CrossHeavyMissingToken ctx) (isFalse : item.isTransit = false) :
    item.occurrence.reverseOwner ∉ p13CrossHeavyWindows ctx ∧
      7 ≤ (p13WindowComponentEntries ctx
        item.occurrence.reverseOwner).length := by
  cases equation : item.outcome with
  | transit member =>
      simp [P13CrossHeavyMissingToken.isTransit, equation] at isFalse
  | ownerComponentHeavy ownerNotCrossHeavy componentHeavy =>
      exact ⟨ownerNotCrossHeavy, componentHeavy⟩

noncomputable def p13CrossHeavyMissingTokens
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    List (P13CrossHeavyMissingToken ctx) :=
  (p13CrossHeavyReverseProfile ctx).missingItems.attach

theorem p13CrossHeavyMissingTokens_nodup
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13CrossHeavyMissingTokens ctx).Nodup :=
  (p13CrossHeavyReverseProfile ctx).missingItems_nodup.attach

noncomputable def p13CrossHeavyTransitMissingTokens
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    List (P13CrossHeavyMissingToken ctx) :=
  (p13CrossHeavyMissingTokens ctx).filter fun item => item.isTransit

noncomputable def p13CrossHeavyOwnerEq
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (left right : P13AmbientCubicWindow ctx) : Bool := by
  letI : DecidableEq (P13AmbientCubicWindow ctx) :=
    (p13AmbientCubicWindows ctx).decEq
  exact decide (left = right)

theorem p13CrossHeavyOwnerEq_true
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (left right : P13AmbientCubicWindow ctx) :
    p13CrossHeavyOwnerEq left right = true ↔ left = right := by
  simp [p13CrossHeavyOwnerEq]

noncomputable def p13CrossHeavySameOwner
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (item : P13CrossHeavyMissingToken ctx)
    (owner : P13AmbientCubicWindow ctx) : Bool :=
  p13CrossHeavyOwnerEq item.occurrence.reverseOwner owner

noncomputable def p13CrossHeavyTransitOwnerProfile
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Core.LocalFibreCapacity.Profile
      (P13CrossHeavyMissingToken ctx) (P13AmbientCubicWindow ctx) where
  items := p13CrossHeavyTransitMissingTokens ctx
  itemsNodup := (p13CrossHeavyMissingTokens_nodup ctx).filter _
  owners := (p13AmbientCubicWindows ctx).orderedValues
  ownersNodup := (p13AmbientCubicWindows ctx).nodup_orderedValues
  owner item := item.occurrence.reverseOwner
  sameOwner := p13CrossHeavyOwnerEq
  sameOwner_true := p13CrossHeavyOwnerEq_true
  owner_mem := by
    intro item _member
    exact (p13AmbientCubicWindows ctx).mem_orderedValues _

noncomputable def p13CrossHeavyTransitFibre
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (owner : P13AmbientCubicWindow ctx) :
    List (P13CrossHeavyMissingToken ctx) :=
  (p13CrossHeavyTransitOwnerProfile ctx).fibre owner

noncomputable def p13CrossHeavyNonTransitMissingTokens
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    List (P13CrossHeavyMissingToken ctx) :=
  (p13CrossHeavyMissingTokens ctx).filter fun item => !item.isTransit

theorem p13CrossHeavyMissing_partition
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13CrossHeavyTransitMissingTokens ctx).length +
      (p13CrossHeavyNonTransitMissingTokens ctx).length =
        (p13CrossHeavyMissingTokens ctx).length := by
  exact Core.LocalBinaryMajority.bool_filter_partition_length
    (p13CrossHeavyMissingTokens ctx) fun item => item.isTransit

theorem p13CrossHeavyNonTransitMissingToken_componentHeavy
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {item : P13CrossHeavyMissingToken ctx}
    (member : item ∈ p13CrossHeavyNonTransitMissingTokens ctx) :
    item.occurrence.reverseOwner ∉ p13CrossHeavyWindows ctx ∧
      7 ≤ (p13WindowComponentEntries ctx
        item.occurrence.reverseOwner).length := by
  rw [p13CrossHeavyNonTransitMissingTokens, List.mem_filter] at member
  apply item.isTransitFalse_componentHeavy
  simpa using member.2

noncomputable def p13CrossHeavyTransitCapacityTokens
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (owner : P13AmbientCubicWindow ctx) :
    List (InducedPathWindowLedger.Token ctx.G.object) :=
  ((windowTokens ctx.G.object owner.1).orderedValues.take 2).map toToken

theorem p13CrossHeavyTransitCapacityTokens_length_le_two
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (owner : P13AmbientCubicWindow ctx) :
    (p13CrossHeavyTransitCapacityTokens ctx owner).length ≤ 2 := by
  rw [p13CrossHeavyTransitCapacityTokens, List.length_map]
  exact Core.LocalPrefixTail.prefix_length_le _ 2

noncomputable def p13CrossHeavyTransitFibreReverseTokens
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (owner : P13AmbientCubicWindow ctx) :
    List (InducedPathWindowLedger.Token ctx.G.object) :=
  (p13CrossHeavyTransitFibre ctx owner).map fun item =>
    item.occurrence.reverseToken

theorem p13CrossHeavyTransitFibreReverseTokens_nodup
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (owner : P13AmbientCubicWindow ctx) :
    (p13CrossHeavyTransitFibreReverseTokens ctx owner).Nodup := by
  unfold p13CrossHeavyTransitFibreReverseTokens
  apply List.Nodup.map_on
  · intro left leftMember right rightMember reverseEqual
    apply Subtype.ext
    have pairLeftEqual :=
      Routes.InducedPathCrossWindowIncidencePair.leftToken_eq_of_rightToken_eq
        left.occurrence.incidencePair right.occurrence.incidencePair reverseEqual
    have occurrenceTokenEqual : left.occurrence.token = right.occurrence.token := by
      calc
        left.occurrence.token = left.occurrence.incidencePair.leftToken := by
          simpa [P13CrossHeavyOccurrence.token] using
            left.occurrence.incidencePair.leftTokenExact.symm
        _ = right.occurrence.incidencePair.leftToken := pairLeftEqual
        _ = right.occurrence.token := by
          simpa [P13CrossHeavyOccurrence.token] using
            right.occurrence.incidencePair.leftTokenExact
    exact left.source.2.2.symm.trans
      (occurrenceTokenEqual.trans right.source.2.2)
  · exact (p13CrossHeavyTransitOwnerProfile ctx).fibre_nodup owner

theorem p13CrossHeavyTransitFibreReverseToken_mem_capacity
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (owner : P13AmbientCubicWindow ctx)
    (item : P13CrossHeavyMissingToken ctx)
    (member : item ∈ p13CrossHeavyTransitFibre ctx owner) :
    item.occurrence.reverseToken ∈
      p13CrossHeavyTransitCapacityTokens ctx owner := by
  rw [p13CrossHeavyTransitFibre,
    Core.LocalFibreCapacity.Profile.fibre, List.mem_filter] at member
  have ownerExact : item.occurrence.reverseOwner = owner :=
    (p13CrossHeavyOwnerEq_true _ _).mp member.2
  have transitListMember : item ∈ p13CrossHeavyTransitMissingTokens ctx := by
    simpa [p13CrossHeavyTransitOwnerProfile] using member.1
  rw [p13CrossHeavyTransitMissingTokens, List.mem_filter] at transitListMember
  have transit : item.IsTransit := transitListMember.2
  have localMember := item.transitMember transit
  subst owner
  rw [p13CrossHeavyTransitCapacityTokens, List.mem_map]
  exact ⟨item.occurrence.incidencePair.rightLocalToken, localMember,
    item.occurrence.incidencePair.rightTokenExact.symm⟩

theorem p13CrossHeavyTransitFibre_length_le_two
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (owner : P13AmbientCubicWindow ctx) :
    (p13CrossHeavyTransitFibre ctx owner).length ≤ 2 := by
  classical
  have labelsBound :
      (p13CrossHeavyTransitFibreReverseTokens ctx owner).length ≤
        (p13CrossHeavyTransitCapacityTokens ctx owner).length := by
    apply Core.LocalFiniteCapacity.nodup_length_le_of_mem
      (p13CrossHeavyTransitFibreReverseTokens_nodup ctx owner)
    intro token tokenMember
    rw [p13CrossHeavyTransitFibreReverseTokens, List.mem_map] at tokenMember
    rcases tokenMember with ⟨item, itemMember, rfl⟩
    exact p13CrossHeavyTransitFibreReverseToken_mem_capacity owner item itemMember
  rw [p13CrossHeavyTransitFibreReverseTokens, List.length_map] at labelsBound
  exact labelsBound.trans
    (p13CrossHeavyTransitCapacityTokens_length_le_two ctx owner)

theorem p13CrossHeavyTransitMissingTokens_global_bound
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13CrossHeavyTransitMissingTokens ctx).length ≤
      2 * (p13AmbientCubicWindows ctx).card := by
  have aggregate :=
    (p13CrossHeavyTransitOwnerProfile ctx).items_length_le_mul_owners_length 2
      (fun owner _ownerMember => by
        simpa [p13CrossHeavyTransitFibre] using
          p13CrossHeavyTransitFibre_length_le_two ctx owner)
  simpa [p13CrossHeavyTransitOwnerProfile,
    FinEnum.orderedValues_length] using aggregate

end Erdos64EG.Internal
