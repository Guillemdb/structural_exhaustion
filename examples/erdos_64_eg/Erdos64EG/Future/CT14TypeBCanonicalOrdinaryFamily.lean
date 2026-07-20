import Erdos64EG.Future.CT14TypeBGlobalFanMass
import Erdos64EG.Future.P13NegativeSupportLocalization

namespace Erdos64EG.Internal.Node84GlobalFanMass.CanonicalOrdinary

open StructuralExhaustion
open scoped BigOperators

set_option maxHeartbeats 800000

universe u

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

/-!
# Canonical ordinary family on the original node-[84] edge

The support universe is obtained by filtering the one graph-owned ordered
component decomposition.  A component enters this node only on the exact
degree-four, negative, center-deleted-unsaturated branch.  Thus the coefficient
bound is derived from the unconditional high-center deletion theorem; it is
not a field supplied by a caller.
-/

noncomputable def emptyReserve :
    Graph.RefinedFanLedger.Reserve ctx.G.Vertex where
  VertexUsed := fun _ => False
  vertexUsedDecidable := fun _ => isFalse (fun impossible => impossible)
  IncidenceUsed := fun _ => False
  incidenceUsedDecidable := fun _ => isFalse (fun impossible => impossible)

/-- The literal assigned scope of one canonical remainder component.  The
ordinary producer uses no decorative external carrier and does not manufacture
a fan certificate. -/
noncomputable def scope
    (index : P13NegativeSupportLocalization.Canonical.ComponentIndex ctx) :
    TypeBSupportScope ctx where
  vertices := (P13NegativeSupportLocalization.Canonical.cell ctx index).core
  assignedCarriers := ∅
  reserve := emptyReserve
  assignedMarkedFan := fun _ => none

/-- Exact component-index enumeration inherited from the canonical component
order. -/
@[implicit_reducible]
noncomputable def componentIndices : FinEnum
    (P13NegativeSupportLocalization.Canonical.ComponentIndex ctx) := by
  let collection := P13NegativeSupportLocalization.Canonical.componentIndices ctx
  exact @FinEnum.ofNodupList _ collection.decEq collection.values
    (by
      intro index
      simpa [collection,
        P13NegativeSupportLocalization.Canonical.componentIndices] using index.2)
    collection.nodup

/-- These are exactly the ordinary canonical supports whose branch reaches
node `[84]`: negative charge, no center above degree four, and no remaining
Type-A receiver overload. -/
def Eligible
    (index : P13NegativeSupportLocalization.Canonical.ComponentIndex ctx) : Prop :=
  let sc := scope index
  sc.highCenterChargeProfile.netQuarterCharge < 0 ∧
    sc.NoHigherCenter ∧ sc.CenterDeletedUnsaturated

private abbrev EligibleIndex :=
  {index : P13NegativeSupportLocalization.Canonical.ComponentIndex ctx //
    Eligible index}

/-- Proof-carrying canonical ordinary support.  Keeping the three branch
proofs as fields prevents elaboration from repeatedly normalizing the large
receiver-unsaturation predicate. -/
structure Family where
  index : P13NegativeSupportLocalization.Canonical.ComponentIndex ctx
  negative : (scope index).highCenterChargeProfile.netQuarterCharge < 0
  noHigherProof : (scope index).NoHigherCenter
  unsaturatedProof : (scope index).CenterDeletedUnsaturated

private def familyEquiv : Family (ctx := ctx) ≃ EligibleIndex (ctx := ctx) where
  toFun member :=
    ⟨member.index, member.negative, member.noHigherProof, member.unsaturatedProof⟩
  invFun member :=
    ⟨member.1, member.2.1, member.2.2.1, member.2.2.2⟩
  left_inv := by intro member; cases member; rfl
  right_inv := by intro member; apply Subtype.ext; rfl

theorem family_index_injective :
    Function.Injective (fun member : Family (ctx := ctx) => member.index) := by
  intro left right equal
  cases left with
  | mk leftIndex leftNegative leftNoHigher leftUnsaturated =>
      cases right with
      | mk rightIndex rightNegative rightNoHigher rightUnsaturated =>
          cases equal
          rfl

@[implicit_reducible]
noncomputable def family : FinEnum (Family (ctx := ctx)) :=
  letI : FinEnum (EligibleIndex (ctx := ctx)) :=
    Core.Enumeration.subtype componentIndices Eligible
      (fun _ => Classical.propDecidable _)
  FinEnum.ofEquiv (EligibleIndex (ctx := ctx)) familyEquiv

theorem family_covers_exact
    (index : P13NegativeSupportLocalization.Canonical.ComponentIndex ctx)
    (eligible : Eligible index) :
    ∃ member : Family (ctx := ctx), member.index = index :=
  ⟨⟨index, eligible.1, eligible.2.1, eligible.2.2⟩, rfl⟩

def noHigher (member : Family (ctx := ctx)) :
    (scope member.index).NoHigherCenter :=
  member.noHigherProof

def unsaturated (member : Family (ctx := ctx)) :
    (scope member.index).CenterDeletedUnsaturated :=
  member.unsaturatedProof

/-- Exact local node-[84] source attached to one canonical ordinary support. -/
noncomputable def source
    (node84 : VerifiedTypeBLocalFanMassPrefix ctx)
    (member : Family (ctx := ctx)) : OrdinarySupportSource node84 where
  scope := scope member.index
  noHigher := noHigher member
  route := (typeBLocalFanMassFacts node84).route
    (scope member.index) (noHigher member)
  routeExact := rfl

/-- One occurrence for each literal high center of each retained canonical
ordinary support. -/
abbrev Occurrence :=
  Σ member : Family (ctx := ctx), (scope member.index).Center

@[implicit_reducible]
noncomputable def occurrences : FinEnum (Occurrence (ctx := ctx)) := by
  letI : FinEnum (Family (ctx := ctx)) := family
  letI : ∀ member : Family (ctx := ctx),
      FinEnum (scope member.index).Center := fun member => (scope member.index).centers
  exact inferInstance

theorem occurrence_center_injective_within_ordinary :
    Function.Injective (fun occurrence : Occurrence (ctx := ctx) =>
      (Graph.SupportIndexedFanMass.Role.ordinary, occurrence.2.1)) := by
  rintro ⟨leftMember, leftCenter⟩ ⟨rightMember, rightCenter⟩ equal
  have centerEqual : leftCenter.1 = rightCenter.1 := congrArg Prod.snd equal
  have leftCore : leftCenter.1 ∈
      (P13NegativeSupportLocalization.Canonical.cell ctx leftMember.index).core := by
    exact (scope leftMember.index).center_mem_vertices leftCenter
  have rightCore : leftCenter.1 ∈
      (P13NegativeSupportLocalization.Canonical.cell ctx rightMember.index).core := by
    rw [centerEqual]
    exact (scope rightMember.index).center_mem_vertices rightCenter
  have indexEqual : leftMember.index = rightMember.index := by
    apply Subtype.ext
    by_contra different
    have disjoint := Graph.OrderedSupportComponents.disjoint_vertices
      ctx.G.object (p13RemainderVertices ctx) different
    exact (Finset.disjoint_left.mp disjoint) leftCore rightCore
  have familyEqual : leftMember = rightMember := family_index_injective indexEqual
  subst rightMember
  have centerSubtypeEqual : leftCenter = rightCenter := Subtype.ext centerEqual
  subst rightCenter
  rfl

theorem exists_occurrence_of_eligible_component
    (index : P13NegativeSupportLocalization.Canonical.ComponentIndex ctx)
    (eligible : Eligible index) (vertex : ctx.G.Vertex)
    (vertexMem : vertex ∈
      (P13NegativeSupportLocalization.Canonical.cell ctx index).core)
    (high : 4 ≤ ctx.G.object.degree vertex) :
    ∃ occurrence : Occurrence (ctx := ctx),
      occurrence.1.index = index ∧ occurrence.2.1 = vertex := by
  let member : Family (ctx := ctx) :=
    ⟨index, eligible.1, eligible.2.1, eligible.2.2⟩
  have remainderMem : vertex ∈ p13RemainderVertices ctx :=
    (P13NegativeSupportLocalization.Canonical.cell ctx index).core_subset_remainder
      vertexMem
  have coreMem : vertex ∈ (scope index).coreVertices := by
    classical
    simp [TypeBSupportScope.coreVertices, scope, vertexMem, remainderMem]
  have highCenterMem : vertex ∈ (scope index).highCenters := by
    classical
    simp [TypeBSupportScope.highCenters, coreMem, high]
  let center : (scope member.index).Center := ⟨vertex, highCenterMem⟩
  exact ⟨⟨member, center⟩, rfl, rfl⟩

theorem occurrence_has_exact_source
    (node84 : VerifiedTypeBLocalFanMassPrefix ctx)
    (occurrence : Occurrence (ctx := ctx)) :
    (source node84 occurrence.1).scope = scope occurrence.1.index ∧
      occurrence.2.1 ∈ (source node84 occurrence.1).scope.highCenters :=
  ⟨rfl, occurrence.2.2⟩

theorem deficit_le_208_mul_assignedSurplus
    (node84 : VerifiedTypeBLocalFanMassPrefix ctx)
    (member : Family (ctx := ctx)) :
    (source node84 member).noMinus ≤
      208 * (scope member.index).highCenterChargeProfile.assignedSurplus := by
  let sc := scope member.index
  have bound :=
    sc.neg_netQuarterCharge_le_twentyOne_mul_surplus_of_centerDeletedUnsaturated
      (unsaturated member)
  have negative : sc.highCenterChargeProfile.netQuarterCharge < 0 := member.negative
  unfold OrdinarySupportSource.noMinus source
  change Int.toNat (-sc.highCenterChargeProfile.netQuarterCharge) ≤ _
  have castEq :
      (Int.toNat (-sc.highCenterChargeProfile.netQuarterCharge) : Int) =
        -sc.highCenterChargeProfile.netQuarterCharge :=
    Int.toNat_of_nonneg (by omega)
  exact_mod_cast (show
    (Int.toNat (-sc.highCenterChargeProfile.netQuarterCharge) : Int) ≤
      208 * (sc.highCenterChargeProfile.assignedSurplus : Int) by
        rw [castEq]
        omega)

end Erdos64EG.Internal.Node84GlobalFanMass.CanonicalOrdinary
