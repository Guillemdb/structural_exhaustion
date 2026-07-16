import StructuralExhaustion.Core.FinitePredicateAlignment
import StructuralExhaustion.CT10.ExhaustiveClassification
import StructuralExhaustion.Graph.SurplusPatternCoarseRouting

namespace StructuralExhaustion.Graph.SurplusPatternSemanticBottleneck

open StructuralExhaustion

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (activation : SurplusPortActivation.VerifiedActivatedStage input ctx setup)

namespace Coarse
export SurplusPatternCoarseRouting
  (Routed HomogeneousAudit VerifiedCollision windowPortAttached
    AttachmentAlignment canonicalGermResidual SemanticBottleneckTrigger)
end Coarse

variable {windowSize remainderSize primitiveSize : Nat}
variable {routed : Coarse.Routed activation windowSize remainderSize primitiveSize}
variable {homogeneous : Coarse.HomogeneousAudit activation
  windowSize remainderSize primitiveSize routed}

abbrev Collision
    (activation : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    {windowSize remainderSize primitiveSize : Nat}
    {routed : Coarse.Routed activation windowSize remainderSize primitiveSize}
    (homogeneous : Coarse.HomogeneousAudit activation
      windowSize remainderSize primitiveSize routed) :=
  Coarse.VerifiedCollision activation homogeneous

/-! ## Exact retained attachment-coordinate universe -/

abbrev AttachmentCoordinate {V : Type u} (object : FiniteObject V) :=
  InducedPathWindowLedger.WindowIndex object ×
    (Fin 13 × (Bool × SurplusPortActivation.PortRole))

@[implicit_reducible]
def portRoles : FinEnum SurplusPortActivation.PortRole :=
  FinEnum.ofList SurplusPortActivation.portRoles
    SurplusPortActivation.mem_portRoles

@[implicit_reducible]
noncomputable def attachmentCoordinates {V : Type u} (object : FiniteObject V) :
    FinEnum (AttachmentCoordinate object) :=
  Core.Enumeration.prod
    (InducedPathWindowLedger.windowIndices object)
    (Core.Enumeration.prod (inferInstance : FinEnum (Fin 13))
      (Core.Enumeration.prod Core.Enumeration.bool portRoles))

@[simp] theorem attachmentCoordinates_card {V : Type u} (object : FiniteObject V) :
    (attachmentCoordinates object).card =
      78 * InducedPathWindowLedger.packingNumber object := by
  letI : FinEnum (InducedPathWindowLedger.WindowIndex object) :=
    InducedPathWindowLedger.windowIndices object
  letI : FinEnum SurplusPortActivation.PortRole := portRoles
  letI : FinEnum (AttachmentCoordinate object) := attachmentCoordinates object
  rw [FinEnum.card_eq_fintypeCard, Fintype.card_prod,
    Fintype.card_prod, Fintype.card_prod]
  rw [← FinEnum.card_eq_fintypeCard,
    InducedPathWindowLedger.windowIndex_card_eq_packingNumber]
  have roleCard : Fintype.card SurplusPortActivation.PortRole = 3 := by
    rw [← FinEnum.card_eq_fintypeCard]
    rfl
  rw [roleCard]
  rw [Fintype.card_fin, Fintype.card_bool]
  omega

noncomputable def alignmentProfile (collision : Collision activation homogeneous) :
    Core.FinitePredicateAlignment.Profile where
  Coordinate := AttachmentCoordinate ctx.G.object
  coordinates := attachmentCoordinates ctx.G.object
  left := fun coordinate =>
    collision.attachments.firstMap coordinate.1 coordinate.2.1
      coordinate.2.2.1 coordinate.2.2.2
  right := fun coordinate =>
    collision.attachments.secondMap coordinate.1 coordinate.2.1
      coordinate.2.2.1 coordinate.2.2.2
  leftDecidable := fun coordinate => by
    rw [collision.attachments.first_exact]
    unfold Coarse.windowPortAttached
    exact ctx.G.object.input.decideAdj _ _
  rightDecidable := fun coordinate => by
    rw [collision.attachments.second_exact]
    unfold Coarse.windowPortAttached
    exact ctx.G.object.input.decideAdj _ _

theorem aligned_exact (collision : Collision activation homogeneous)
    (exact : ∀ coordinate : (alignmentProfile activation collision).Coordinate,
      (alignmentProfile activation collision).left coordinate ↔
        (alignmentProfile activation collision).right coordinate) :
    Coarse.AttachmentAlignment activation collision := by
  intro window position first role
  exact exact ⟨window, position, first, role⟩

/-! ## Five honest residual leaves

The four aligned tags only expose the already retained canonical tree-path
comparison.  They do not assert a sparse exit, CT3 compression, Type-B
structure, or fixed-cap closure. -/

inductive GermShape
  | leftPrefix
  | rightPrefix
  | divergeAtRoot
  | divergeAfterEdge
  deriving DecidableEq, Repr

noncomputable def germShape
    (collision : Collision activation homogeneous) : GermShape :=
  match (Coarse.canonicalGermResidual activation collision).germs.comparison with
  | .leftPrefix .. => .leftPrefix
  | .rightPrefix .. => .rightPrefix
  | .divergeAtRoot .. => .divergeAtRoot
  | .divergeAfterEdge .. => .divergeAfterEdge

inductive ResidualTag
  | attachmentMismatch
  | alignedLeftPrefix
  | alignedRightPrefix
  | alignedRootDivergence
  | alignedAfterEdgeDivergence
  deriving DecidableEq, Repr

def residualTags : List ResidualTag :=
  [.attachmentMismatch, .alignedLeftPrefix, .alignedRightPrefix,
    .alignedRootDivergence, .alignedAfterEdgeDivergence]

theorem mem_residualTags (tag : ResidualTag) : tag ∈ residualTags := by
  cases tag <;> simp [residualTags]

@[implicit_reducible]
def residualTagEnum : FinEnum ResidualTag :=
  FinEnum.ofList residualTags mem_residualTags

@[simp] theorem residualTagEnum_card : residualTagEnum.card = 5 := rfl

def Evidence (collision : Collision activation homogeneous)
    (trigger : Coarse.SemanticBottleneckTrigger activation collision) :
    ResidualTag → Prop
  | .attachmentMismatch =>
      ∃ hit : Core.FiniteSearch.FirstHit
          (alignmentProfile activation collision).coordinates.orderedValues
          (alignmentProfile activation collision).Mismatch,
        (alignmentProfile activation collision).Mismatch hit.value
  | .alignedLeftPrefix =>
      Coarse.AttachmentAlignment activation collision ∧
        germShape activation collision = .leftPrefix
  | .alignedRightPrefix =>
      Coarse.AttachmentAlignment activation collision ∧
        germShape activation collision = .rightPrefix
  | .alignedRootDivergence =>
      Coarse.AttachmentAlignment activation collision ∧
        germShape activation collision = .divergeAtRoot
  | .alignedAfterEdgeDivergence =>
      Coarse.AttachmentAlignment activation collision ∧
        germShape activation collision = .divergeAfterEdge

structure Residual (collision : Collision activation homogeneous)
    (trigger : Coarse.SemanticBottleneckTrigger activation collision) where
  source : Coarse.SemanticBottleneckTrigger activation collision
  source_exact : source = trigger
  tag : ResidualTag
  evidence : Evidence activation collision trigger tag

noncomputable def classify (collision : Collision activation homogeneous)
    (trigger : Coarse.SemanticBottleneckTrigger activation collision) :
    Residual activation collision trigger := by
  cases decision : (alignmentProfile activation collision).decide with
  | mismatch hit =>
      exact ⟨trigger, rfl, .attachmentMismatch, hit, hit.holds⟩
  | aligned exact =>
      have alignment := aligned_exact activation collision exact
      cases comparison :
          (Coarse.canonicalGermResidual activation collision).germs.comparison with
      | leftPrefix =>
          exact ⟨trigger, rfl, .alignedLeftPrefix, alignment,
            by simp [germShape, comparison]⟩
      | rightPrefix =>
          exact ⟨trigger, rfl, .alignedRightPrefix, alignment,
            by simp [germShape, comparison]⟩
      | divergeAtRoot =>
          exact ⟨trigger, rfl, .alignedRootDivergence, alignment,
            by simp [germShape, comparison]⟩
      | divergeAfterEdge =>
          exact ⟨trigger, rfl, .alignedAfterEdgeDivergence, alignment,
            by simp [germShape, comparison]⟩

theorem classify_source_exact (collision : Collision activation homogeneous)
    (trigger : Coarse.SemanticBottleneckTrigger activation collision) :
    (classify activation collision trigger).source = trigger :=
  (classify activation collision trigger).source_exact

theorem classify_total (collision : Collision activation homogeneous)
    (trigger : Coarse.SemanticBottleneckTrigger activation collision) :
    ∃ tag, Evidence activation collision trigger tag :=
  ⟨(classify activation collision trigger).tag,
    (classify activation collision trigger).evidence⟩

/-! ## CT10 exhaustive finite residual table -/

noncomputable def ct10Profile (collision : Collision activation homogeneous)
    (trigger : Coarse.SemanticBottleneckTrigger activation collision) :
    CT10.ExhaustiveClassification.Profile ResidualTag :=
  CT10.ExhaustiveClassification.Profile.exactSelection residualTagEnum
    (classify activation collision trigger).tag

noncomputable def ct10Run (collision : Collision activation homogeneous)
    (trigger : Coarse.SemanticBottleneckTrigger activation collision) :=
  (ct10Profile activation collision trigger).run ctx.toBranchContext

theorem ct10Run_terminal (collision : Collision activation homogeneous)
    (trigger : Coarse.SemanticBottleneckTrigger activation collision) :
    (ct10Run activation collision trigger).terminal = .exhaustive :=
  (ct10Profile activation collision trigger).run_terminal_exhaustive
    ctx.toBranchContext

theorem ct10Run_trace (collision : Collision activation homogeneous)
    (trigger : Coarse.SemanticBottleneckTrigger activation collision) :
    (ct10Run activation collision trigger).trace =
      [.entry, .table, .direct, .missing, .exhaustiveTerminal] :=
  (ct10Profile activation collision trigger).run_trace ctx.toBranchContext

theorem ct10Run_verified (collision : Collision activation homogeneous)
    (trigger : Coarse.SemanticBottleneckTrigger activation collision) :
    (ct10Run activation collision trigger).outcome.Valid :=
  (ct10Profile activation collision trigger).run_verified ctx.toBranchContext

theorem ct10Run_trace_valid (collision : Collision activation homogeneous)
    (trigger : Coarse.SemanticBottleneckTrigger activation collision) :
    CT10.Graph.ValidTrace
      ((ct10Profile activation collision trigger).capability input.problem)
      ((ct10Profile activation collision trigger).input ctx.toBranchContext)
      (ct10Run activation collision trigger).trace :=
  (ct10Profile activation collision trigger).run_trace_valid ctx.toBranchContext

noncomputable def ct10RunTotal (collision : Collision activation homogeneous)
    (trigger : Coarse.SemanticBottleneckTrigger activation collision) :=
  (ct10Profile activation collision trigger).run_total ctx.toBranchContext

noncomputable def ct10VerifiedStage (collision : Collision activation homogeneous)
    (trigger : Coarse.SemanticBottleneckTrigger activation collision) :=
  (ct10Profile activation collision trigger).verifiedStage ctx.toBranchContext

theorem ct10ClassCount_eq_one (collision : Collision activation homogeneous)
    (trigger : Coarse.SemanticBottleneckTrigger activation collision) :
    (ct10Profile activation collision trigger).classCount = 1 :=
  CT10.ExhaustiveClassification.Profile.exactSelection_classCount _ _

theorem ct10Checks_eq_seven (collision : Collision activation homogeneous)
    (trigger : Coarse.SemanticBottleneckTrigger activation collision) :
    (ct10Profile activation collision trigger).checks = 7 := by
  simpa [ct10Profile] using
    (CT10.ExhaustiveClassification.Profile.exactSelection_checks
      residualTagEnum (classify activation collision trigger).tag)

theorem classified_tag_in_ct10_table
    (collision : Collision activation homogeneous)
    (trigger : Coarse.SemanticBottleneckTrigger activation collision) :
    ⟨(classify activation collision trigger).tag, rfl⟩ ∈
      (ct10Profile activation collision trigger).classes.orderedValues :=
  (ct10Profile activation collision trigger).classes.mem_orderedValues _

/-! One predicate comparison charges the two retained map projections and
their Boolean equality.  CT10's five-class complete table contributes its
exact `5 + 5 + 5^2 = 35` reference checks. -/

noncomputable def classificationWork
    (collision : Collision activation homogeneous)
    (trigger : Coarse.SemanticBottleneckTrigger activation collision) : Nat :=
  3 * (alignmentProfile activation collision).checks +
    (ct10Profile activation collision trigger).checks

theorem classificationWork_eq
    (collision : Collision activation homogeneous)
    (trigger : Coarse.SemanticBottleneckTrigger activation collision) :
    classificationWork activation collision trigger =
      234 * InducedPathWindowLedger.packingNumber ctx.G.object + 7 := by
  have coordinates : (alignmentProfile activation collision).checks =
      78 * InducedPathWindowLedger.packingNumber ctx.G.object := by
    exact attachmentCoordinates_card ctx.G.object
  have table : (ct10Profile activation collision trigger).checks = 7 :=
    ct10Checks_eq_seven activation collision trigger
  rw [classificationWork, coordinates, table]
  omega

theorem classificationWork_le_vertices
    (collision : Collision activation homogeneous)
    (trigger : Coarse.SemanticBottleneckTrigger activation collision) :
    classificationWork activation collision trigger ≤
      234 * ctx.G.object.input.vertices.card + 7 := by
  rw [classificationWork_eq]
  have packed := InducedPathPacking.packing_vertices_bound
    ctx.G.object 13 (by decide)
  rw [← InducedPathWindowLedger.packingNumber_eq_inducedPathPacking] at packed
  have packingLe : InducedPathWindowLedger.packingNumber ctx.G.object ≤
      ctx.G.object.input.vertices.card := by omega
  omega

end StructuralExhaustion.Graph.SurplusPatternSemanticBottleneck
