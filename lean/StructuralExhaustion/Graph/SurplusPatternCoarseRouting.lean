import StructuralExhaustion.Core.FiniteCodeCollision
import StructuralExhaustion.Graph.InducedPathWindowLedger
import StructuralExhaustion.Graph.SurplusHomogeneousPattern
import StructuralExhaustion.Graph.SurplusRoutingGerm

namespace StructuralExhaustion.Graph.SurplusPatternCoarseRouting

open StructuralExhaustion

universe u

/-!
# Fixed coarse repetition before any ambient attachment scan

The fixed code below uses only observations already constructed before the
node-144 pigeonhole step.  In particular it does not replace the missing
piece-local capped boundary-degree profile by ambient degrees.  Omitting that
coordinate makes the code coarser and therefore creates at least as many
collisions.  No selected-window or ambient-vertex attachment relation is
enumerated or decided in this module.
-/

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (activation : SurplusPortActivation.VerifiedActivatedStage input ctx setup)

abbrev Pair := SurplusPairResponse.ScheduledPair (setup := setup)
abbrev Token := SurplusCapacityTokenRouting.Token (ctx := ctx) (setup := setup)

noncomputable abbrev Routed (windowSize remainderSize primitiveSize : Nat) :=
  SurplusClasswiseOverload.RoutedOverload activation
    windowSize remainderSize primitiveSize

noncomputable abbrev HomogeneousAudit
    (windowSize remainderSize primitiveSize : Nat)
    (routed : Routed activation windowSize remainderSize primitiveSize) :=
  SurplusHomogeneousPattern.Audit activation
    windowSize remainderSize primitiveSize routed

noncomputable def patternPairs
    {windowSize remainderSize primitiveSize : Nat}
    {routed : Routed activation windowSize remainderSize primitiveSize}
    (audit : HomogeneousAudit activation windowSize remainderSize primitiveSize routed) :
    List (Pair (setup := setup)) :=
  match audit with
  | .window _ stage | .remainder _ stage | .primitive _ stage =>
      match stage.pattern with
      | .matching result => result.pairs
      | .star result => result.pairs

theorem patternPairs_length
    {windowSize remainderSize primitiveSize : Nat}
    {routed : Routed activation windowSize remainderSize primitiveSize}
    (audit : HomogeneousAudit activation windowSize remainderSize primitiveSize routed) :
    (patternPairs activation audit).length =
      match audit with
      | .window _ _ => windowSize
      | .remainder _ _ => remainderSize
      | .primitive _ _ => primitiveSize := by
  cases audit with
  | window route stage | remainder route stage | primitive route stage =>
      cases patternEq : stage.pattern with
      | matching result => simpa [patternPairs, patternEq] using result.exactSize
      | star result => simpa [patternPairs, patternEq] using result.exactSize

theorem patternPairs_nodup
    {windowSize remainderSize primitiveSize : Nat}
    {routed : Routed activation windowSize remainderSize primitiveSize}
    (audit : HomogeneousAudit activation windowSize remainderSize primitiveSize routed) :
    (patternPairs activation audit).Nodup := by
  cases audit with
  | window route stage | remainder route stage | primitive route stage =>
      cases patternEq : stage.pattern with
      | matching result =>
          simpa [patternPairs, patternEq] using result.matching.1
      | star result =>
          simpa [patternPairs, patternEq] using result.star.1

/-- Three fixed structural branch tags reserved by the coarse paper code.
Only `.local` is populated before the later semantic consumers exist. -/
inductive FixedBranchTag
  | local
  | firstResidual
  | secondResidual
  deriving DecidableEq, Repr

def fixedBranchTags : List FixedBranchTag :=
  [.local, .firstResidual, .secondResidual]

theorem mem_fixedBranchTags (tag : FixedBranchTag) : tag ∈ fixedBranchTags := by
  cases tag <;> simp [fixedBranchTags]

@[reducible] def fixedBranchTagEnum : FinEnum FixedBranchTag :=
  FinEnum.ofList fixedBranchTags mem_fixedBranchTags

/-- Exact graph-independent code.  It deliberately uses only the two literal
constant-size port-type tests at this predecessor.  The other two Boolean
slots and the branch tag remain their neutral values until a later structural
map proves the corresponding semantics.  A coarser code only increases the
collision fibre and does not assume missing data. -/
abbrev CoarseCode :=
  Bool × SurplusPortActivity.PortType × SurplusPortActivity.PortType ×
    Bool × FixedBranchTag

@[reducible] def bools : FinEnum Bool :=
  FinEnum.ofList [false, true] (by intro value; cases value <;> simp)

@[reducible] def coarseCodes : FinEnum CoarseCode := by
  exact Core.Enumeration.prod bools
    (Core.Enumeration.prod SurplusPortActivity.portTypes
      (Core.Enumeration.prod SurplusPortActivity.portTypes
        (Core.Enumeration.prod bools
          fixedBranchTagEnum)))

@[simp] theorem coarseCodes_card : coarseCodes.card = 48 := by
  rfl

noncomputable def coarseCode
    (_token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup)) : CoarseCode :=
  (false,
    SurplusPortActivity.portType ctx.G.object setup.deletionCritical pair.first,
    SurplusPortActivity.portType ctx.G.object setup.deletionCritical pair.second,
    false,
    .local)

abbrev Collision
    (token : Token (ctx := ctx) (setup := setup))
    (pairs : List (Pair (setup := setup))) :=
  Core.FiniteCodeCollision.OrderedCollision
    (coarseCode token) pairs

/-- Any selected pattern of length at least 49 contains two distinct
occurrences with the same exact coarse code. -/
theorem collision_of_48_lt_length
    (token : Token (ctx := ctx) (setup := setup))
    (pairs : List (Pair (setup := setup)))
    (large : 48 < pairs.length) :
    Nonempty (Collision token pairs) := by
  apply Core.FiniteCodeCollision.collision_of_card_lt_length
    coarseCodes (coarseCode token) pairs
  simpa using large

/-! ## Structural selected-window incidence maps

These maps are queried at a supplied selected window and fixed local
coordinates.  They do not enumerate windows, vertices, paths, pairs, or
attachments and make no global equality decision.
-/

def pairSlot (pair : Pair (setup := setup)) (first : Bool) :
    SurplusPortActivation.Slot setup :=
  if first then pair.first else pair.second

def windowPortAttached
    (pair : Pair (setup := setup))
    (window : InducedPathWindowLedger.WindowIndex ctx.G.object)
    (position : Fin 13) (first : Bool)
    (role : SurplusPortActivation.PortRole) : Prop :=
  ctx.G.object.graph.Adj
    (InducedPathWindowLedger.selectedWindow ctx.G.object window position)
    (SurplusPortActivation.portVertex setup (pairSlot pair first) role)

noncomputable def pairPortCarrier
    (pair : Pair (setup := setup)) : Finset ctx.G.Vertex := by
  classical
  exact SurplusPortActivation.PortSupport setup pair.first ∪
    SurplusPortActivation.PortSupport setup pair.second

theorem pairPortCarrier_card_le_six
    (pair : Pair (setup := setup)) :
    (pairPortCarrier (ctx := ctx) (setup := setup) pair).card ≤ 6 := by
  classical
  have unionBound := Finset.card_union_le
    (SurplusPortActivation.PortSupport setup pair.first)
    (SurplusPortActivation.PortSupport setup pair.second)
  calc
    (pairPortCarrier (ctx := ctx) (setup := setup) pair).card ≤
        (SurplusPortActivation.PortSupport setup pair.first).card +
          (SurplusPortActivation.PortSupport setup pair.second).card :=
      by simpa [pairPortCarrier] using unionBound
    _ = 6 := by rw [SurplusPortActivation.portSupport_card,
      SurplusPortActivation.portSupport_card]

structure StructuralAttachmentMaps
    (first second : Pair (setup := setup)) where
  firstMap : InducedPathWindowLedger.WindowIndex ctx.G.object →
    Fin 13 → Bool → SurplusPortActivation.PortRole → Prop
  secondMap : InducedPathWindowLedger.WindowIndex ctx.G.object →
    Fin 13 → Bool → SurplusPortActivation.PortRole → Prop
  first_exact : firstMap = windowPortAttached (ctx := ctx) (setup := setup) first
  second_exact : secondMap = windowPortAttached (ctx := ctx) (setup := setup) second
  window_injective : ∀ window,
    Function.Injective (InducedPathWindowLedger.selectedWindow ctx.G.object window)
  firstCarrierBound :
    (pairPortCarrier (ctx := ctx) (setup := setup) first).card ≤ 6
  secondCarrierBound :
    (pairPortCarrier (ctx := ctx) (setup := setup) second).card ≤ 6

def structuralAttachmentMaps
    (first second : Pair (setup := setup)) :
    StructuralAttachmentMaps first second where
  firstMap := windowPortAttached (ctx := ctx) (setup := setup) first
  secondMap := windowPortAttached (ctx := ctx) (setup := setup) second
  first_exact := rfl
  second_exact := rfl
  window_injective := fun window =>
    (InducedPathWindowLedger.selectedWindow ctx.G.object window).injective
  firstCarrierBound := pairPortCarrier_card_le_six first
  secondCarrierBound := pairPortCarrier_card_le_six second

/-! ## Composition on the exact homogeneous pattern -/

structure VerifiedCollision
    {windowSize remainderSize primitiveSize : Nat}
    {routed : Routed activation
      windowSize remainderSize primitiveSize}
    (homogeneous : HomogeneousAudit activation
      windowSize remainderSize primitiveSize routed) : Type u where
  large : 48 <
    (patternPairs activation homogeneous).length
  collision : Collision routed.overload.residual.label.1
    (patternPairs activation homogeneous)
  distinct : collision.first ≠ collision.second
  sameCode : coarseCode routed.overload.residual.label.1 collision.first =
    coarseCode routed.overload.residual.label.1 collision.second
  attachments : StructuralAttachmentMaps collision.first collision.second
  decisionExact : Core.FiniteCodeCollision.decide coarseCodes
      (coarseCode routed.overload.residual.label.1)
      (patternPairs activation homogeneous) = .collision collision

/-- Select the first exact coarse collision.  No ambient vertex, selected
window, attachment, path, pair, or graph universe is scanned here. -/
noncomputable def verifiedCollision
    {windowSize remainderSize primitiveSize : Nat}
    {routed : Routed activation
      windowSize remainderSize primitiveSize}
    (homogeneous : HomogeneousAudit activation
      windowSize remainderSize primitiveSize routed)
    (large : 48 <
      (patternPairs activation homogeneous).length) :
    VerifiedCollision activation homogeneous := by
  generalize decisionEq : Core.FiniteCodeCollision.decide coarseCodes
    (coarseCode routed.overload.residual.label.1)
    (patternPairs activation homogeneous) = decision
  cases decision with
  | collision collision =>
      exact {
        large := large
        collision := collision
        distinct := collision.first_ne_second_of_nodup
          (patternPairs_nodup activation homogeneous)
        sameCode := collision.code_eq
        attachments := structuralAttachmentMaps collision.first collision.second
        decisionExact := decisionEq
      }
  | unique codesNodup =>
      have bounded := Core.Enumeration.length_le_elems_of_nodup
        coarseCodes codesNodup
      rw [List.length_map, FinEnum.orderedValues_length] at bounded
      rw [coarseCodes_card] at bounded
      omega

/-- Conservative primitive comparison count for the actual nested ordered
collision scan.  The reference runner compares at most every ordered pair in
the supplied homogeneous pattern and never scans an ambient family. -/
noncomputable def collisionChecks
    {windowSize remainderSize primitiveSize : Nat}
    {routed : Routed activation windowSize remainderSize primitiveSize}
    (homogeneous : HomogeneousAudit activation
      windowSize remainderSize primitiveSize routed) : Nat :=
  (patternPairs activation homogeneous).length ^ 2

theorem collisionChecks_eq_square
    {windowSize remainderSize primitiveSize : Nat}
    {routed : Routed activation windowSize remainderSize primitiveSize}
    (homogeneous : HomogeneousAudit activation
      windowSize remainderSize primitiveSize routed) :
    collisionChecks activation homogeneous =
      (patternPairs activation homogeneous).length ^ 2 :=
  rfl

/-! ## Exactly two canonical germs after the fixed collision -/

structure CanonicalCollisionGerms
    {windowSize remainderSize primitiveSize : Nat}
    {routed : Routed activation windowSize remainderSize primitiveSize}
    {homogeneous : HomogeneousAudit activation
      windowSize remainderSize primitiveSize routed}
    (collision : VerifiedCollision activation homogeneous) : Type u where
  firstBranch : SurplusRoutingSupport.PairBranch activation collision.collision.first
  secondBranch : SurplusRoutingSupport.PairBranch activation collision.collision.second
  comparison : (SurplusRoutingGerm.bfsProfile
      routed.overload.residual.label.1).TreePathComparison
        SurplusRoutingGerm.bfsPreconnected
        (SurplusRoutingGerm.endpointSelection activation
          routed.overload.residual.label.1 collision.collision.first
          firstBranch true).vertex
        (SurplusRoutingGerm.endpointSelection activation
          routed.overload.residual.label.1 collision.collision.second
          secondBranch true).vertex
  firstLands :
    (SurplusRoutingGerm.endpointSelection activation
      routed.overload.residual.label.1 collision.collision.first
      firstBranch true).vertex ∈
        SurplusRoutingGerm.endpointSupport collision.collision.first true
  secondLands :
    (SurplusRoutingGerm.endpointSelection activation
      routed.overload.residual.label.1 collision.collision.second
      secondBranch true).vertex ∈
        SurplusRoutingGerm.endpointSupport collision.collision.second true
  firstShortest : ∀ {candidate : ctx.G.Vertex},
    candidate ∈ SurplusRoutingGerm.endpointSupport collision.collision.first true →
    (walk : ctx.G.object.graph.Walk
      (SurplusRoutingSupport.tokenRoot routed.overload.residual.label.1) candidate) →
    (SurplusRoutingGerm.selectedGerm activation
      routed.overload.residual.label.1 collision.collision.first
      firstBranch true).length ≤ walk.length
  secondShortest : ∀ {candidate : ctx.G.Vertex},
    candidate ∈ SurplusRoutingGerm.endpointSupport collision.collision.second true →
    (walk : ctx.G.object.graph.Walk
      (SurplusRoutingSupport.tokenRoot routed.overload.residual.label.1) candidate) →
    (SurplusRoutingGerm.selectedGerm activation
      routed.overload.residual.label.1 collision.collision.second
      secondBranch true).length ≤ walk.length

/-- Construct only the two collided-pair germs and compare their supplied BFS
tree words.  No other pattern pair is inspected. -/
noncomputable def canonicalCollisionGerms
    {windowSize remainderSize primitiveSize : Nat}
    {routed : Routed activation windowSize remainderSize primitiveSize}
    {homogeneous : HomogeneousAudit activation
      windowSize remainderSize primitiveSize routed}
    (collision : VerifiedCollision activation homogeneous) :
    CanonicalCollisionGerms activation collision := by
  let firstBranch := SurplusRoutingSupport.classify activation
    collision.collision.first
  let secondBranch := SurplusRoutingSupport.classify activation
    collision.collision.second
  exact {
    firstBranch := firstBranch
    secondBranch := secondBranch
    comparison := (SurplusRoutingGerm.bfsProfile
      routed.overload.residual.label.1).classifyTreePaths
        SurplusRoutingGerm.bfsPreconnected
        (SurplusRoutingGerm.endpointSelection activation
          routed.overload.residual.label.1 collision.collision.first
          firstBranch true).vertex
        (SurplusRoutingGerm.endpointSelection activation
          routed.overload.residual.label.1 collision.collision.second
          secondBranch true).vertex
    firstLands := (SurplusRoutingGerm.selectedGerm_first_lands activation
      routed.overload.residual.label.1 collision.collision.first
      firstBranch true).1
    secondLands := (SurplusRoutingGerm.selectedGerm_first_lands activation
      routed.overload.residual.label.1 collision.collision.second
      secondBranch true).1
    firstShortest := fun candidateMem walk =>
      SurplusRoutingGerm.selectedGerm_shortest activation
        routed.overload.residual.label.1 collision.collision.first
        firstBranch true candidateMem walk
    secondShortest := fun candidateMem walk =>
      SurplusRoutingGerm.selectedGerm_shortest activation
        routed.overload.residual.label.1 collision.collision.second
        secondBranch true candidateMem walk
  }

/-- The precise semantic field not determined by the pair data: equality of
the two structural selected-window attachment maps.  This is a requirement,
not an assumed theorem and not an executable ambient scan. -/
def AttachmentAlignment
    {windowSize remainderSize primitiveSize : Nat}
    {routed : Routed activation windowSize remainderSize primitiveSize}
    {homogeneous : HomogeneousAudit activation
      windowSize remainderSize primitiveSize routed}
    (collision : VerifiedCollision activation homogeneous) : Prop :=
  ∀ window position first role,
    collision.attachments.firstMap window position first role ↔
      collision.attachments.secondMap window position first role

structure CanonicalGermResidual
    {windowSize remainderSize primitiveSize : Nat}
    {routed : Routed activation windowSize remainderSize primitiveSize}
    {homogeneous : HomogeneousAudit activation
      windowSize remainderSize primitiveSize routed}
    (collision : VerifiedCollision activation homogeneous) : Type u where
  germs : CanonicalCollisionGerms activation collision
  requiredAlignment : Prop
  requiredAlignment_eq : requiredAlignment = AttachmentAlignment activation collision

noncomputable def canonicalGermResidual
    {windowSize remainderSize primitiveSize : Nat}
    {routed : Routed activation windowSize remainderSize primitiveSize}
    {homogeneous : HomogeneousAudit activation
      windowSize remainderSize primitiveSize routed}
    (collision : VerifiedCollision activation homogeneous) :
    CanonicalGermResidual activation collision where
  germs := canonicalCollisionGerms activation collision
  requiredAlignment := AttachmentAlignment activation collision
  requiredAlignment_eq := rfl

/-! ## Registered semantic-consumer boundary

The classifier does not prove attachment alignment or any sparse-exit/Type-B
conclusion.  This trigger is the exact input of the unique downstream semantic
consumer.  It registers the route without placing a proof of the open goal in
the producer payload. -/

structure SemanticBottleneckTrigger
    {windowSize remainderSize primitiveSize : Nat}
    {routed : Routed activation windowSize remainderSize primitiveSize}
    {homogeneous : HomogeneousAudit activation
      windowSize remainderSize primitiveSize routed}
    (collision : VerifiedCollision activation homogeneous) : Type u where
  source : CanonicalGermResidual activation collision
  openGoal : Prop
  openGoal_eq : openGoal = AttachmentAlignment activation collision

/-- S-Rout: transport the computed collision residual, unchanged, to the
unique semantic bottleneck consumer. -/
noncomputable def toSemanticBottleneckTrigger
    {windowSize remainderSize primitiveSize : Nat}
    {routed : Routed activation windowSize remainderSize primitiveSize}
    {homogeneous : HomogeneousAudit activation
      windowSize remainderSize primitiveSize routed}
    (collision : VerifiedCollision activation homogeneous)
    (source : CanonicalGermResidual activation collision) :
    SemanticBottleneckTrigger activation collision where
  source := source
  openGoal := source.requiredAlignment
  openGoal_eq := source.requiredAlignment_eq

/-- S-Trig: every computed residual populates the complete registered input
of the semantic consumer; no alignment proof is assumed. -/
theorem semanticBottleneckTrigger_total
    {windowSize remainderSize primitiveSize : Nat}
    {routed : Routed activation windowSize remainderSize primitiveSize}
    {homogeneous : HomogeneousAudit activation
      windowSize remainderSize primitiveSize routed}
    (collision : VerifiedCollision activation homogeneous)
    (source : CanonicalGermResidual activation collision) :
    Nonempty (SemanticBottleneckTrigger activation collision) :=
  ⟨toSemanticBottleneckTrigger activation collision source⟩

/-- Persistence: the consumer receives the identical collision, attachment
maps, and two canonical germs. -/
theorem semanticBottleneckTrigger_source_exact
    {windowSize remainderSize primitiveSize : Nat}
    {routed : Routed activation windowSize remainderSize primitiveSize}
    {homogeneous : HomogeneousAudit activation
      windowSize remainderSize primitiveSize routed}
    (collision : VerifiedCollision activation homogeneous)
    (source : CanonicalGermResidual activation collision) :
    (toSemanticBottleneckTrigger activation collision source).source = source :=
  rfl

/-- Conservative local work currency for the executed collision scan and the
two selected rooted germs.  The current runner does not cache codes, so each
of at most `length^2` comparisons is charged two coarse-code projections.
The `decisionExact` field ties the scan term to the actual `decide` result. -/
noncomputable def classificationWork
    {windowSize remainderSize primitiveSize : Nat}
    {routed : Routed activation windowSize remainderSize primitiveSize}
    {homogeneous : HomogeneousAudit activation
      windowSize remainderSize primitiveSize routed}
    (collision : VerifiedCollision activation homogeneous) : Nat :=
  let length := (patternPairs activation homogeneous).length
  3 * length ^ 2 +
    2 * SurplusRoutingGerm.zstarBudget routed.overload.residual.label.1

theorem classificationWork_eq
    {windowSize remainderSize primitiveSize : Nat}
    {routed : Routed activation windowSize remainderSize primitiveSize}
    {homogeneous : HomogeneousAudit activation
      windowSize remainderSize primitiveSize routed}
    (collision : VerifiedCollision activation homogeneous) :
    classificationWork activation collision =
      3 * (patternPairs activation homogeneous).length ^ 2 +
        2 * SurplusRoutingGerm.zstarBudget
          routed.overload.residual.label.1 :=
  rfl

end StructuralExhaustion.Graph.SurplusPatternCoarseRouting
