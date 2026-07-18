import StructuralExhaustion.Graph.SurplusPatternSemanticBottleneck

namespace StructuralExhaustion.Graph.SurplusPatternAttachmentMismatch

open StructuralExhaustion

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (activation : SurplusPortActivation.VerifiedActivatedStage input ctx setup)

namespace Previous
export SurplusPatternSemanticBottleneck
  (Collision Evidence AttachmentCoordinate alignmentProfile)
end Previous

namespace Coarse
export SurplusPatternCoarseRouting (Routed HomogeneousAudit pairSlot)
end Coarse

variable {windowSize remainderSize primitiveSize : Nat}
variable {routed : Coarse.Routed activation windowSize remainderSize primitiveSize}
variable {homogeneous : Coarse.HomogeneousAudit activation
  windowSize remainderSize primitiveSize routed}

/-- Proof-carrying first mismatch, retaining the exact declared coordinate
order and agreement of every earlier coordinate. -/
structure Origin (collision : Previous.Collision activation homogeneous) where
  hit : Core.FiniteSearch.FirstHit
    (Previous.alignmentProfile activation collision).coordinates.orderedValues
    (Previous.alignmentProfile activation collision).Mismatch
  sound : (Previous.alignmentProfile activation collision).Mismatch hit.value
  prefixExact : ∀ coordinate, coordinate ∈ hit.before →
    ((Previous.alignmentProfile activation collision).left coordinate ↔
      (Previous.alignmentProfile activation collision).right coordinate)

noncomputable def ofEvidence
    (collision : Previous.Collision activation homogeneous)
    {trigger : SurplusPatternCoarseRouting.SemanticBottleneckTrigger activation
      collision}
    (evidence : Previous.Evidence activation collision trigger
      .attachmentMismatch) : Origin activation collision := by
  let hit := Classical.choose evidence
  exact {
    hit := hit
    sound := Classical.choose_spec evidence
    prefixExact :=
      (Previous.alignmentProfile activation collision).mismatch_prefix_exact hit
  }

namespace Origin

variable {collision : Previous.Collision activation homogeneous}

def window (origin : Origin activation collision) := origin.hit.value.1
def position (origin : Origin activation collision) := origin.hit.value.2.1
def pairSide (origin : Origin activation collision) := origin.hit.value.2.2.1
def role (origin : Origin activation collision) := origin.hit.value.2.2.2

noncomputable def windowVertex (origin : Origin activation collision) : ctx.G.Vertex :=
  InducedPathWindowLedger.selectedWindow ctx.G.object origin.window origin.position

noncomputable def firstPair (origin : Origin activation collision) :=
  collision.collision.first
noncomputable def secondPair (origin : Origin activation collision) :=
  collision.collision.second

noncomputable def firstSlot (origin : Origin activation collision) :
    SurplusPortActivation.Slot setup :=
  Coarse.pairSlot origin.firstPair origin.pairSide

noncomputable def secondSlot (origin : Origin activation collision) :
    SurplusPortActivation.Slot setup :=
  Coarse.pairSlot origin.secondPair origin.pairSide

noncomputable def firstRoleVertex (origin : Origin activation collision) : ctx.G.Vertex :=
  SurplusPortActivation.portVertex setup origin.firstSlot origin.role

noncomputable def secondRoleVertex (origin : Origin activation collision) : ctx.G.Vertex :=
  SurplusPortActivation.portVertex setup origin.secondSlot origin.role

theorem mismatch_exact (origin : Origin activation collision) :
    ¬(ctx.G.object.graph.Adj origin.windowVertex origin.firstRoleVertex ↔
      ctx.G.object.graph.Adj origin.windowVertex origin.secondRoleVertex) := by
  have sound := origin.sound
  change ¬(collision.attachments.firstMap origin.hit.value.1
      origin.hit.value.2.1 origin.hit.value.2.2.1 origin.hit.value.2.2.2 ↔
    collision.attachments.secondMap origin.hit.value.1
      origin.hit.value.2.1 origin.hit.value.2.2.1 origin.hit.value.2.2.2) at sound
  rw [collision.attachments.first_exact,
    collision.attachments.second_exact] at sound
  simpa [SurplusPatternCoarseRouting.windowPortAttached, windowVertex,
    firstRoleVertex, secondRoleVertex, firstSlot, secondSlot, firstPair,
    secondPair, window, position, pairSide, role,
    Previous.alignmentProfile] using sound

/-- The only two literal meanings of one adjacency mismatch. -/
inductive Orientation (origin : Origin activation collision) : Prop where
  | firstOnly
      (firstAdjacent : ctx.G.object.graph.Adj origin.windowVertex
        origin.firstRoleVertex)
      (secondNonadjacent : ¬ctx.G.object.graph.Adj origin.windowVertex
        origin.secondRoleVertex)
  | secondOnly
      (firstNonadjacent : ¬ctx.G.object.graph.Adj origin.windowVertex
        origin.firstRoleVertex)
      (secondAdjacent : ctx.G.object.graph.Adj origin.windowVertex
        origin.secondRoleVertex)

noncomputable def orientation (origin : Origin activation collision) :
    Orientation activation origin := by
  letI : DecidableRel ctx.G.object.graph.Adj := ctx.G.object.input.decideAdj
  by_cases firstAdjacent : ctx.G.object.graph.Adj origin.windowVertex
      origin.firstRoleVertex
  · have secondNonadjacent : ¬ctx.G.object.graph.Adj origin.windowVertex
        origin.secondRoleVertex := by
      intro secondAdjacent
      exact (mismatch_exact activation origin)
        (Iff.intro (fun _ => secondAdjacent) (fun _ => firstAdjacent))
    exact .firstOnly firstAdjacent secondNonadjacent
  · have secondAdjacent : ctx.G.object.graph.Adj origin.windowVertex
        origin.secondRoleVertex := by
      by_contra secondNonadjacent
      exact (mismatch_exact activation origin)
        (Iff.intro (fun first => (firstAdjacent first).elim)
          (fun second => (secondNonadjacent second).elim))
    exact .secondOnly firstAdjacent secondAdjacent

theorem roleVertices_ne (origin : Origin activation collision) :
    origin.firstRoleVertex ≠ origin.secondRoleVertex := by
  intro equal
  apply origin.mismatch_exact
  rw [equal]

end Origin

/-- Exact accounting class of the common capacity token. -/
inductive TokenClassOrigin : Type where
  | window
      (route : SurplusClasswiseOverload.tokenClass
        routed.overload.residual.label.1 = .window)
  | remainder
      (route : SurplusClasswiseOverload.tokenClass
        routed.overload.residual.label.1 = .remainder)
  | primitive
      (route : SurplusClasswiseOverload.tokenClass
        routed.overload.residual.label.1 = .primitive)

def tokenClassOrigin : TokenClassOrigin (routed := routed) := by
  cases homogeneous with
  | window route stage => exact .window route
  | remainder route stage => exact .remainder route
  | primitive route stage => exact .primitive route

/-- Complete dependency-ready mismatch leaf.  It deliberately contains no
boundaried quotient, target response, compression, delocalization, or cycle. -/
structure UnmatchedCoordinateResidual
    (collision : Previous.Collision activation homogeneous) : Type u where
  origin : Origin activation collision
  orientation : origin.Orientation
  roleVerticesDistinct : origin.firstRoleVertex ≠ origin.secondRoleVertex
  tokenClass : TokenClassOrigin (routed := routed)

noncomputable def residual
    (collision : Previous.Collision activation homogeneous)
    {trigger : SurplusPatternCoarseRouting.SemanticBottleneckTrigger activation
      collision}
    (evidence : Previous.Evidence activation collision trigger
      .attachmentMismatch) :
    UnmatchedCoordinateResidual activation collision := by
  let origin := ofEvidence activation collision evidence
  exact {
    origin := origin
    orientation := origin.orientation
    roleVerticesDistinct := origin.roleVertices_ne
    tokenClass := tokenClassOrigin (homogeneous := homogeneous)
  }

end StructuralExhaustion.Graph.SurplusPatternAttachmentMismatch
