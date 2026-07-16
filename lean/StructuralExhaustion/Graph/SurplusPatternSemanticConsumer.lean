import StructuralExhaustion.Graph.SurplusPatternSemanticBottleneck
import StructuralExhaustion.Graph.RootIncidence

namespace StructuralExhaustion.Graph.SurplusPatternSemanticConsumer

open StructuralExhaustion

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (activation : SurplusPortActivation.VerifiedActivatedStage input ctx setup)

namespace Previous
export SurplusPatternSemanticBottleneck
  (Collision Evidence Residual ResidualTag classify)
end Previous

namespace Coarse
export SurplusPatternCoarseRouting
  (Routed HomogeneousAudit SemanticBottleneckTrigger canonicalGermResidual)
end Coarse

variable {windowSize remainderSize primitiveSize : Nat}
variable {routed : Coarse.Routed activation windowSize remainderSize primitiveSize}
variable {homogeneous : Coarse.HomogeneousAudit activation
  windowSize remainderSize primitiveSize routed}

abbrev Collision := Previous.Collision activation homogeneous

noncomputable abbrev Comparison
    (collision : Previous.Collision activation homogeneous) :=
  (Coarse.canonicalGermResidual (routed := routed) (homogeneous := homogeneous)
    activation collision).germs.comparison

noncomputable abbrev root : ctx.G.Vertex :=
  (SurplusRoutingGerm.bfsProfile routed.overload.residual.label.1).root

/-! ## Proof-carrying divergence payloads

The classifier below constructs these records only while pattern matching on
the corresponding constructor of the actual comparison retained at node
[177]. -/
structure RootDivergence where
  leftNext : ctx.G.Vertex
  rightNext : ctx.G.Vertex
  leftAdjacent : ctx.G.object.graph.Adj (root (routed := routed)) leftNext
  rightAdjacent : ctx.G.object.graph.Adj (root (routed := routed)) rightNext
  distinct : leftNext ≠ rightNext

def RootDivergence.incidence (data : RootDivergence (routed := routed)) :
    RootIncidence.Divergence ctx.G.object (root (routed := routed)) where
  leftNext := data.leftNext
  rightNext := data.rightNext
  leftAdjacent := data.leftAdjacent
  rightAdjacent := data.rightAdjacent
  distinct := data.distinct

def degree_ge_three (vertex : ctx.G.Vertex) :
    3 ≤ ctx.G.object.degree vertex := by
  rw [← setup.minimumDegree_eq_three]
  exact (SurplusPortActivation.Setup.baseline setup).trans
    (ctx.G.object.minDegree_le_degree vertex)

/-! ## Exact consumer of the five node-[177] leaves -/

inductive Frontier (collision : Previous.Collision activation homogeneous)
    (trigger : Coarse.SemanticBottleneckTrigger activation collision)
    (residual : Previous.Residual activation collision trigger) : Type u where
  | attachmentMismatch
      (tag_eq : residual.tag = .attachmentMismatch)
      (evidence : Previous.Evidence activation collision trigger
        .attachmentMismatch)
  | alignedLeftPrefix
      (tag_eq : residual.tag = .alignedLeftPrefix)
      (evidence : Previous.Evidence activation collision trigger
        .alignedLeftPrefix)
  | alignedRightPrefix
      (tag_eq : residual.tag = .alignedRightPrefix)
      (evidence : Previous.Evidence activation collision trigger
        .alignedRightPrefix)
  | rootDivergence
      (tag_eq : residual.tag = .alignedRootDivergence)
      (evidence : Previous.Evidence activation collision trigger
        .alignedRootDivergence)
      (data : RootDivergence (routed := routed))
      (branch : RootIncidence.Branch ctx.G.object
        (root (routed := routed)) data.incidence)
  | afterEdgeDivergence
      (tag_eq : residual.tag = .alignedAfterEdgeDivergence)
      (evidence : Previous.Evidence activation collision trigger
        .alignedAfterEdgeDivergence)
      (separator : ctx.G.Vertex)
      (incidence : RootIncidence.AfterEdge ctx.G.object separator)
      (branch : RootIncidence.AfterEdgeBranch ctx.G.object separator incidence)

/-- Consume the exact residual returned by node [177].  Mismatch and prefix
leaves are preserved verbatim.  A divergent stored comparison exposes its
literal separator incidences; only the actual neighbour schedule at a root or
one local degree comparison after an edge is inspected. -/
noncomputable def classify (collision : Previous.Collision activation homogeneous)
    (trigger : Coarse.SemanticBottleneckTrigger activation collision)
    (residual : Previous.Residual activation collision trigger) :
    Frontier activation collision trigger residual := by
  cases tagEq : residual.tag with
  | attachmentMismatch =>
      exact .attachmentMismatch tagEq (tagEq ▸ residual.evidence)
  | alignedLeftPrefix =>
      exact .alignedLeftPrefix tagEq (tagEq ▸ residual.evidence)
  | alignedRightPrefix =>
      exact .alignedRightPrefix tagEq (tagEq ▸ residual.evidence)
  | alignedRootDivergence =>
      have evidence : Previous.Evidence activation collision trigger
          .alignedRootDivergence := tagEq ▸ residual.evidence
      cases comparisonEq : Comparison (routed := routed) (homogeneous := homogeneous)
          activation collision with
      | leftPrefix rightRest rightEq =>
          simp [Previous.Evidence, SurplusPatternSemanticBottleneck.germShape,
            comparisonEq] at evidence
      | rightPrefix leftRest leftEq =>
          simp [Previous.Evidence, SurplusPatternSemanticBottleneck.germShape,
            comparisonEq] at evidence
      | divergeAtRoot leftNext rightNext leftTail rightTail leftEq rightEq
          distinct leftAdjacent rightAdjacent residualDisjoint =>
          let data : RootDivergence (routed := routed) := {
            leftNext := leftNext
            rightNext := rightNext
            leftAdjacent := leftAdjacent
            rightAdjacent := rightAdjacent
            distinct := distinct
          }
          exact .rootDivergence tagEq evidence data
            (RootIncidence.classify ctx.G.object (root (routed := routed))
              (degree_ge_three (setup := setup) _) data.incidence)
      | divergeAfterEdge stem predecessor separator leftNext rightNext
          leftTail rightTail leftEq rightEq predecessorAdjacent leftAdjacent
          rightAdjacent distinct residualDisjoint =>
          simp [Previous.Evidence, SurplusPatternSemanticBottleneck.germShape,
            comparisonEq] at evidence
  | alignedAfterEdgeDivergence =>
      have evidence : Previous.Evidence activation collision trigger
          .alignedAfterEdgeDivergence := tagEq ▸ residual.evidence
      cases comparisonEq : Comparison (routed := routed) (homogeneous := homogeneous)
          activation collision with
      | leftPrefix rightRest rightEq =>
          simp [Previous.Evidence, SurplusPatternSemanticBottleneck.germShape,
            comparisonEq] at evidence
      | rightPrefix leftRest leftEq =>
          simp [Previous.Evidence, SurplusPatternSemanticBottleneck.germShape,
            comparisonEq] at evidence
      | divergeAtRoot leftNext rightNext leftTail rightTail leftEq rightEq
          distinct leftAdjacent rightAdjacent residualDisjoint =>
          simp [Previous.Evidence, SurplusPatternSemanticBottleneck.germShape,
            comparisonEq] at evidence
      | divergeAfterEdge stem predecessor separator leftNext rightNext
          leftTail rightTail leftEq rightEq predecessorAdjacent leftAdjacent
          rightAdjacent distinct residualDisjoint =>
          have predecessorNeLeft : predecessor ≠ leftNext := by
            have nodup := ((SurplusRoutingGerm.bfsProfile
              routed.overload.residual.label.1).treeWalk_isPath
                SurplusRoutingGerm.bfsPreconnected
                (SurplusRoutingGerm.endpointSelection activation
                  routed.overload.residual.label.1
                  collision.collision.first
                  (Coarse.canonicalGermResidual activation collision).germs.firstBranch
                  true).vertex).support_nodup
            rw [leftEq] at nodup
            have separated : List.Disjoint
                (stem ++ [predecessor, separator]) (leftNext :: leftTail) :=
              nodup.disjoint
            intro equal
            have predecessorRest : predecessor ∈ leftNext :: leftTail := by
              rw [equal]
              simp
            exact (List.disjoint_left.mp separated) (by simp) predecessorRest
          have predecessorNeRight : predecessor ≠ rightNext := by
            have nodup := ((SurplusRoutingGerm.bfsProfile
              routed.overload.residual.label.1).treeWalk_isPath
                SurplusRoutingGerm.bfsPreconnected
                (SurplusRoutingGerm.endpointSelection activation
                  routed.overload.residual.label.1
                  collision.collision.second
                  (Coarse.canonicalGermResidual activation collision).germs.secondBranch
                  true).vertex).support_nodup
            rw [rightEq] at nodup
            have separated : List.Disjoint
                (stem ++ [predecessor, separator]) (rightNext :: rightTail) :=
              nodup.disjoint
            intro equal
            have predecessorRest : predecessor ∈ rightNext :: rightTail := by
              rw [equal]
              simp
            exact (List.disjoint_left.mp separated) (by simp) predecessorRest
          let incidence : RootIncidence.AfterEdge ctx.G.object separator := {
            predecessor := predecessor
            leftNext := leftNext
            rightNext := rightNext
            predecessorAdjacent := predecessorAdjacent.symm
            leftAdjacent := leftAdjacent
            rightAdjacent := rightAdjacent
            predecessor_ne_left := predecessorNeLeft
            predecessor_ne_right := predecessorNeRight
            left_ne_right := distinct
          }
          exact .afterEdgeDivergence tagEq evidence separator incidence
            (RootIncidence.classifyAfterEdge ctx.G.object separator
              (degree_ge_three (setup := setup) separator) incidence)

theorem classify_total (collision : Previous.Collision activation homogeneous)
    (trigger : Coarse.SemanticBottleneckTrigger activation collision)
    (residual : Previous.Residual activation collision trigger) :
    Nonempty (Frontier activation collision trigger residual) :=
  ⟨classify activation collision trigger residual⟩

/-- The root scan is bounded by the supplied vertex order; the after-edge
branch costs one comparison.  Taking their sum gives a uniform local bound. -/
def checks : Nat := ctx.G.object.input.vertices.card + 1

theorem checks_le_linear : checks (ctx := ctx) ≤
    ctx.G.object.input.vertices.card + 1 := le_rfl

end StructuralExhaustion.Graph.SurplusPatternSemanticConsumer
