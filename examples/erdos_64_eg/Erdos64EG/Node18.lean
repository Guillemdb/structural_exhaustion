import Erdos64EG.Node17
import Erdos64EG.Shared.CT10P13LabelAlgebra

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [18]: the finite `P₁₃` label algebra

This is the thin node-local successor of the literal node-[17] packing
stage.  The predecessor and the full accumulated ledger are retained by
`DependentSuccessor`; this payload contains only the new CT10 classification
and the paper's exact label count, size distribution, `C_s`, and `Ω₂`
certificates.
-/

/-- The selected minimal graph carried by the literal node-[17] stage. -/
abbrev Node18Context {V : Type u} {residual : InitialResidual V}
    (node17 : Node17Stage residual) :=
  Node17StageContext node17

/-- Only the mathematics first established at node [18]. -/
structure Node18Output {V : Type u} {residual : InitialResidual V}
    (node17 : Node17Stage residual) : Prop where
  classificationStage :
    p13LabelClassification.VerifiedStage
      (Node18Context node17).toBranchContext
  labelCount : p13LabelClassification.classCount = 399
  sizeDistribution :
    p13LabelsOfSize 1 = 13 ∧
    p13LabelsOfSize 2 = 60 ∧
    p13LabelsOfSize 3 = 122 ∧
    p13LabelsOfSize 4 = 122 ∧
    p13LabelsOfSize 5 = 63 ∧
    p13LabelsOfSize 6 = 17 ∧
    p13LabelsOfSize 7 = 2
  relationSemantics : ∀ shift left right,
    p13C shift left right = 1 ↔
      Graph.InducedPathAttachment.Compatible 13 PowerOfTwoLength shift
        left right
  curvatureSemantics : ∀ source middle target,
    p13OmegaTwo source middle target = 1 ↔
      Graph.InducedPathAttachment.Compatible 13 PowerOfTwoLength 1
          source middle ∧
        Graph.InducedPathAttachment.Compatible 13 PowerOfTwoLength 1
          middle target ∧
        ¬Graph.InducedPathAttachment.Compatible 13 PowerOfTwoLength 2
          source target
  actualLabelsLegal : ∀
    (path : SimpleGraph.pathGraph 13 ↪g
      (Node18Context node17).G.object.graph)
    (outside : (Node18Context node17).G.Vertex)
    (_outsidePath : ∀ position : Fin 13, outside ≠ path position)
    (_attached : ∃ position,
      (Node18Context node17).G.object.graph.Adj outside (path position)),
    P13Legal
      (packedStaticInput.inducedPathAttachmentLabel 13
        (Node18Context node17) path outside)

/-- Node [18] is one framework-owned successor of the exact node-[17]
stage; no predecessor copy or application handoff is defined here. -/
abbrev Node18Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentSuccessor
    (@Node17Stage V) (fun _residual node17 => Node18Output node17) residual

/-- Public live-context cursor for the literal node-[18] successor. -/
abbrev Node18StageContext {V : Type u} {residual : InitialResidual V}
    (node18 : Node18Stage residual) :=
  Node18Context node18.previous

/-- Execute the paper-local CT10 table and attach its exact mathematical
certificate to the one accumulated ledger. -/
noncomputable def node18P13LabelAlgebra {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node17Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node18Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapStage fun _residual node17 =>
    let ctx := Node18Context node17
    {
      classificationStage := verifiedP13LabelCT10Stage ctx
      labelCount := p13LegalLabel_count
      sizeDistribution := p13LegalLabel_size_distribution
      relationSemantics := p13C_eq_one_iff
      curvatureSemantics := p13OmegaTwo_eq_one_iff
      actualLabelsLegal := by
        intro path outside outsidePath attached
        letI : DecidableRel ctx.G.object.graph.Adj :=
          ctx.G.object.input.decideAdj
        exact Graph.InducedPathAttachment.attachmentLabel_legal_of_avoids
          PowerOfTwoLength path outside outsidePath attached ctx.avoids
    }

/-- Continue the literal node-[17] branch through node [18]; branch routing
and preservation of every earlier fact are performed by the framework. -/
noncomputable def runInitialThroughNode18 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode17 residual).mapYesStage node18P13LabelAlgebra

/-- Node [18] performs exactly the bounded fixed-table audit already exposed
by the CT10 profile. -/
def node18LocalChecks : Nat := p13LabelClassification.checks

theorem node18LocalChecks_eq : node18LocalChecks = 167792 :=
  p13Label_check_count

#print axioms node18P13LabelAlgebra
#print axioms runInitialThroughNode18
#print axioms node18LocalChecks_eq

end Erdos64EG.Internal
