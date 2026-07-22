import Erdos64EG.Node8
import HypostructureErdos64EG.Node8
import HypostructureParity.Erdos64EG.Node7

namespace HypostructureParity.Erdos64EG.Node8

open Hypostructure

universe u

/-!
# Diagram node 8 parity

Node `[8]` is the no-return branch from node `[6]`.  Its normalized
Hypostructure surface is the graph-owned no-proper-baseline certificate:
every certified proper subgraph of the selected minimal counterexample fails
the minimum-degree-three baseline, and each hypothetical proper core closes by
Core strict progress.
-/

private noncomputable abbrev rootNode4Stage
    (root : HypostructureErdos64EG.InitialResidual.{u}) :
    HypostructureErdos64EG.Node4Stage.{u} :=
  HypostructureErdos64EG.node4
    (HypostructureErdos64EG.node2
      (HypostructureErdos64EG.node1 root))

private noncomputable abbrev rootNode5Stage
    (root : HypostructureErdos64EG.InitialResidual.{u}) :
    HypostructureErdos64EG.Node5Stage.{u} :=
  HypostructureErdos64EG.node5 (rootNode4Stage root)

private noncomputable abbrev rootNode6Stage
    (root : HypostructureErdos64EG.InitialResidual.{u}) :
    HypostructureErdos64EG.Node6Stage.{u} :=
  HypostructureErdos64EG.node6 (rootNode5Stage root)

private noncomputable abbrev rootNode6AvoidingStage
    (root : HypostructureErdos64EG.InitialResidual.{u}) :
    HypostructureErdos64EG.Node6AvoidingStage.{u} :=
  HypostructureErdos64EG.node6ContinueAvoiding (rootNode6Stage root)

private noncomputable abbrev rootNode8Stage
    (root : HypostructureErdos64EG.InitialResidual.{u}) :
    HypostructureErdos64EG.Node8Stage.{u} :=
  HypostructureErdos64EG.node8 (rootNode6AvoidingStage root)

/-- The new node-8 certificate excludes every certified proper subgraph
that would preserve the baseline. -/
theorem selected_noProperCore
    (root : HypostructureErdos64EG.InitialResidual.{u})
    (active :
      HypostructureErdos64EG.Node8Focus.Active
        (rootNode8Stage root))
    (subgraph : Graph.ProperSubgraph
      (HypostructureErdos64EG.node4ContextAtNode6AvoidingQuery.read
        (rootNode6AvoidingStage root) active).G) :
    Not (HypostructureErdos64EG.Baseline subgraph.value) :=
  HypostructureErdos64EG.node8_noProperCore
    (rootNode8Stage root) active subgraph

/-- A hypothetical baseline-preserving proper subgraph closes by Core's
strict-progress mechanism. -/
theorem selected_closure_mechanism
    (root : HypostructureErdos64EG.InitialResidual.{u})
    (active :
      HypostructureErdos64EG.Node8Focus.Active
        (rootNode8Stage root))
    (subgraph : Graph.ProperSubgraph
      (HypostructureErdos64EG.node4ContextAtNode6AvoidingQuery.read
        (rootNode6AvoidingStage root) active).G)
    (baseline : HypostructureErdos64EG.Baseline subgraph.value) :
    ((HypostructureErdos64EG.node8CertificateQuery.read
      (rootNode8Stage root) active).closure subgraph baseline).mechanism =
        Core.Closure.Mechanism.strictProgress :=
  HypostructureErdos64EG.node8_closure_mechanism
    (rootNode8Stage root) active subgraph baseline

/-- Node 8 parity preserves the production focused-selection work bound. -/
theorem node8_work_bounded
    (previous : HypostructureErdos64EG.Node6AvoidingStage.{u}) :
    HypostructureErdos64EG.Node6AvoidingFocus.selectionBudget.Within previous
      (HypostructureErdos64EG.node8Counted previous).checks :=
  HypostructureErdos64EG.node8Counted_work_bounded previous

/-- The legacy node-8 output states the same paper-visible no-proper-core
predicate on its selected context. -/
theorem legacy_noProperCore {V : Type u}
    {residual : _root_.Erdos64EG.Internal.InitialResidual V}
    (node7 : _root_.Erdos64EG.Internal.Node7Stage residual)
    (output : _root_.Erdos64EG.Internal.Node8Output node7) :
    ∀ subgraph :
      _root_.StructuralExhaustion.Graph.PackedFiniteObject.ProperSubgraph
        output.context.G,
      ¬_root_.Erdos64EG.Internal.packedStaticInput.problem.Baseline
        subgraph.value :=
  _root_.Erdos64EG.Internal.node8_noProperCore node7 output

/-- The legacy CT2 certificate is retained as parity evidence for the older
implementation shape; the new node uses Core strict-progress closure directly. -/
theorem legacy_ct2_certificate {V : Type u}
    {residual : _root_.Erdos64EG.Internal.InitialResidual V}
    (node7 : _root_.Erdos64EG.Internal.Node7Stage residual)
    (output : _root_.Erdos64EG.Internal.Node8Output node7)
    (subgraph :
      _root_.StructuralExhaustion.Graph.PackedFiniteObject.ProperSubgraph
        output.context.G)
    (baseline :
      _root_.Erdos64EG.Internal.packedStaticInput.problem.Baseline
        subgraph.value) :
    (_root_.Erdos64EG.Internal.packedStaticInput.properSubgraphCT2Run
        output.context subgraph baseline).terminal =
        .deletionC2 ∧
      (_root_.Erdos64EG.Internal.packedStaticInput.properSubgraphCT2Run
        output.context subgraph baseline).trace =
        [.entry, .deletionDecision, .deletionC2Terminal] ∧
      (_root_.Erdos64EG.Internal.packedStaticInput.properSubgraphCT2Run
        output.context subgraph baseline).checks = 1 :=
  _root_.Erdos64EG.Internal.node8_ct2_certificate
    node7 output subgraph baseline

#print axioms selected_noProperCore
#print axioms selected_closure_mechanism
#print axioms node8_work_bounded
#print axioms legacy_noProperCore
#print axioms legacy_ct2_certificate

end HypostructureParity.Erdos64EG.Node8
