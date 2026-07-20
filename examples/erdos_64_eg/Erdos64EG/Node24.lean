import Erdos64EG.Node23

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [24]: exact window-density output

Node [24] consumes only node [22]'s literal complementary inequality.  It
records that window-only cap and the symbolic implication used later on the
paper's high-entropy edge.  Node [23]'s yes-edge output is transported as the
already handled sibling, not eliminated by an assumption.  The high-entropy
premise itself is not asserted here: node [52] supplies the joint
window--remainder budget when its own branch is selected.
-/

/-- Fixed-point coefficient for the remainder's `1/10` entropy contribution,
at the same `10^9` normalization as node [22]. -/
def node24HighEntropyRemainderNumerator : Nat := 100000000

/-- The exact joint window--remainder feasibility premise supplied later by
the high-entropy branch.  This is a local scalar inequality; no state or graph
universe is enumerated. -/
def Node24HighEntropyJointBudget {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual) : Prop :=
  node24HighEntropyRemainderNumerator *
        ((Node21Context node18).G.object.input.vertices.card -
          13 * node22PackingCount node18) +
      node22WindowRateNumerator * node22PackingCount node18 ≤
    node22SkeletonRateNumerator *
      (Node21Context node18).G.object.input.vertices.card

/-- Exact fixed-point form of the paper's sharper high-entropy density cap. -/
def Node24HighEntropyCap {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual) : Prop :=
  116808581006 * node22PackingCount node18 ≤
    1400000000 * (Node21Context node18).G.object.input.vertices.card

/-- The paper's high-entropy arithmetic is a symbolic consequence of the
joint budget and the exact disjoint-packing support bound. -/
theorem node24HighEntropyCap_of_jointBudget {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual)
    (packingSupport : 13 * node22PackingCount node18 ≤
      (Node21Context node18).G.object.input.vertices.card)
    (joint : Node24HighEntropyJointBudget node18) :
    Node24HighEntropyCap node18 := by
  unfold Node24HighEntropyJointBudget at joint
  unfold Node24HighEntropyCap
  have partition :
      ((Node21Context node18).G.object.input.vertices.card -
          13 * node22PackingCount node18) +
        13 * node22PackingCount node18 =
      (Node21Context node18).G.object.input.vertices.card :=
    Nat.sub_add_cancel packingSupport
  norm_num [node24HighEntropyRemainderNumerator,
    node22WindowRateNumerator, node22SkeletonRateNumerator] at joint ⊢
  omega

/-- Reusable residual-wide form of node [24]'s high-entropy arithmetic.
Later paper nodes retrieve this theorem from the accumulated ledger rather
than reopening the branch payload or re-proving the packing support bound. -/
def Node24HighEntropyTransformer {V : Type u}
    (residual : InitialResidual V) : Prop :=
  ∀ node18 : Node18Stage residual,
    Node24HighEntropyJointBudget node18 → Node24HighEntropyCap node18

theorem node24HighEntropyTransformer {V : Type u}
    {residual : InitialResidual V} :
    Node24HighEntropyTransformer residual := by
  intro node18 joint
  exact node24HighEntropyCap_of_jointBudget node18
    (Graph.InducedPathMaximalPacking.packing_vertices_bound
      (Node21Context node18).G.object 13 node17ThirteenPositive)
    joint

/-- Only the mathematics introduced at node [24].  The exact branch proofs
and every predecessor stage are transported by Core's active cursor. -/
structure Node24Output {V : Type u} {residual : InitialResidual V}
    (node18 : Node18Stage residual)
    (_bounded : Node19Low residual node18)
    (_node21 : Node21Output node18 _bounded)
    (_low : Node22Low residual node18 _bounded _node21) : Type (u + 1) where
  windowDensity :
    node22WindowRateNumerator * node22PackingCount node18 ≤
      node22SkeletonRateNumerator *
        (Node21Context node18).G.object.input.vertices.card
  packingSupport : 13 * node22PackingCount node18 ≤
    (Node21Context node18).G.object.input.vertices.card
  highEntropy : Node24HighEntropyJointBudget node18 →
    Node24HighEntropyCap node18

/-- The surviving node-[24] cursor.  Node [20]'s pre-existing leaf is the
framework bypass; the node-[22] no leaf carries only node [24]'s new output. -/
abbrev Node24Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentDecisionOnNoNoAfterYes
    (@Node18Stage V) (@Node19High V) (@Node19Low V)
    (fun _residual node18 bounded => Node21Output node18 bounded)
    (@Node22High V) (@Node22Low V)
    (fun _residual node18 bounded node21 high =>
      Node23Output node18 bounded node21 high)
    (fun _residual node18 bounded node21 low =>
      Node24Output node18 bounded node21 low) residual

/-- The framework exposes node [24]'s reusable scalar transformer through the
same accumulated stage ledger. -/
instance node24StageEntailsHighEntropyTransformer {V : Type u} :
    Core.ResidualRefinement.State.StageEntails
      (@Node24Stage V) (@Node24HighEntropyTransformer V) where
  prove := fun _stage => node24HighEntropyTransformer

/-- Framework-owned `[23] -> [24]` continuation.  The Erdős layer supplies
only the two local arithmetic certificates. -/
noncomputable def node24P13DensityBounds {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node23Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node24Stage V) :=
  Core.ResidualRefinement.State.StageNode.continueDependentDecisionOnNoNoAfterYes
    fun _residual node18 _bounded _node21 low =>
        let packed := Graph.InducedPathMaximalPacking.packing_vertices_bound
          (Node21Context node18).G.object 13 node17ThirteenPositive
        {
          windowDensity := low
          packingSupport := packed
          highEntropy := node24HighEntropyCap_of_jointBudget node18 packed
        }

noncomputable def runInitialThroughNode24 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode23 residual).mapYesStage
    node24P13DensityBounds

/-- Node [24] uses only symbolic arithmetic and a stored packing theorem. -/
def node24LocalChecks : Nat := 0

theorem node24LocalChecks_eq_zero : node24LocalChecks = 0 := rfl

#print axioms node24HighEntropyCap_of_jointBudget
#print axioms node24P13DensityBounds
#print axioms runInitialThroughNode24

end Erdos64EG.Internal
