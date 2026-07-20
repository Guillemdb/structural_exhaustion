import Erdos64EG.Node22

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [23]: dense-window entropy-overflow output

Node [22]'s strict branch is the exact finite window-entropy overflow
inequality.  Node [23] is the payload on that literal yes constructor; it does
not assume that the constructor is empty.  The complementary node-[22] no
constructor remains available to node [24].
-/

/-- The yes-edge proof is exactly the manuscript's strict cross-multiplied
window overflow, with no downstream cold or node-[24] conclusion. -/
theorem node23StrictWindowOverflow {V : Type u}
    {residual : InitialResidual V} {node18 : Node18Stage residual}
    {bounded : Node19Low residual node18}
    {node21 : Node21Output node18 bounded}
    (high : Node22High residual node18 bounded node21) :
    node22SkeletonRateNumerator *
        (Node21Context node18).G.object.input.vertices.card <
      node22WindowRateNumerator * node22PackingCount node18 :=
  high

/-- Node [23]'s sole new output.  Its inequality is the exact proof already
selected by node [22]'s yes constructor, now named for its diagram consumer. -/
structure Node23Output {V : Type u} {residual : InitialResidual V}
    (node18 : Node18Stage residual)
    (_bounded : Node19Low residual node18)
    (_node21 : Node21Output node18 _bounded)
    (_high : Node22High residual node18 _bounded _node21) : Type where
  strictWindowOverflow :
    node22SkeletonRateNumerator *
        (Node21Context node18).G.object.input.vertices.card <
      node22WindowRateNumerator * node22PackingCount node18

/-- The pre-existing node-[20] leaf and node [22]'s complementary no edge are
retained literally while the yes edge acquires node [23]'s output. -/
abbrev Node23Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentDecisionOnNoYesContinuation
    (@Node18Stage V) (@Node19High V) (@Node19Low V)
    (fun _residual node18 bounded => Node21Output node18 bounded)
    (@Node22High V) (@Node22Low V)
    (fun _residual node18 bounded node21 high =>
      Node23Output node18 bounded node21 high) residual

/-- Framework-owned continuation of node [22]'s exact yes constructor. -/
noncomputable def node23P13WindowEntropyOverflow {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node22Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node23Stage V) :=
  Core.ResidualRefinement.State.StageNode.continueDependentDecisionOnNoYes
    fun _residual _node18 _bounded node21 high =>
      { strictWindowOverflow :=
          node23StrictWindowOverflow (node21 := node21) high }

noncomputable def runInitialThroughNode23 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode22 residual).mapYesStage
    node23P13WindowEntropyOverflow

#print axioms node23StrictWindowOverflow
#print axioms node23P13WindowEntropyOverflow

end Erdos64EG.Internal
