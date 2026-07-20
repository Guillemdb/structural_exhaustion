import Erdos64EG.Node36

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u


/-!
# Diagram node [37]: target-defective quotient

The no constructor of node [36] already is the complete branch-local terminal:
one original-interface context and one exact response mismatch.  Node [37]
only marks that constructor terminal.  It proves nothing about the universal
sibling and introduces no application-owned route payload.
-/

/-- Manuscript-facing name for node [36]'s concrete target-defect edge. -/
abbrev Node37TargetDefect {V : Type u} {residual : InitialResidual V}
    {node18 : Node18Stage residual}
    {bounded : Node19Low residual node18}
    {node21 : Node21Output node18 bounded}
    {low : Node22Low residual node18 bounded node21}
    {node31 : Node31Output node18 bounded node21 low}
    {rankDrop : Node32RankDrop node18}
    (node35 : Node35Output node18 bounded node21 low node31 rankDrop) : Prop :=
  Node36OriginalDefect node35

/-- Node [37] freezes only node [36]'s no leaf.  All other constructors are
transported by Core without an Erdős callback. -/
abbrev Node37Stage {V : Type u} (residual : InitialResidual V) :=
  (node35FocusedFamily V).NoTerminal
    (fun _ data => Node36OriginalUniversal data.output)
    (fun _ data => Node37TargetDefect data.output) residual

/-- Framework-owned `[36] --no--> [37]` terminal marker. -/
noncomputable def node37P13TargetDefect {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node36Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node37Stage V) :=
  Core.ResidualRefinement.State.StageNode.markFocusedYesContinuationNoTerminal
    (node35FocusedFamily V)

noncomputable def runInitialThroughNode37 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode36 residual).mapYesStage
    node37P13TargetDefect

def node37LocalChecks : Nat := 0

theorem node37LocalChecks_eq_zero : node37LocalChecks = 0 := rfl

#print axioms node37P13TargetDefect
#print axioms runInitialThroughNode37

end Erdos64EG.Internal
