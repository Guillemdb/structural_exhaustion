import Erdos64EG.Node19

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [20]: the non-near-cubic accounting branch

Node `[20]` introduces no second mathematical assertion.  In the original
diagram it is the name of the strict (`yes`) constructor produced by node
`[19]`; its internal mathematics is expanded separately by nodes `[125]`--
`[144]`.  Consequently this module gives that constructor a manuscript name
without restaging it, copying its predecessor, or constructing an
application-owned handoff.

The eventual `[20] -> [125]` continuation must use the framework's dependent
yes-branch continuation on `Node19Stage`.  It must not consume a detached
`NonNearCubicScaleResidual`.
-/

/-- The exact proposition labeling the existing edge `[19] --yes--> [20]`.
This is definitionally the strict constructor of the framework-owned node-19
decision. -/
abbrev Node20Entry {V : Type u} (residual : InitialResidual V)
    (node18 : Node18Stage residual) : Prop :=
  Node19High residual node18

/-- Node `[20]` is represented by the literal node-[19] decision stage.  No
new stage is appended here because the paper introduces no new fact between
the decision constructor and the Part-X expansion entry `[125]`. -/
abbrev Node20SourceStage {V : Type u} (residual : InitialResidual V) :=
  Node19Stage residual

/-- The branch name is definitionally exact; this theorem is the local
kernel-checked identity used by manuscript/web provenance. -/
theorem node20Entry_iff_node19High {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual) :
    Node20Entry residual node18 ↔ Node19High residual node18 :=
  Iff.rfl

/-- Node `[20]` performs no additional primitive check beyond node `[19]`'s
single symbolic comparison. -/
def node20LocalChecks : Nat := 0

theorem node20LocalChecks_eq_zero : node20LocalChecks = 0 := rfl

#print axioms node20Entry_iff_node19High

end Erdos64EG.Internal
