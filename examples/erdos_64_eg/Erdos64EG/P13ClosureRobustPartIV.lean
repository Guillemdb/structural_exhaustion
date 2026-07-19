import Erdos64EG.P13LargeBudgetNetDeficiency

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Non-enumerative closure-robust Part-IV spine

The manuscript's closure-robust route does not need a Boolean-product state
family.  Its genuine missing input is the same-context window-density theorem
owed at node `[24]`: the fixed cold-skeleton/F2--F5 analysis must supply its
packing ceiling, an exact finite form of the displayed window-density cap, and
the finite window-only inequality used by the quarter-budget arithmetic.  This
file gives that theorem a typed boundary and composes it
with the already verified node-`[47]` prefix and nodes `[55]`--`[56]`.

There is intentionally no constructor that derives the structural theorem
below from rank, entropy, a family of graphs, or a scan of ambient vertices.
Until the genuine fixed cold-skeleton/F2--F5 argument proves it, this production spine has no
closed inhabitant and the corresponding diagram stage remains partial.  In
particular, the rejected provisional cold-CT3 producer is not a constructor
for this boundary.
-/

/-- Integer normalization of the printed coefficient
`118.108581006`. -/
def p13WindowDensityRateNumerator : Nat := 118108581006

/-- Integer normalization of the near-cubic skeleton rate `1.5`. -/
def p13WindowDensitySkeletonNumerator : Nat := 1500000000

/-- Exact finite strengthening of the displayed window-only cap
`p13 / n <= 1.5 / 118.108581006`.  Keeping this predicate separate prevents a
tautological ceiling `windowCeiling := p13` from being mislabeled as a density
theorem. -/
def P13WindowDensityFiniteCap
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (windowCeiling : Nat) : Prop :=
  p13WindowDensityRateNumerator * windowCeiling ≤
    p13WindowDensitySkeletonNumerator *
      ctx.G.object.input.vertices.card

/-- Exact theorem owed by the genuine fixed cold-skeleton/F2--F5
window-density analysis at node
`[24]`.  Both fields concern the packing literally retained by node `[21]` on
the same minimal context. -/
structure P13WindowDensityStructuralTheorem
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type u where
  coverage : P13CoverageResidual ctx (p13MultiScalePackingPrefix node21)
  densityCap : P13WindowDensityFiniteCap ctx coverage.windowCeiling
  windowOnlyQuarter :
    P13QuarterNetBudget ctx (node21 := node21) coverage

/-- Typed node-`[24]` output.  Its constructor consumes the genuine structural
window-density theorem rather than accepting an author-selected terminal tag
or manufacturing a ceiling from later rank information. -/
structure VerifiedP13WindowDensityOutput
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type u where
  structural : P13WindowDensityStructuralTheorem ctx node21

namespace VerifiedP13WindowDensityOutput

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

/-- The coverage ceiling is exactly the one proved by the structural node-24
theorem. -/
def coverage (node24 : VerifiedP13WindowDensityOutput ctx node21) :
    P13CoverageResidual ctx (p13MultiScalePackingPrefix node21) :=
  node24.structural.coverage

/-- The strict finite window-only budget is retained verbatim from node 24. -/
theorem quarterBudget (node24 : VerifiedP13WindowDensityOutput ctx node21) :
    P13QuarterNetBudget ctx (node21 := node21) node24.coverage :=
  node24.structural.windowOnlyQuarter

/-- The output really contains the finite density cap named by node `[24]`;
it is not merely a downstream quarter-budget hypothesis. -/
theorem densityCap (node24 : VerifiedP13WindowDensityOutput ctx node21) :
    P13WindowDensityFiniteCap ctx node24.coverage.windowCeiling :=
  node24.structural.densityCap

/-- The certified ceiling bounds the actual packing, so the finite density
cap applies to `p13 ctx` itself. -/
theorem packingDensityCap (node24 : VerifiedP13WindowDensityOutput ctx node21) :
    p13WindowDensityRateNumerator * p13 ctx ≤
      p13WindowDensitySkeletonNumerator *
        ctx.G.object.input.vertices.card := by
  exact (Nat.mul_le_mul_left p13WindowDensityRateNumerator
    node24.coverage.packing_le).trans node24.densityCap

end VerifiedP13WindowDensityOutput

/-- Node `[47]` tied definitionally to the genuine node-`[24]` output on the
same context.  The rank prefix is retained for diagram provenance, although
the closure-robust arithmetic below does not consume its rank magnitude. -/
structure P13ClosureRobustNode47Prefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13WindowDensityOutput ctx node21) : Type (u + 3) where
  previous : P13DensityConnectedGlobalRankPrefix ctx node21 node24.coverage

/-- Recompute the already verified node-`[47]` ledger only after the actual
node-`[24]` theorem has fixed the same-context coverage output. -/
noncomputable def p13ClosureRobustNode47Prefix
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node24 : VerifiedP13WindowDensityOutput ctx node21) :
    P13ClosureRobustNode47Prefix ctx node21 node24 where
  previous := p13DensityConnectedGlobalRankPrefix ctx node21 node24.coverage

/-- Node `[55]`: the node-24 window-only inequality, routed through the exact
node-47 predecessor without using Boolean entropy or enumerating graph states.
-/
structure P13ClosureRobustNode55Budget
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13WindowDensityOutput ctx node21) : Type (u + 3) where
  previous : P13ClosureRobustNode47Prefix ctx node21 node24
  budget : P13QuarterNetBudget ctx (node21 := node21) node24.coverage

noncomputable def p13ClosureRobustNode55Budget
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node24 : VerifiedP13WindowDensityOutput ctx node21) :
    P13ClosureRobustNode55Budget ctx node21 node24 where
  previous := p13ClosureRobustNode47Prefix node24
  budget := node24.quarterBudget

/-- Node `[56]`: unconditional arithmetic once the structural node-24 theorem
is supplied.  The conclusion is the literal finite strict-quarter net-charge
bound, with no asymptotic division hidden in the interface. -/
def p13ClosureRobustNode56Handoff
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13WindowDensityOutput ctx node21}
    (node55 : P13ClosureRobustNode55Budget ctx node21 node24) :
    P13QuarterNetDeficiencyHandoff ctx node21 node24.coverage :=
  p13QuarterNetDeficiencyHandoff node55.previous.previous node55.budget

/-- Direct non-enumerative production composition from node `[24]` through
the same-context node `[47]` ledger to node `[56]`. -/
noncomputable def p13ClosureRobustPartIV
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node24 : VerifiedP13WindowDensityOutput ctx node21) :
    P13QuarterNetDeficiencyHandoff ctx node21 node24.coverage :=
  p13ClosureRobustNode56Handoff (p13ClosureRobustNode55Budget node24)

/-- The exact explicit net-charge conclusion exported by the production
closure-robust spine. -/
theorem p13ClosureRobustPartIV_strictQuarter
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node24 : VerifiedP13WindowDensityOutput ctx node21) :
    4 * ((p13RemainderCurvatureProfile ctx).positiveDeficiency -
        Graph.InducedPathWindowLedger.remainderSurplus ctx.G.object) <
      (p13RemainderVertices ctx).card := by
  exact p13NetDeficiency_strict_quarter_explicit
    (p13ClosureRobustPartIV node24).previous
    (p13ClosureRobustPartIV node24).budget

end Erdos64EG.Internal
