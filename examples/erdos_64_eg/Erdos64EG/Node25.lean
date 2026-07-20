import Erdos64EG.Node24
import StructuralExhaustion.Core.DensityAsymptoticTransport

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [25]: Residual A

This node maps the surviving node-[24] cursor once.  Its only new payload is
the canonical complement of the already selected maximum induced-`P₁₃`
packing, together with the exact scaled largeness and hereditary
`P₁₃`-freeness asserted by the paper.
-/

/-- Exact numerator of the forced remainder proportion
`118108581006 - 13 * 1500000000`. -/
def node25RemainderRateNumerator : Nat := 98608581006

/-- Residual A is definitionally the canonical complement selected by the
existing induced-path packing profile; node [25] does not choose another
vertex set or graph. -/
noncomputable abbrev Node25Remainder {V : Type u} {residual : InitialResidual V}
    (node18 : Node18Stage residual) :=
  p13Remainder (Node21Context node18)

/-- Only the mathematics first attached at node [25]. -/
structure Node25Output {V : Type u} {residual : InitialResidual V}
    (node18 : Node18Stage residual)
    (_bounded : Node19Low residual node18)
    (_node21 : Node21Output node18 _bounded)
    (_low : Node22Low residual node18 _bounded _node21) : Type (u + 1) where
  exactPartition :
    (p13RemainderVertices (Node21Context node18)).card +
        13 * p13 (Node21Context node18) =
      (Node21Context node18).G.object.input.vertices.card
  scaledLarge :
    node25RemainderRateNumerator *
        (Node21Context node18).G.object.input.vertices.card ≤
      node22WindowRateNumerator *
        (p13RemainderVertices (Node21Context node18)).card
  remainderFree :
    Graph.InducedPathFree (Node25Remainder node18).graph 13
  componentwiseFree :
    ∀ vertices : Set (P13RemainderVertex (Node21Context node18)),
      Graph.InducedPathFree
        ((Node25Remainder node18).graph.induce vertices) 13

/-- The active cursor after node [25].  Core transports the bypass and all
branch proofs; the application changes only the current local payload. -/
abbrev Node25Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentDecisionOnNoNoAfterYes
    (@Node18Stage V) (@Node19High V) (@Node19Low V)
    (fun _residual node18 bounded => Node21Output node18 bounded)
    (@Node22High V) (@Node22Low V)
    (fun _residual node18 bounded node21 high =>
      Node23Output node18 bounded node21 high)
    (fun _residual node18 bounded node21 low =>
      Node25Output node18 bounded node21 low) residual

/-- Framework-owned `[24] -> [25]` successor.  The proof uses the literal
node-[24] density certificate and the reusable symbolic packing theorems; it
performs no graph scan. -/
noncomputable def node25P13LargeRemainder {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node24Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node25Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapDependentDecisionOnNoNoAfterYes
    (Current := fun _ node18 bounded node21 low =>
      Node24Output node18 bounded node21 low)
    (Next := fun _ node18 bounded node21 low =>
      Node25Output node18 bounded node21 low)
    fun _residual node18 bounded node21 low
        (node24 : Node24Output node18 bounded node21 low) => by
      let ctx := Node21Context node18
      have partition := p13Remainder_partition ctx
      have scaledLarge :
          node25RemainderRateNumerator *
              ctx.G.object.input.vertices.card ≤
            node22WindowRateNumerator *
              (p13RemainderVertices ctx).card := by
        exact Core.DensityAsymptoticTransport.nat_partition_complement_lower
          (rate := node22WindowRateNumerator)
          (complementRate := node25RemainderRateNumerator)
          (width := 13)
          (budget := node22SkeletonRateNumerator)
          (mass := node22PackingCount node18)
          (remainder := (p13RemainderVertices ctx).card)
          (order := ctx.G.object.input.vertices.card)
          (by norm_num [node22WindowRateNumerator,
            node25RemainderRateNumerator, node22SkeletonRateNumerator])
          partition node24.windowDensity
      exact {
        exactPartition := partition
        scaledLarge := scaledLarge
        remainderFree := p13Remainder_free ctx
        componentwiseFree := p13Remainder_componentwise_free ctx
      }

noncomputable def runInitialThroughNode25 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode24 residual).mapYesStage
    node25P13LargeRemainder

/-- Node [25] is purely symbolic: it reuses the selected packing and performs
no new local semantic checks. -/
def node25LocalChecks : Nat := 0

theorem node25LocalChecks_eq_zero : node25LocalChecks = 0 := rfl

#print axioms node25P13LargeRemainder
#print axioms runInitialThroughNode25

end Erdos64EG.Internal
