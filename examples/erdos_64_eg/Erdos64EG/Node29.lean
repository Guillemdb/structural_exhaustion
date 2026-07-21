import Erdos64EG.Node28
import Erdos64EG.Shared.CT15RemainderCurvature

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

structure Node29Output {V : Type u} {residual : InitialResidual V}
    (node18 : Node18Stage residual)
    (_bounded : Node19Low residual node18)
    (_node21 : Node21Output node18 _bounded)
    (_low : Node22Low residual node18 _bounded _node21) : Type (u + 1) where
  deficiencyLedgerExact :
    (p13RemainderCurvatureProfile
        (Node21Context node18)).positiveDeficiency =
      (p13RemainderDeficiencyProfile
        (Node21Context node18)).positiveDeficiency
  deficiency_le_boundaryIncidences :
    (p13RemainderCurvatureProfile
        (Node21Context node18)).positiveDeficiency ≤
      (p13RemainderCurvatureProfile
        (Node21Context node18)).boundaryIncidences
  boundaryIncidences_le_windowTokens :
    (p13RemainderCurvatureProfile
        (Node21Context node18)).boundaryIncidences ≤
      Graph.InducedPathWindowLedger.tokenCount
        (Node21Context node18).G.object
  tokenCountExact :
    Graph.InducedPathWindowLedger.tokenCount
        (Node21Context node18).G.object =
      15 * Graph.InducedPathWindowLedger.packingNumber
          (Node21Context node18).G.object +
        Graph.InducedPathWindowLedger.windowSurplus
          (Node21Context node18).G.object
  incidenceSupply :
    (p13RemainderCurvatureProfile (Node21Context node18)).positiveDeficiency ≤
      15 * Graph.InducedPathWindowLedger.packingNumber
        (Node21Context node18).G.object +
      Graph.InducedPathWindowLedger.windowSurplus
        (Node21Context node18).G.object
  surplusPartition :
    Graph.InducedPathWindowLedger.windowSurplus
          (Node21Context node18).G.object +
        Graph.InducedPathWindowLedger.remainderSurplus
          (Node21Context node18).G.object =
      Graph.InducedPathWindowLedger.totalSurplus
        (Node21Context node18).G.object
  windowSurplus_le_total :
    Graph.InducedPathWindowLedger.windowSurplus
        (Node21Context node18).G.object ≤
      Graph.InducedPathWindowLedger.totalSurplus
        (Node21Context node18).G.object
  totalSurplusSupply :
    (p13RemainderCurvatureProfile (Node21Context node18)).positiveDeficiency ≤
      15 * Graph.InducedPathWindowLedger.packingNumber
          (Node21Context node18).G.object +
        Graph.InducedPathWindowLedger.totalSurplus
          (Node21Context node18).G.object
  /-- The subtraction in the manuscript is signed.  Stating it in `Int`
  retains the negative case instead of silently truncating both sides at
  zero. -/
  surplusAdjustedSupply :
    ((p13RemainderCurvatureProfile
        (Node21Context node18)).positiveDeficiency : Int) -
          (Graph.InducedPathWindowLedger.remainderSurplus
            (Node21Context node18).G.object : Int) ≤
      ((15 * Graph.InducedPathWindowLedger.packingNumber
              (Node21Context node18).G.object +
            Graph.InducedPathWindowLedger.windowSurplus
              (Node21Context node18).G.object : Nat) : Int) -
        (Graph.InducedPathWindowLedger.remainderSurplus
          (Node21Context node18).G.object : Int)
  /-- Exact finite producer for the paper's `15 p₁₃ + o(n)` statement.
  The inherited node-[19] certificate makes the displayed excess
  `O(√n)`, hence `o(n)`, without storing another copy of that certificate. -/
  incidenceErrorSquared :
    ((p13RemainderCurvatureProfile
          (Node21Context node18)).positiveDeficiency -
        15 * Graph.InducedPathWindowLedger.packingNumber
          (Node21Context node18).G.object) ^ 2 ≤
      node19SurplusCoefficient *
        (Node21Context node18).G.object.input.vertices.card
  localWork :
    Graph.InducedPathWindowLedger.checks
        (Node21Context node18).G.object ≤
      13 * (Node21Context node18).G.object.input.vertices.card ^ 2

abbrev Node29Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentDecisionOnNoNoAfterYes
    (@Node18Stage V) (@Node19High V) (@Node19Low V)
    (fun _residual node18 bounded => Node21Output node18 bounded)
    (@Node22High V) (@Node22Low V)
    (fun _residual node18 bounded node21 high =>
      Node23Output node18 bounded node21 high)
    (fun _residual node18 bounded node21 low =>
      Node29Output node18 bounded node21 low) residual

/-- Node [29]'s reusable ledger consequence in the exact finite form later
needed by node [56]: the actual remainder numerator `def⁺(R)-σ_R` is bounded
by the packing/window budget transported along the same residual. -/
def Node29RemainderNetBudgetAvailable {V : Type u}
    (residual : InitialResidual V) : Prop :=
  ∀ (node18 : Node18Stage residual)
    (bounded : Node19Low residual node18)
    (node21 : Node21Output node18 bounded)
    (_low : Node22Low residual node18 bounded node21),
    (p13RemainderCurvatureProfile (Node21Context node18)).positiveDeficiency -
        Graph.InducedPathWindowLedger.remainderSurplus
          (Node21Context node18).G.object ≤
      15 * Graph.InducedPathWindowLedger.packingNumber
          (Node21Context node18).G.object +
        Graph.InducedPathWindowLedger.windowSurplus
          (Node21Context node18).G.object -
        Graph.InducedPathWindowLedger.remainderSurplus
          (Node21Context node18).G.object

theorem node29RemainderNetBudgetAvailable {V : Type u}
    {residual : InitialResidual V} :
    Node29RemainderNetBudgetAvailable residual := by
  intro node18 _bounded _node21 _low
  let ctx := Node21Context node18
  exact
    Graph.InducedPathWindowLedger.remainderPositiveDeficiency_sub_remainderSurplus_le
      ctx.G.object
      (fun vertex => ctx.baseline.trans
        (ctx.G.object.minDegree_le_degree vertex))

/-- Register node [29]'s finite net-budget ledger consequence once at its
producer.  Later nodes retrieve this through Core queries rather than
reopening incidence accounting. -/
instance node29StageEntailsRemainderNetBudgetAvailable {V : Type u} :
    Core.ResidualRefinement.State.StageEntails
      (@Node29Stage V) (@Node29RemainderNetBudgetAvailable V) where
  prove := fun _stage => node29RemainderNetBudgetAvailable

noncomputable def node29P13ExternalIncidenceSupply {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node28Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node29Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapDependentDecisionOnNoNoAfterYes
    (Current := fun _ node18 bounded node21 low =>
      Node28Output node18 bounded node21 low)
    (Next := fun _ node18 bounded node21 low =>
      Node29Output node18 bounded node21 low)
    fun _residual node18 bounded node21 low
        (node28 : Node28Output node18 bounded node21 low) => by
      let ctx := Node21Context node18
      have _ := node28.exactFormula
      have incidenceSupply :=
        p13Remainder_positiveDeficiency_le_fifteen_mul_packing_add_surplus ctx
      have surplusPartition :=
        Graph.InducedPathWindowLedger.window_add_remainder_eq_totalSurplus
          ctx.G.object
      have windowSurplus_le_total :
          Graph.InducedPathWindowLedger.windowSurplus ctx.G.object ≤
            Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
        omega
      have totalSurplusSupply :
          (p13RemainderCurvatureProfile ctx).positiveDeficiency ≤
            15 * Graph.InducedPathWindowLedger.packingNumber ctx.G.object +
              Graph.InducedPathWindowLedger.totalSurplus ctx.G.object :=
        incidenceSupply.trans (Nat.add_le_add_left windowSurplus_le_total _)
      exact {
        deficiencyLedgerExact := p13Curvature_positiveDeficiency_eq_previous ctx
        deficiency_le_boundaryIncidences :=
          (p13RemainderCurvatureProfile ctx).positiveDeficiency_le_boundaryIncidences
            (fun vertex => ctx.baseline.trans
              (ctx.G.object.minDegree_le_degree vertex))
        boundaryIncidences_le_windowTokens :=
          Graph.InducedPathWindowLedger.remainderBoundaryIncidences_le_tokenCount
            ctx.G.object
        tokenCountExact :=
          Graph.InducedPathWindowLedger.tokenCount_eq_fifteen_mul_packing_add_surplus
            ctx.G.object (fun vertex => ctx.baseline.trans
              (ctx.G.object.minDegree_le_degree vertex))
        incidenceSupply := incidenceSupply
        surplusPartition := surplusPartition
        windowSurplus_le_total := windowSurplus_le_total
        totalSurplusSupply := totalSurplusSupply
        surplusAdjustedSupply := by
          have incidenceSupplyInt :
              ((p13RemainderCurvatureProfile ctx).positiveDeficiency : Int) ≤
                ((15 * Graph.InducedPathWindowLedger.packingNumber ctx.G.object +
                    Graph.InducedPathWindowLedger.windowSurplus
                      ctx.G.object : Nat) : Int) := by
            exact_mod_cast incidenceSupply
          exact sub_le_sub_right incidenceSupplyInt _
        incidenceErrorSquared := by
          have excessLe :
              (p13RemainderCurvatureProfile ctx).positiveDeficiency -
                  15 * Graph.InducedPathWindowLedger.packingNumber ctx.G.object ≤
                Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
            omega
          have squared := Nat.pow_le_pow_left excessLe 2
          change Graph.InducedPathWindowLedger.totalSurplus ctx.G.object ^ 2 ≤
              node19SurplusCoefficient *
                ctx.G.object.input.vertices.card at bounded
          exact squared.trans bounded
        localWork :=
          Graph.InducedPathWindowLedger.checks_le_thirteen_mul_square
            ctx.G.object
      }

noncomputable def runInitialThroughNode29 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode28 residual).mapYesStage
    node29P13ExternalIncidenceSupply

def node29LocalChecks : Nat := 0
theorem node29LocalChecks_eq_zero : node29LocalChecks = 0 := rfl

#print axioms node29P13ExternalIncidenceSupply
#print axioms runInitialThroughNode29

end Erdos64EG.Internal
