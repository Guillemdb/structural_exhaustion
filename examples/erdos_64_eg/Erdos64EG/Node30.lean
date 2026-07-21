import Erdos64EG.Node29
import Erdos64EG.Shared.P13Node30Constants

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-! The exact finite constants used by the window-only node-[30] transport. -/

/-- Numerator of the window-only wedge coefficient after eliminating the
packed-window density from the exact remainder partition. -/
def node30WindowWedgeRateNumerator : Nat :=
  3 * node25RemainderRateNumerator -
    30 * node22SkeletonRateNumerator

/-- The manuscript's window-only positive-deficiency coefficient, retained
as its exact rational value. -/
noncomputable def node30WindowDeficiencyRate : ℝ :=
  ((15 * node22SkeletonRateNumerator : Nat) : ℝ) /
    (node25RemainderRateNumerator : ℝ)

/-- The exact window-only wedge coefficient `3 - 2 τ_win`. -/
noncomputable def node30OmegaWindow : ℝ :=
  3 - 2 * node30WindowDeficiencyRate

theorem node30WindowWedgeRateNumerator_eq :
    node30WindowWedgeRateNumerator = 250825743018 := by
  norm_num [node30WindowWedgeRateNumerator,
    node25RemainderRateNumerator, node22SkeletonRateNumerator]

/-- Rigorous lower approximation to the decimal printed in the manuscript. -/
theorem node30OmegaWindow_gt_printed :
    (254365026308 / 100000000000 : ℝ) < node30OmegaWindow := by
  norm_num [node30OmegaWindow, node30WindowDeficiencyRate,
    node25RemainderRateNumerator, node22SkeletonRateNumerator]

structure Node30Output {V : Type u} {residual : InitialResidual V}
    (node18 : Node18Stage residual)
    (_bounded : Node19Low residual node18)
    (_node21 : Node21Output node18 _bounded)
    (_low : Node22Low residual node18 _bounded _node21) : Type (u + 1) where
  componentWedgeFloor : ∀ component : Finset (Node21Context node18).G.Vertex,
    let profile : Graph.PositiveDeficiencyWedge.Profile
        (Node21Context node18).G.object := { core := component }
    3 * component.card - 2 * profile.positiveDeficiency ≤
      profile.wedgeCount
  remainderWedgeFloor :
    3 * (p13RemainderVertices (Node21Context node18)).card -
        2 * (p13RemainderCurvatureProfile
          (Node21Context node18)).positiveDeficiency ≤
      (p13RemainderCurvatureProfile (Node21Context node18)).wedgeCount
  windowFiniteSupply :
    3 * (p13RemainderVertices (Node21Context node18)).card ≤
      (p13RemainderCurvatureProfile (Node21Context node18)).wedgeCount +
        30 * Graph.InducedPathWindowLedger.packingNumber
          (Node21Context node18).G.object +
        2 * Graph.InducedPathWindowLedger.totalSurplus
          (Node21Context node18).G.object
  /-- Exact finite, error-bearing form of the window-only wedge coefficient.
  The total-surplus term is the finite quantity later made `o(|R|)` by the
  already accumulated node-[19] certificate. -/
  windowFiniteError :
    node30WindowWedgeRateNumerator *
        (p13RemainderVertices (Node21Context node18)).card ≤
      node25RemainderRateNumerator *
          (p13RemainderCurvatureProfile
            (Node21Context node18)).wedgeCount +
        2 * node25RemainderRateNumerator *
          Graph.InducedPathWindowLedger.totalSurplus
            (Node21Context node18).G.object
  /-- Exact finite producer for the large-budget net-deficiency cap:
  after multiplying by the fixed remainder denominator, the window-supplied
  deficiency is bounded by the paper's `τ_win` numerator plus the inherited
  near-cubic surplus error. -/
  netDeficiencyFiniteCap :
    node25RemainderRateNumerator *
        (p13RemainderCurvatureProfile
          (Node21Context node18)).positiveDeficiency ≤
      15 * node22SkeletonRateNumerator *
          (p13RemainderVertices (Node21Context node18)).card +
        node25RemainderRateNumerator *
          Graph.InducedPathWindowLedger.totalSurplus
            (Node21Context node18).G.object
  rateTransport : ∀ (rate error : ℝ),
    ((p13RemainderCurvatureProfile
      (Node21Context node18)).positiveDeficiency : ℝ) ≤
        rate * (p13RemainderVertices (Node21Context node18)).card + error →
      (3 - 2 * rate) *
          (p13RemainderVertices (Node21Context node18)).card ≤
        (p13RemainderCurvatureProfile (Node21Context node18)).wedgeCount +
          2 * error
  windowRateTransport : ∀ error : ℝ,
    ((p13RemainderCurvatureProfile
      (Node21Context node18)).positiveDeficiency : ℝ) ≤
        node30WindowDeficiencyRate *
          (p13RemainderVertices (Node21Context node18)).card + error →
      (254365026308 / 100000000000 : ℝ) *
          (p13RemainderVertices (Node21Context node18)).card ≤
        (p13RemainderCurvatureProfile (Node21Context node18)).wedgeCount +
          2 * error
  highEntropyTransport : ∀ error : ℝ,
    ((p13RemainderCurvatureProfile
      (Node21Context node18)).positiveDeficiency : ℝ) ≤
        p13Node30HighEntropyDeficiencyRate *
          (p13RemainderVertices (Node21Context node18)).card + error →
      p13Node30OmegaHighEntropy *
          (p13RemainderVertices (Node21Context node18)).card ≤
        (p13RemainderCurvatureProfile (Node21Context node18)).wedgeCount +
          2 * error
  localWork :
    (p13RemainderCurvatureProfile (Node21Context node18)).checks ≤
      (Node21Context node18).G.object.input.vertices.card ^ 2

abbrev Node30Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentDecisionOnNoNoAfterYes
    (@Node18Stage V) (@Node19High V) (@Node19Low V)
    (fun _residual node18 bounded => Node21Output node18 bounded)
    (@Node22High V) (@Node22Low V)
    (fun _residual node18 bounded node21 high =>
      Node23Output node18 bounded node21 high)
    (fun _residual node18 bounded node21 low =>
      Node30Output node18 bounded node21 low) residual

noncomputable def node30P13WedgeLower {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node29Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node30Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapDependentDecisionOnNoNoAfterYes
    (Current := fun _ node18 bounded node21 low =>
      Node29Output node18 bounded node21 low)
    (Next := fun _ node18 bounded node21 low =>
      Node30Output node18 bounded node21 low)
    fun _residual node18 bounded node21 low
        (node29 : Node29Output node18 bounded node21 low) => by
      let ctx := Node21Context node18
      have partition := p13Remainder_partition ctx
      rw [p13,
        ← Graph.InducedPathWindowLedger.packingNumber_eq_inducedPathPacking]
        at partition
      have density :
          node22WindowRateNumerator *
              Graph.InducedPathWindowLedger.packingNumber ctx.G.object ≤
            node22SkeletonRateNumerator *
              ctx.G.object.input.vertices.card := by
        change node22WindowRateNumerator *
              Graph.InducedPathWindowLedger.packingNumber ctx.G.object ≤
            node22SkeletonRateNumerator *
              ctx.G.object.input.vertices.card at low
        exact low
      have remainderDensity :
          node25RemainderRateNumerator *
              Graph.InducedPathWindowLedger.packingNumber ctx.G.object ≤
            node22SkeletonRateNumerator *
              (p13RemainderVertices ctx).card := by
        have densityScaled :
            node22WindowRateNumerator *
                  Graph.InducedPathWindowLedger.packingNumber ctx.G.object * 1 ≤
                node22SkeletonRateNumerator *
                  ctx.G.object.input.vertices.card * 1 + 0 := by
          simpa using density
        simpa using
          (Core.DensityAsymptoticTransport.nat_partition_density_with_error
            (rate := node22WindowRateNumerator)
            (remainderRate := node25RemainderRateNumerator)
            (width := 13)
            (skeleton := node22SkeletonRateNumerator)
            (mass := Graph.InducedPathWindowLedger.packingNumber ctx.G.object)
            (remainder := (p13RemainderVertices ctx).card)
            (order := ctx.G.object.input.vertices.card)
            (scale := 1) (error := 0)
            (by norm_num [node22WindowRateNumerator,
              node25RemainderRateNumerator, node22SkeletonRateNumerator])
            partition densityScaled)
      have windowFiniteSupply :
          3 * (p13RemainderVertices ctx).card ≤
            (p13RemainderCurvatureProfile ctx).wedgeCount +
              30 * Graph.InducedPathWindowLedger.packingNumber ctx.G.object +
              2 * Graph.InducedPathWindowLedger.totalSurplus
                ctx.G.object := by
        have totalSupply :
            (p13RemainderCurvatureProfile ctx).positiveDeficiency ≤
              15 * Graph.InducedPathWindowLedger.packingNumber ctx.G.object +
                Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
          simpa [ctx] using node29.totalSurplusSupply
        have capBound :=
          Graph.PositiveDeficiencyWedge.Profile.three_mul_card_le_wedgeCount_add_twice_cap
            (profile := p13RemainderCurvatureProfile ctx) totalSupply
        change 3 * (p13RemainderVertices ctx).card ≤
            (p13RemainderCurvatureProfile ctx).wedgeCount +
              2 * (15 * Graph.InducedPathWindowLedger.packingNumber ctx.G.object +
                Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) at capBound
        omega
      have rateTransport : ∀ (rate error : ℝ),
          ((p13RemainderCurvatureProfile ctx).positiveDeficiency : ℝ) ≤
              rate * (p13RemainderVertices ctx).card + error →
            (3 - 2 * rate) * (p13RemainderVertices ctx).card ≤
              (p13RemainderCurvatureProfile ctx).wedgeCount + 2 * error := by
        intro rate error deficiency
        exact (p13RemainderCurvatureProfile ctx).wedgeRate_of_deficiencyRate
          rate error deficiency
      exact {
        componentWedgeFloor := by
          intro component
          exact (show Graph.PositiveDeficiencyWedge.Profile ctx.G.object from
            { core := component }).wedgeFloor
        remainderWedgeFloor := p13Remainder_wedgeFloor ctx
        windowFiniteSupply := windowFiniteSupply
        windowFiniteError := by
          have remainderDensityScaled :
              node25RemainderRateNumerator *
                    Graph.InducedPathWindowLedger.packingNumber ctx.G.object * 1 ≤
                  node22SkeletonRateNumerator *
                    (p13RemainderVertices ctx).card * 1 + 0 := by
            simpa using remainderDensity
          simpa using
            (Core.DensityAsymptoticTransport.nat_scaled_wedge_with_error
              (baseline := 3)
              (remainderRate := node25RemainderRateNumerator)
              (wedgeRate := node30WindowWedgeRateNumerator)
              (incidence := 30)
              (skeleton := node22SkeletonRateNumerator)
              (packing :=
                Graph.InducedPathWindowLedger.packingNumber ctx.G.object)
              (remainder := (p13RemainderVertices ctx).card)
              (wedgeCount := (p13RemainderCurvatureProfile ctx).wedgeCount)
              (surplusFactor := 2)
              (surplus :=
                Graph.InducedPathWindowLedger.totalSurplus ctx.G.object)
              (scale := 1) (error := 0)
              (by norm_num [node30WindowWedgeRateNumerator,
                node25RemainderRateNumerator,
                node22SkeletonRateNumerator])
              remainderDensityScaled windowFiniteSupply)
        netDeficiencyFiniteCap := by
          have supplyScaled :
              node25RemainderRateNumerator *
                  (p13RemainderCurvatureProfile ctx).positiveDeficiency ≤
                node25RemainderRateNumerator *
                  (15 *
                      Graph.InducedPathWindowLedger.packingNumber
                        ctx.G.object +
                    Graph.InducedPathWindowLedger.totalSurplus
                      ctx.G.object) :=
            Nat.mul_le_mul_left node25RemainderRateNumerator
              node29.totalSurplusSupply
          have packingScaled :
              15 *
                  (node25RemainderRateNumerator *
                    Graph.InducedPathWindowLedger.packingNumber
                      ctx.G.object) ≤
                15 *
                  (node22SkeletonRateNumerator *
                    (p13RemainderVertices ctx).card) :=
            Nat.mul_le_mul_left 15 remainderDensity
          calc
            node25RemainderRateNumerator *
                (p13RemainderCurvatureProfile ctx).positiveDeficiency ≤
              node25RemainderRateNumerator *
                (15 *
                    Graph.InducedPathWindowLedger.packingNumber
                      ctx.G.object +
                  Graph.InducedPathWindowLedger.totalSurplus
                    ctx.G.object) := supplyScaled
            _ = 15 *
                  (node25RemainderRateNumerator *
                    Graph.InducedPathWindowLedger.packingNumber
                      ctx.G.object) +
                node25RemainderRateNumerator *
                  Graph.InducedPathWindowLedger.totalSurplus
                    ctx.G.object := by ring
            _ ≤ 15 *
                  (node22SkeletonRateNumerator *
                    (p13RemainderVertices ctx).card) +
                node25RemainderRateNumerator *
                  Graph.InducedPathWindowLedger.totalSurplus
                    ctx.G.object :=
              Nat.add_le_add_right packingScaled _
            _ = 15 * node22SkeletonRateNumerator *
                  (p13RemainderVertices ctx).card +
                node25RemainderRateNumerator *
                  Graph.InducedPathWindowLedger.totalSurplus
                    ctx.G.object := by ring
        rateTransport := rateTransport
        windowRateTransport := by
          intro error deficiency
          have transported :=
            rateTransport node30WindowDeficiencyRate error deficiency
          calc
            (254365026308 / 100000000000 : ℝ) *
                (p13RemainderVertices ctx).card ≤
              node30OmegaWindow *
                (p13RemainderVertices ctx).card := by
                  exact mul_le_mul_of_nonneg_right
                    node30OmegaWindow_gt_printed.le (by positivity)
            _ ≤ (p13RemainderCurvatureProfile ctx).wedgeCount +
                2 * error := by
                  simpa [node30OmegaWindow] using transported
        highEntropyTransport := by
          intro error deficiency
          rw [p13Node30OmegaHighEntropy_eq]
          exact (p13RemainderCurvatureProfile ctx).wedgeRate_of_deficiencyRate
            p13Node30HighEntropyDeficiencyRate error deficiency
        localWork := (p13RemainderCurvatureProfile ctx).checks_le_square
      }

noncomputable def runInitialThroughNode30 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode29 residual).mapYesStage
    node30P13WedgeLower

def node30LocalChecks : Nat := 0
theorem node30LocalChecks_eq_zero : node30LocalChecks = 0 := rfl

#print axioms node30P13WedgeLower
#print axioms runInitialThroughNode30

end Erdos64EG.Internal
