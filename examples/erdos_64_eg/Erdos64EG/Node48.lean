import Erdos64EG.Node47

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [48]: forced curvature cost

The finite inequalities below are transported from the exact node-[30]
certificate retained proof-relevantly inside node [31], together with node
[47]'s full-rank proof.  Core owns that provenance; node [48] accepts no
certificate or checkpoint input.
-/

noncomputable def node48CurvatureEntropyCost : ℝ :=
  Real.logb 2 ((543958 : ℝ) / 111286)

noncomputable def node48WindowCurvatureDensity : ℝ :=
  (node30WindowWedgeRateNumerator : ℝ) /
    node25RemainderRateNumerator

noncomputable def node48HighEntropyCurvatureDensity : ℝ :=
  (253825743018 : ℝ) / node25RemainderRateNumerator

noncomputable def node48WindowForcedCost : ℝ :=
  node48CurvatureEntropyCost * node48WindowCurvatureDensity

noncomputable def node48HighEntropyForcedCost : ℝ :=
  node48CurvatureEntropyCost * node48HighEntropyCurvatureDensity

noncomputable def node48CostError {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual) : ℝ :=
  2 * node48CurvatureEntropyCost *
    Graph.InducedPathWindowLedger.totalSurplus
      (Node21Context node18).G.object

/-- The entropy conversion used at node [48] is monotone.  This is a local
scalar fact, independent of the graph and of the active diagram leaf. -/
theorem node48CurvatureEntropyCost_nonneg :
    0 ≤ node48CurvatureEntropyCost := by
  apply Real.logb_nonneg (by norm_num)
  norm_num [node48CurvatureEntropyCost]

private theorem node48RemainderRatePositive :
    (0 : ℝ) < node25RemainderRateNumerator := by
  norm_num [node25RemainderRateNumerator]

/-- Every node-[48] cardinality is taken from the literal remainder carried by
node [31].  Its equality certificate identifies that carrier with the
canonical packing complement used by the earlier arithmetic profiles. -/
theorem node48_remainderCard_eq {V : Type u}
    {residual : InitialResidual V} {node18 : Node18Stage residual}
    {bounded : Node19Low residual node18}
    {node21 : Node21Output node18 bounded}
    {low : Node22Low residual node18 bounded node21}
    (node31 : Node31Output node18 bounded node21 low) :
    (Node25Remainder node18).input.vertices.card =
      (p13RemainderVertices (Node21Context node18)).card := by
  exact Graph.FiniteObject.induceFinset_vertexCount
    (Node21Context node18).G.object
    (p13RemainderVertices (Node21Context node18))

/-- Convert the finite window accounting into the paper's entropy-cost
units.  The input is precisely the finite inequality proved by the preceding
local accounting; no diagram state or graph family is inspected here. -/
private theorem node48ForcedCost_of_finiteCost {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual)
    (finiteCost :
      node30WindowWedgeRateNumerator *
          (p13RemainderVertices (Node21Context node18)).card ≤
        node25RemainderRateNumerator *
            p13CurvatureTargetRank (Node21Context node18) +
          2 * node25RemainderRateNumerator *
            Graph.InducedPathWindowLedger.totalSurplus
              (Node21Context node18).G.object) :
    node48WindowForcedCost *
        (p13RemainderVertices (Node21Context node18)).card ≤
      node48CurvatureEntropyCost *
          p13CurvatureTargetRank (Node21Context node18) +
        node48CostError node18 := by
  have finiteCostReal :
      (node30WindowWedgeRateNumerator : ℝ) *
          (p13RemainderVertices (Node21Context node18)).card ≤
        (node25RemainderRateNumerator : ℝ) *
            p13CurvatureTargetRank (Node21Context node18) +
          2 * (node25RemainderRateNumerator : ℝ) *
            Graph.InducedPathWindowLedger.totalSurplus
              (Node21Context node18).G.object := by
    exact_mod_cast finiteCost
  have normalized :
      node48WindowCurvatureDensity *
          (p13RemainderVertices (Node21Context node18)).card ≤
        p13CurvatureTargetRank (Node21Context node18) +
          2 * Graph.InducedPathWindowLedger.totalSurplus
            (Node21Context node18).G.object := by
    rw [node48WindowCurvatureDensity]
    calc
      (node30WindowWedgeRateNumerator : ℝ) /
            node25RemainderRateNumerator *
          (p13RemainderVertices (Node21Context node18)).card =
        ((node30WindowWedgeRateNumerator : ℝ) *
          (p13RemainderVertices (Node21Context node18)).card) /
            node25RemainderRateNumerator := by ring
      _ ≤ ((node25RemainderRateNumerator : ℝ) *
            p13CurvatureTargetRank (Node21Context node18) +
          2 * (node25RemainderRateNumerator : ℝ) *
            Graph.InducedPathWindowLedger.totalSurplus
              (Node21Context node18).G.object) /
            node25RemainderRateNumerator :=
        div_le_div_of_nonneg_right finiteCostReal node48RemainderRatePositive.le
      _ = p13CurvatureTargetRank (Node21Context node18) +
          2 * Graph.InducedPathWindowLedger.totalSurplus
            (Node21Context node18).G.object := by
        field_simp [ne_of_gt node48RemainderRatePositive]
  have scaled := mul_le_mul_of_nonneg_left normalized
    node48CurvatureEntropyCost_nonneg
  simpa [node48WindowForcedCost, node48CostError, mul_add, mul_assoc,
    mul_left_comm, mul_comm] using scaled

/-- The same scalar transport on node [48]'s sharper high-entropy edge. -/
private theorem node48HighEntropyForcedCost_of_finiteCost {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual)
    (finiteCost :
      253825743018 *
          (p13RemainderVertices (Node21Context node18)).card ≤
        node25RemainderRateNumerator *
            p13CurvatureTargetRank (Node21Context node18) +
          2 * node25RemainderRateNumerator *
            Graph.InducedPathWindowLedger.totalSurplus
              (Node21Context node18).G.object) :
    node48HighEntropyForcedCost *
        (p13RemainderVertices (Node21Context node18)).card ≤
      node48CurvatureEntropyCost *
          p13CurvatureTargetRank (Node21Context node18) +
        node48CostError node18 := by
  have finiteCostReal :
      (253825743018 : ℝ) *
          (p13RemainderVertices (Node21Context node18)).card ≤
        (node25RemainderRateNumerator : ℝ) *
            p13CurvatureTargetRank (Node21Context node18) +
          2 * (node25RemainderRateNumerator : ℝ) *
            Graph.InducedPathWindowLedger.totalSurplus
              (Node21Context node18).G.object := by
    exact_mod_cast finiteCost
  have normalized :
      node48HighEntropyCurvatureDensity *
          (p13RemainderVertices (Node21Context node18)).card ≤
        p13CurvatureTargetRank (Node21Context node18) +
          2 * Graph.InducedPathWindowLedger.totalSurplus
            (Node21Context node18).G.object := by
    rw [node48HighEntropyCurvatureDensity]
    calc
      (253825743018 : ℝ) / node25RemainderRateNumerator *
          (p13RemainderVertices (Node21Context node18)).card =
        ((253825743018 : ℝ) *
          (p13RemainderVertices (Node21Context node18)).card) /
            node25RemainderRateNumerator := by ring
      _ ≤ ((node25RemainderRateNumerator : ℝ) *
            p13CurvatureTargetRank (Node21Context node18) +
          2 * (node25RemainderRateNumerator : ℝ) *
            Graph.InducedPathWindowLedger.totalSurplus
              (Node21Context node18).G.object) /
            node25RemainderRateNumerator :=
        div_le_div_of_nonneg_right finiteCostReal node48RemainderRatePositive.le
      _ = p13CurvatureTargetRank (Node21Context node18) +
          2 * Graph.InducedPathWindowLedger.totalSurplus
            (Node21Context node18).G.object := by
        field_simp [ne_of_gt node48RemainderRatePositive]
  have scaled := mul_le_mul_of_nonneg_left normalized
    node48CurvatureEntropyCost_nonneg
  simpa [node48HighEntropyForcedCost, node48CostError, mul_add, mul_assoc,
    mul_left_comm, mul_comm] using scaled

/-- Only node [48]'s new finite and cost-unit conclusions. -/
structure Node48Output {V : Type u} {residual : InitialResidual V}
    (node18 : Node18Stage residual)
    (_bounded : Node19Low residual node18)
    (_node21 : Node21Output node18 _bounded)
    (_low : Node22Low residual node18 _bounded _node21)
    (_node31 : Node31Output node18 _bounded _node21 _low)
    (_fullRank : Node32FullRank node18) : Type (u + 1) where
  finiteCost :
    node30WindowWedgeRateNumerator *
        (Node25Remainder node18).input.vertices.card ≤
      node25RemainderRateNumerator *
          p13CurvatureTargetRank (Node21Context node18) +
        2 * node25RemainderRateNumerator *
          Graph.InducedPathWindowLedger.totalSurplus
            (Node21Context node18).G.object
  highEntropyFiniteCost : Node24HighEntropyJointBudget node18 →
    253825743018 *
        (Node25Remainder node18).input.vertices.card ≤
      node25RemainderRateNumerator *
          p13CurvatureTargetRank (Node21Context node18) +
        2 * node25RemainderRateNumerator *
          Graph.InducedPathWindowLedger.totalSurplus
            (Node21Context node18).G.object
  forcedCost :
    node48WindowForcedCost *
        (Node25Remainder node18).input.vertices.card ≤
      node48CurvatureEntropyCost *
          p13CurvatureTargetRank (Node21Context node18) +
        node48CostError node18
  highEntropyForcedCost : Node24HighEntropyJointBudget node18 →
    node48HighEntropyForcedCost *
        (Node25Remainder node18).input.vertices.card ≤
      node48CurvatureEntropyCost *
          p13CurvatureTargetRank (Node21Context node18) +
        node48CostError node18
  localWork : Nat := 0
  localWorkZero : localWork = 0

abbrev Node48Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuation
    (@Node32Bypass V) (@Node32Active V)
    (fun _ data => Node32RankDrop data.previous)
    (fun _ data => Node32FullRank data.previous)
    (fun _ data fullRank => Node48Output data.previous data.outerProof
      data.outerOutput data.innerProof data.current fullRank) residual

/-- Install only the exact old mathematical output on the literal node-[47]
leaf; Core owns the continuation and every bypass. -/
noncomputable def node48P13ForcedCurvatureCost {V : Type u}
    {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node47Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node48Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchNoContinuation
    (Output := fun _ data fullRank => Node34Output data.previous data.outerProof
      data.outerOutput data.innerProof data.current fullRank)
    fun residual data fullRank node47 =>
      let node18 := data.previous
      let bounded := data.outerProof
      let node21 := data.outerOutput
      let low := data.innerProof
      let node31 := data.current
      let ctx := Node21Context node18
      let node30 := node31.node30
      have remainderCardExact := node48_remainderCard_eq node31
      have wedge_le_rank :
          (p13RemainderCurvatureProfile ctx).wedgeCount ≤
            p13CurvatureTargetRank ctx := by
        rw [← node31.coordinateCount]
        exact fullRank.symm.le
      have finiteCost :
          node30WindowWedgeRateNumerator *
              (p13RemainderVertices ctx).card ≤
            node25RemainderRateNumerator * p13CurvatureTargetRank ctx +
              2 * node25RemainderRateNumerator *
                Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
        exact le_trans node30.windowFiniteError
          (Nat.add_le_add_right
            (Nat.mul_le_mul_left node25RemainderRateNumerator wedge_le_rank) _)
      have highEntropyFiniteCost : Node24HighEntropyJointBudget node18 →
          253825743018 * (p13RemainderVertices ctx).card ≤
            node25RemainderRateNumerator * p13CurvatureTargetRank ctx +
              2 * node25RemainderRateNumerator *
                Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
        intro high
        have cap := node24HighEntropyTransformer (residual := residual)
          node18 high
        have partition := p13Remainder_partition ctx
        have supply := node30.windowFiniteSupply
        have packing_eq : node22PackingCount node18 =
            Graph.InducedPathWindowLedger.packingNumber ctx.G.object := by
          unfold node22PackingCount node17PackingNumber node17Windows
          rw [Graph.InducedPathWindowLedger.packingNumber_eq_inducedPathPacking]
          rfl
        unfold Node24HighEntropyCap at cap
        rw [packing_eq] at cap
        rw [p13,
          ← Graph.InducedPathWindowLedger.packingNumber_eq_inducedPathPacking]
          at partition
        have remainderDensity :
            node25RemainderRateNumerator *
                  Graph.InducedPathWindowLedger.packingNumber ctx.G.object * 1 ≤
                1400000000 * (p13RemainderVertices ctx).card * 1 + 0 := by
          exact Core.DensityAsymptoticTransport.nat_partition_density_with_error
            (rate := 116808581006)
            (remainderRate := node25RemainderRateNumerator)
            (width := 13)
            (skeleton := 1400000000)
            (mass := Graph.InducedPathWindowLedger.packingNumber ctx.G.object)
            (remainder := (p13RemainderVertices ctx).card)
            (order := ctx.G.object.input.vertices.card)
            (scale := 1) (error := 0)
            (by norm_num [node25RemainderRateNumerator])
            (by simpa [ctx, node18] using partition)
            (by simpa [ctx, node18] using cap)
        have wedgeSupply :
            3 * (p13RemainderVertices ctx).card ≤
              (p13RemainderCurvatureProfile ctx).wedgeCount +
                30 * Graph.InducedPathWindowLedger.packingNumber ctx.G.object +
                2 * Graph.InducedPathWindowLedger.totalSurplus
                  ctx.G.object := by
          simpa [ctx, node18, node31, node30] using supply
        have highWedge :
            253825743018 * (p13RemainderVertices ctx).card ≤
              node25RemainderRateNumerator *
                  (p13RemainderCurvatureProfile ctx).wedgeCount +
                2 * node25RemainderRateNumerator *
                  Graph.InducedPathWindowLedger.totalSurplus
                    ctx.G.object := by
          simpa using
            (Core.DensityAsymptoticTransport.nat_scaled_wedge_with_error
              (baseline := 3)
              (remainderRate := node25RemainderRateNumerator)
              (wedgeRate := 253825743018)
              (incidence := 30)
              (skeleton := 1400000000)
              (packing :=
                Graph.InducedPathWindowLedger.packingNumber ctx.G.object)
              (remainder := (p13RemainderVertices ctx).card)
              (wedgeCount := (p13RemainderCurvatureProfile ctx).wedgeCount)
              (surplusFactor := 2)
              (surplus :=
                Graph.InducedPathWindowLedger.totalSurplus ctx.G.object)
              (scale := 1) (error := 0)
              (by norm_num [node25RemainderRateNumerator])
              remainderDensity wedgeSupply)
        exact le_trans highWedge
          (Nat.add_le_add_right
            (Nat.mul_le_mul_left node25RemainderRateNumerator wedge_le_rank) _)
      {
        finiteCost := by
          rw [remainderCardExact]
          exact finiteCost
        highEntropyFiniteCost := fun high => by
          rw [remainderCardExact]
          exact highEntropyFiniteCost high
        forcedCost := by
          rw [remainderCardExact]
          exact node48ForcedCost_of_finiteCost node18 finiteCost
        highEntropyForcedCost := fun high =>
          by
            rw [remainderCardExact]
            exact node48HighEntropyForcedCost_of_finiteCost node18
              (highEntropyFiniteCost high)
        localWork := 0
        localWorkZero := rfl
      }

noncomputable def runInitialThroughNode48 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode47 residual).mapYesStage
    node48P13ForcedCurvatureCost

def node48LocalChecks : Nat := 0

theorem node48LocalChecks_eq_zero : node48LocalChecks = 0 := rfl

#print axioms node48P13ForcedCurvatureCost
#print axioms runInitialThroughNode48

end Erdos64EG.Internal
