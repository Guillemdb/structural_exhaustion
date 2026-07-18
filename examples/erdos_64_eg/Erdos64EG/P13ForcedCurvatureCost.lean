import Erdos64EG.P13PartIWindowDensityTriage
import Erdos64EG.CT15BaselineSpineDemand
import Mathlib.Data.Set.PowersetCard
import StructuralExhaustion.Graph.ConditionalFibreProductCost

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

set_option maxRecDepth 100000

/-!
# Node [48]: exact finite forced-curvature accounting

The manuscript writes the wedge floor and its curvature cost with an
`o(|R|)` error.  On the actual bounded-surplus branch the corresponding
finite statement has the total degree surplus as its explicit error term.
This file proves that statement from the same node-[24] coverage residual and
node-[47] rank prefix.  It scans no new universe.

The numerical inequality below is deliberately kept separate from the claim
that rank independence realizes a simultaneous product of curvature states.
The latter is a stronger semantic requirement.  This file retains its exact
payload and consequences only as conditional support; it exposes no absence
outcome because the original diagram has only `[47] -> [48] -> [49]`.
-/

/-- Common denominator after eliminating the thirteen vertices occupied by
each selected `P₁₃` window from the exact density cap. -/
def p13WindowRemainderRateDenominator : Nat :=
  p13WindowDensityRateNumerator -
    13 * p13WindowDensitySkeletonNumerator

/-- Exact scaled window-only wedge-rate numerator. -/
def p13WindowWedgeRateNumerator : Nat :=
  3 * p13WindowRemainderRateDenominator -
    30 * p13WindowDensitySkeletonNumerator

/-- The constants are positive and have the literal values used by the
finite arithmetic proof. -/
theorem p13Window_forcedCost_constants :
    p13WindowRemainderRateDenominator = 98608581006 ∧
      p13WindowWedgeRateNumerator = 250825743018 := by
  norm_num [p13WindowRemainderRateDenominator,
    p13WindowWedgeRateNumerator, p13WindowDensityRateNumerator,
    p13WindowDensitySkeletonNumerator]

/-- Eliminate the occupied window vertices from node `[24]`'s exact density
cap. -/
theorem p13Window_densityCap_remainderForm
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node24 : VerifiedP13Node24DensityHandoff ctx node21) :
    p13WindowRemainderRateDenominator * p13 ctx ≤
      p13WindowDensitySkeletonNumerator *
        (p13RemainderVertices ctx).card := by
  have partition := (node24.globalRankPrefix).remainder.exactPartition
  have density := node24.packingDensityCap
  norm_num [p13WindowRemainderRateDenominator,
    p13WindowDensityRateNumerator,
    p13WindowDensitySkeletonNumerator] at density ⊢
  nlinarith

/-- Exact node-[30] wedge floor after the node-[24] packing cap is substituted.
The only error is twice the total surplus, in the same scaled integer units.
-/
theorem p13Window_scaledWedgeCost
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node24 : VerifiedP13Node24DensityHandoff ctx node21) :
    p13WindowWedgeRateNumerator * (p13RemainderVertices ctx).card ≤
      p13WindowRemainderRateDenominator *
          (p13RemainderCurvatureProfile ctx).wedgeCount +
        2 * p13WindowRemainderRateDenominator *
          Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
  let profile := p13RemainderCurvatureProfile ctx
  have density := p13Window_densityCap_remainderForm node24
  have deficiency :=
    p13Remainder_positiveDeficiency_le_fifteen_mul_packing_add_surplus ctx
  have wedge := profile.three_mul_card_le_wedgeCount_add_twice_deficiency
  have surplusPartition :=
    Graph.InducedPathWindowLedger.window_add_remainder_eq_totalSurplus ctx.G.object
  dsimp [profile] at wedge
  change 3 * (p13RemainderVertices ctx).card ≤
    (p13RemainderCurvatureProfile ctx).wedgeCount +
      2 * (p13RemainderCurvatureProfile ctx).positiveDeficiency at wedge
  norm_num [p13WindowWedgeRateNumerator,
    p13WindowRemainderRateDenominator,
    p13WindowDensityRateNumerator,
    p13WindowDensitySkeletonNumerator] at density ⊢
  have surplusLe :
      Graph.InducedPathWindowLedger.windowSurplus ctx.G.object ≤
        Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
    omega
  have errorCover :
      2 * 98608581006 *
          (p13RemainderCurvatureProfile ctx).positiveDeficiency ≤
        30 * 98608581006 * p13 ctx +
          2 * 98608581006 *
            Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
    calc
      2 * 98608581006 *
          (p13RemainderCurvatureProfile ctx).positiveDeficiency ≤
        2 * 98608581006 *
          (15 * p13 ctx +
            Graph.InducedPathWindowLedger.windowSurplus ctx.G.object) :=
        Nat.mul_le_mul_left _ deficiency
      _ = 30 * 98608581006 * p13 ctx +
          2 * 98608581006 *
            Graph.InducedPathWindowLedger.windowSurplus ctx.G.object := by ring
      _ ≤ 30 * 98608581006 * p13 ctx +
          2 * 98608581006 *
            Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
        exact Nat.add_le_add_left (Nat.mul_le_mul_left _ surplusLe) _
  have wedgeWithBudget :
      3 * 98608581006 * (p13RemainderVertices ctx).card ≤
        98608581006 *
            (p13RemainderCurvatureProfile ctx).wedgeCount +
          30 * 98608581006 * p13 ctx +
          2 * 98608581006 *
            Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
    calc
      3 * 98608581006 * (p13RemainderVertices ctx).card =
          98608581006 * (3 * (p13RemainderVertices ctx).card) := by ring
      _ ≤ 98608581006 *
          ((p13RemainderCurvatureProfile ctx).wedgeCount +
            2 * (p13RemainderCurvatureProfile ctx).positiveDeficiency) :=
        Nat.mul_le_mul_left _ wedge
      _ = 98608581006 *
            (p13RemainderCurvatureProfile ctx).wedgeCount +
          2 * 98608581006 *
            (p13RemainderCurvatureProfile ctx).positiveDeficiency := by ring
      _ ≤ 98608581006 *
            (p13RemainderCurvatureProfile ctx).wedgeCount +
          (30 * 98608581006 * p13 ctx +
            2 * 98608581006 *
              Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) :=
        Nat.add_le_add_left errorCover _
      _ = 98608581006 *
            (p13RemainderCurvatureProfile ctx).wedgeCount +
          30 * 98608581006 * p13 ctx +
          2 * 98608581006 *
            Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by ring
  have densityScaled :
      30 * 98608581006 * p13 ctx ≤
        30 * 1500000000 * (p13RemainderVertices ctx).card := by
    calc
      30 * 98608581006 * p13 ctx =
          30 * (98608581006 * p13 ctx) := by ring
      _ ≤ 30 * (1500000000 * (p13RemainderVertices ctx).card) :=
        Nat.mul_le_mul_left 30 density
      _ = 30 * 1500000000 * (p13RemainderVertices ctx).card := by ring
  apply (Nat.add_le_add_iff_right).mp
  calc
    250825743018 * (p13RemainderVertices ctx).card +
        30 * 1500000000 * (p13RemainderVertices ctx).card =
      3 * 98608581006 * (p13RemainderVertices ctx).card := by ring
    _ ≤ 98608581006 *
          (p13RemainderCurvatureProfile ctx).wedgeCount +
        30 * 98608581006 * p13 ctx +
        2 * 98608581006 *
          Graph.InducedPathWindowLedger.totalSurplus ctx.G.object :=
      wedgeWithBudget
    _ ≤ 98608581006 *
          (p13RemainderCurvatureProfile ctx).wedgeCount +
        30 * 1500000000 * (p13RemainderVertices ctx).card +
        2 * 98608581006 *
          Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_left densityScaled _) _
    _ = (98608581006 *
          (p13RemainderCurvatureProfile ctx).wedgeCount +
        197217162012 *
          Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) +
        30 * 1500000000 * (p13RemainderVertices ctx).card := by ring

/-- Exact sharper numerator on the separately proved high-entropy density
branch. -/
def p13HighEntropyWedgeRateNumerator : Nat := 253825743018

/-- The high-entropy cap has the same remainder denominator and a smaller
right-hand rate. -/
theorem p13HighEntropy_densityCap_remainderForm
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node24 : VerifiedP13Node24DensityHandoff ctx node21)
    (high : node24.highEntropy.conclusion) :
    98608581006 * p13 ctx ≤
      1400000000 * (p13RemainderVertices ctx).card := by
  have partition := node24.globalRankPrefix.remainder.exactPartition
  have highCap : P13HighEntropyFiniteCap ctx node24.coverage.windowCeiling := by
    rwa [node24.highEntropy.conclusionExact] at high
  have density : p13HighEntropyRateNumerator * p13 ctx ≤
      p13HighEntropySkeletonNumerator * ctx.G.object.input.vertices.card :=
    (Nat.mul_le_mul_left p13HighEntropyRateNumerator
      node24.coverage.packing_le).trans highCap
  norm_num [p13HighEntropyRateNumerator,
    p13HighEntropySkeletonNumerator] at density ⊢
  nlinarith

/-- Sharper node-[48] finite magnitude, conditional only on the actual
high-entropy cap and using the same local wedge ledger. -/
theorem p13HighEntropy_scaledWedgeCost
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node24 : VerifiedP13Node24DensityHandoff ctx node21)
    (high : node24.highEntropy.conclusion) :
    p13HighEntropyWedgeRateNumerator * (p13RemainderVertices ctx).card ≤
      p13WindowRemainderRateDenominator *
          (p13RemainderCurvatureProfile ctx).wedgeCount +
        2 * p13WindowRemainderRateDenominator *
          Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
  let profile := p13RemainderCurvatureProfile ctx
  have density := p13HighEntropy_densityCap_remainderForm node24 high
  have deficiency :=
    p13Remainder_positiveDeficiency_le_fifteen_mul_packing_add_surplus ctx
  have wedge := profile.three_mul_card_le_wedgeCount_add_twice_deficiency
  have surplusPartition :=
    Graph.InducedPathWindowLedger.window_add_remainder_eq_totalSurplus ctx.G.object
  dsimp [profile] at wedge
  change 3 * (p13RemainderVertices ctx).card ≤
    (p13RemainderCurvatureProfile ctx).wedgeCount +
      2 * (p13RemainderCurvatureProfile ctx).positiveDeficiency at wedge
  norm_num [p13HighEntropyWedgeRateNumerator,
    p13WindowRemainderRateDenominator,
    p13WindowDensityRateNumerator] at density ⊢
  have surplusLe :
      Graph.InducedPathWindowLedger.windowSurplus ctx.G.object ≤
        Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
    omega
  have errorCover :
      2 * 98608581006 *
          (p13RemainderCurvatureProfile ctx).positiveDeficiency ≤
        30 * 98608581006 * p13 ctx +
          2 * 98608581006 *
            Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
    calc
      2 * 98608581006 *
          (p13RemainderCurvatureProfile ctx).positiveDeficiency ≤
        2 * 98608581006 *
          (15 * p13 ctx +
            Graph.InducedPathWindowLedger.windowSurplus ctx.G.object) :=
        Nat.mul_le_mul_left _ deficiency
      _ = 30 * 98608581006 * p13 ctx +
          2 * 98608581006 *
            Graph.InducedPathWindowLedger.windowSurplus ctx.G.object := by ring
      _ ≤ 30 * 98608581006 * p13 ctx +
          2 * 98608581006 *
            Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
        exact Nat.add_le_add_left (Nat.mul_le_mul_left _ surplusLe) _
  have wedgeWithBudget :
      3 * 98608581006 * (p13RemainderVertices ctx).card ≤
        98608581006 *
            (p13RemainderCurvatureProfile ctx).wedgeCount +
          30 * 98608581006 * p13 ctx +
          2 * 98608581006 *
            Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
    calc
      3 * 98608581006 * (p13RemainderVertices ctx).card =
          98608581006 * (3 * (p13RemainderVertices ctx).card) := by ring
      _ ≤ 98608581006 *
          ((p13RemainderCurvatureProfile ctx).wedgeCount +
            2 * (p13RemainderCurvatureProfile ctx).positiveDeficiency) :=
        Nat.mul_le_mul_left _ wedge
      _ = 98608581006 *
            (p13RemainderCurvatureProfile ctx).wedgeCount +
          2 * 98608581006 *
            (p13RemainderCurvatureProfile ctx).positiveDeficiency := by ring
      _ ≤ 98608581006 *
            (p13RemainderCurvatureProfile ctx).wedgeCount +
          (30 * 98608581006 * p13 ctx +
            2 * 98608581006 *
              Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) :=
        Nat.add_le_add_left errorCover _
      _ = 98608581006 *
            (p13RemainderCurvatureProfile ctx).wedgeCount +
          30 * 98608581006 * p13 ctx +
          2 * 98608581006 *
            Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by ring
  have densityScaled :
      30 * 98608581006 * p13 ctx ≤
        30 * 1400000000 * (p13RemainderVertices ctx).card := by
    calc
      30 * 98608581006 * p13 ctx =
          30 * (98608581006 * p13 ctx) := by ring
      _ ≤ 30 * (1400000000 * (p13RemainderVertices ctx).card) :=
        Nat.mul_le_mul_left 30 density
      _ = 30 * 1400000000 * (p13RemainderVertices ctx).card := by ring
  apply (Nat.add_le_add_iff_right).mp
  calc
    253825743018 * (p13RemainderVertices ctx).card +
        30 * 1400000000 * (p13RemainderVertices ctx).card =
      3 * 98608581006 * (p13RemainderVertices ctx).card := by ring
    _ ≤ 98608581006 *
          (p13RemainderCurvatureProfile ctx).wedgeCount +
        30 * 98608581006 * p13 ctx +
        2 * 98608581006 *
          Graph.InducedPathWindowLedger.totalSurplus ctx.G.object :=
      wedgeWithBudget
    _ ≤ 98608581006 *
          (p13RemainderCurvatureProfile ctx).wedgeCount +
        30 * 1400000000 * (p13RemainderVertices ctx).card +
        2 * 98608581006 *
          Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_left densityScaled _) _
    _ = (98608581006 *
          (p13RemainderCurvatureProfile ctx).wedgeCount +
        197217162012 *
          Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) +
        30 * 1400000000 * (p13RemainderVertices ctx).card := by ring

/-- Node `[48]` output in rank coordinates.  Node `[47]` identifies the
complete CT15 coordinate count with the literal wedge count, so this is a
pure transport of the preceding theorem. -/
structure VerifiedP13Node48FiniteCost
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24DensityHandoff ctx node21) : Type u where
  previous : P13DensityConnectedGlobalRankPrefix ctx node21 node24.coverage
  exactPrevious : previous = node24.globalRankPrefix
  fullRank :
    (p13CurvatureResponseProfile ctx).ct15Profile.coordinates.card =
      (p13RemainderCurvatureProfile ctx).wedgeCount
  scaledCost :
    p13WindowWedgeRateNumerator * (p13RemainderVertices ctx).card ≤
      p13WindowRemainderRateDenominator *
          (p13CurvatureResponseProfile ctx).ct15Profile.coordinates.card +
        2 * p13WindowRemainderRateDenominator *
          Graph.InducedPathWindowLedger.totalSurplus ctx.G.object
  highEntropyScaledCost : node24.highEntropy.conclusion →
    p13HighEntropyWedgeRateNumerator * (p13RemainderVertices ctx).card ≤
      p13WindowRemainderRateDenominator *
          (p13CurvatureResponseProfile ctx).ct15Profile.coordinates.card +
        2 * p13WindowRemainderRateDenominator *
          Graph.InducedPathWindowLedger.totalSurplus ctx.G.object

/-- Construct the exact finite node-[48] arithmetic from its literal green
predecessors. -/
noncomputable def verifiedP13Node48FiniteCost
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node24 : VerifiedP13Node24DensityHandoff ctx node21) :
    VerifiedP13Node48FiniteCost ctx node21 node24 where
  previous := node24.globalRankPrefix
  exactPrevious := rfl
  fullRank := node24.globalRankPrefix_fullRankCount
  scaledCost := by
    rw [node24.globalRankPrefix_fullRankCount]
    exact p13Window_scaledWedgeCost node24
  highEntropyScaledCost := by
    intro high
    rw [node24.globalRankPrefix_fullRankCount]
    exact p13HighEntropy_scaledWedgeCost node24 high

/-- One literal undirected edge slot on the labelled ambient vertex set. -/
abbrev P13BaselineEdgeSlot
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Enumeration.DistinctPair ctx.G.Vertex

/-- The manuscript's actual labelled baseline-skeleton family: a skeleton is
a finite set of distinct undirected edge slots with exactly the authored
baseline edge count. -/
abbrev P13BaselineSkeleton
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Set.powersetCard (P13BaselineEdgeSlot ctx) (baselineSpineEdgeCount ctx)

/-- The literal edge-set skeleton family has exactly the binomial cardinality
used by the manuscript budget. -/
theorem p13BaselineSkeleton_natCard
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Nat.card (P13BaselineSkeleton ctx) = baselineSpineStateCount ctx := by
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  letI : Fintype ctx.G.Vertex :=
    @FinEnum.instFintype _ ctx.G.object.input.vertices
  let edgeSlots := Core.Enumeration.distinctPairs ctx.G.object.input.vertices
  letI : FinEnum (P13BaselineEdgeSlot ctx) := edgeSlots
  letI : Fintype (P13BaselineEdgeSlot ctx) :=
    @FinEnum.instFintype _ edgeSlots
  rw [Set.powersetCard.card, Nat.card_eq_fintype_card,
    ← FinEnum.card_eq_fintypeCard,
    Core.Enumeration.distinctPairs_card]
  rfl

structure P13CurvatureProductCostRealization
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24DensityHandoff ctx node21) : Type (u + 1) where
  previous : VerifiedP13Node48FiniteCost ctx node21 node24
  State : Type u
  states : Core.OrderedCollection State
  context : State →
    Graph.PackedBoundariedGluing.Context ctx.G.Vertex
  accepts : P13CurvatureCoordinate ctx → State → Bool
  responseSemantic : ∀ coordinate state,
    accepts coordinate state =
      (p13CurvatureResponseProfile ctx).responseSystem.response
        coordinate (context state)
  contextInjective : Function.Injective context
  contextSkeleton :
    Graph.PackedBoundariedGluing.Context ctx.G.Vertex →
      P13BaselineSkeleton ctx
  contextSkeletonInjectiveOnStates :
    Function.Injective (fun state ↦ contextSkeleton (context state))
  ledger :
    let profile : Graph.ConditionalFibreProductCost.Profile := {
      State := State
      Coordinate := P13CurvatureCoordinate ctx
      states := states
      coordinates := (p13CurvatureCoordinates ctx).toOrderedCollection
      accepts := accepts
      safe := 543958
      flat := 111286
      skeletonCount := baselineSpineStateCount ctx
    }
    Graph.ConditionalFibreProductCost.Profile.Ledger profile
      profile.states.values profile.coordinates.values
  finalNonempty :
    let profile : Graph.ConditionalFibreProductCost.Profile := {
      State := State
      Coordinate := P13CurvatureCoordinate ctx
      states := states
      coordinates := (p13CurvatureCoordinates ctx).toOrderedCollection
      accepts := accepts
      safe := 543958
      flat := 111286
      skeletonCount := baselineSpineStateCount ctx
    }
    0 < ledger.finalStates.length

namespace P13CurvatureProductCostRealization

/-- The supplied state list fits in the exact labelled-skeleton family because
its duplicate-free entries have an injective graph-owned skeleton code. -/
theorem states_length_le_baseline
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    (realized : P13CurvatureProductCostRealization ctx node21 node24) :
    realized.states.values.length ≤ baselineSpineStateCount ctx := by
  have codesNodup :
      (realized.states.values.map
        (fun state ↦ realized.contextSkeleton (realized.context state))).Nodup :=
    realized.states.nodup.map realized.contextSkeletonInjectiveOnStates
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  letI : Fintype ctx.G.Vertex :=
    @FinEnum.instFintype _ ctx.G.object.input.vertices
  letI : FinEnum (P13BaselineEdgeSlot ctx) :=
    Core.Enumeration.distinctPairs ctx.G.object.input.vertices
  letI : Fintype (P13BaselineEdgeSlot ctx) :=
    @FinEnum.instFintype _
      (Core.Enumeration.distinctPairs ctx.G.object.input.vertices)
  calc
    realized.states.values.length ≤
        Fintype.card (P13BaselineSkeleton ctx) := by
      simpa using codesNodup.length_le_card
    _ = Nat.card (P13BaselineSkeleton ctx) := by
      exact Fintype.card_eq_nat_card
    _ = baselineSpineStateCount ctx := p13BaselineSkeleton_natCard ctx

/-- Assemble the generic conditional-fibre certificate from the actual local
ledger and the derived labelled-skeleton capacity. -/
noncomputable def certificate
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    (realized : P13CurvatureProductCostRealization ctx node21 node24) :
    let profile : Graph.ConditionalFibreProductCost.Profile := {
      State := realized.State
      Coordinate := P13CurvatureCoordinate ctx
      states := realized.states
      coordinates := (p13CurvatureCoordinates ctx).toOrderedCollection
      accepts := realized.accepts
      safe := 543958
      flat := 111286
      skeletonCount := baselineSpineStateCount ctx
    }
    Graph.ConditionalFibreProductCost.Profile.Certificate profile := by
  dsimp
  exact {
    ledger := realized.ledger
    startCapacity := realized.states_length_le_baseline
    finalNonempty := realized.finalNonempty
  }

/-- The graph-owned local conditional-fibre ledger, rather than CT15
nonidentification alone, is what yields the exact multiplicative cost. -/
theorem safeFlatProductBound
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    (realized : P13CurvatureProductCostRealization ctx node21 node24) :
    543958 ^ (p13CurvatureResponseProfile ctx).ct15Profile.coordinates.card ≤
      111286 ^ (p13CurvatureResponseProfile ctx).ct15Profile.coordinates.card *
        baselineSpineStateCount ctx := by
  let profile : Graph.ConditionalFibreProductCost.Profile := {
    State := realized.State
    Coordinate := P13CurvatureCoordinate ctx
    states := realized.states
    coordinates := (p13CurvatureCoordinates ctx).toOrderedCollection
    accepts := realized.accepts
    safe := 543958
    flat := 111286
    skeletonCount := baselineSpineStateCount ctx
  }
  have product :=
    Graph.ConditionalFibreProductCost.Profile.Certificate.power_le_flat_mul_skeleton
      profile realized.certificate
  change 543958 ^ (p13CurvatureCoordinates ctx).card ≤
    111286 ^ (p13CurvatureCoordinates ctx).card *
      baselineSpineStateCount ctx
  simpa [profile, FinEnum.toOrderedCollection_length] using product

/-- The realized product ledger checks only its supplied local state list
against its supplied curvature-coordinate schedule. -/
theorem localChecks_le_state_mul_coordinate
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    (realized : P13CurvatureProductCostRealization ctx node21 node24) :
    let profile : Graph.ConditionalFibreProductCost.Profile := {
      State := realized.State
      Coordinate := P13CurvatureCoordinate ctx
      states := realized.states
      coordinates := (p13CurvatureCoordinates ctx).toOrderedCollection
      accepts := realized.accepts
      safe := 543958
      flat := 111286
      skeletonCount := baselineSpineStateCount ctx
    }
    profile.checks ≤
      profile.states.values.length * profile.coordinates.values.length := by
  dsimp
  exact Core.ConditionalFibreProductCost.Profile.checks_le_state_mul_coordinate _

end P13CurvatureProductCostRealization

end Erdos64EG.Internal
