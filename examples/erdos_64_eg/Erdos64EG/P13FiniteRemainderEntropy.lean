import Erdos64EG.P13ForcedCurvatureCost
import StructuralExhaustion.Core.FiniteStateEntropyBookkeeping

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Node [49]: finite remainder-state entropy bookkeeping

The repaired manuscript node measures the exact local state family already
carried by node `[48]`'s realized conditional-fibre branch.  It does not
enumerate all labelled graphs on the remainder, subsets, contexts, or Boolean
assignments.  Lean exposes the exact state count, the manuscript's literal
real-valued normalization, and its executable integer floor logarithm.
-/

/-- Core-owned bookkeeping instantiated with node `[48]`'s exact supplied
state schedule and the literal remainder cardinality. -/
noncomputable def p13RemainderStateEntropyProfile
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    (realized : P13CurvatureProductCostRealization ctx node21 node24) :
    Core.FiniteStateEntropyBookkeeping.Profile where
  State := realized.State
  states := realized.states
  supportSize := (p13RemainderVertices ctx).card

/-- Exact proof-carried state count replacing the forbidden ambient
all-graphs enumeration. -/
noncomputable def p13RemainderStateCount
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    (realized : P13CurvatureProductCostRealization ctx node21 node24) : Nat :=
  (p13RemainderStateEntropyProfile realized).stateCount

/-- Executable numerator `floor (log₂ |S_R|)`. -/
noncomputable def p13RemainderEntropyBits
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    (realized : P13CurvatureProductCostRealization ctx node21 node24) : Nat :=
  (p13RemainderStateEntropyProfile realized).bitCount

/-- Literal real-valued manuscript normalization
`η(R) = log₂ |S_R| / |R|`. -/
noncomputable def p13RemainderEntropy
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    (realized : P13CurvatureProductCostRealization ctx node21 node24) : ℝ :=
  (p13RemainderStateEntropyProfile realized).normalizedEntropy

/-- Node `[49]`'s single output responsibility.  Positivity is inherited from
the nonempty terminal conditional fibre, while the upper bound is inherited
from the literal labelled-edge-set skeleton encoding at node `[48]`. -/
structure VerifiedP13Node49FiniteEntropy
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24DensityHandoff ctx node21)
    (realized : P13CurvatureProductCostRealization ctx node21 node24) :
    Type (u + 1) where
  previous : P13CurvatureProductCostRealization ctx node21 node24
  exactPrevious : previous = realized
  stateCountExact : p13RemainderStateCount realized = realized.states.values.length
  bitCountExact : p13RemainderEntropyBits realized =
    Nat.log2 (p13RemainderStateCount realized)
  bitCountFloorRealLog : p13RemainderEntropyBits realized =
    ⌊Real.logb 2 (p13RemainderStateCount realized)⌋₊
  normalizedEntropyExact : p13RemainderEntropy realized =
    Real.logb 2 (p13RemainderStateCount realized) /
      (p13RemainderVertices ctx).card
  countPos : 0 < p13RemainderStateCount realized
  countLeSkeleton : p13RemainderStateCount realized ≤
    baselineSpineStateCount ctx
  semanticChecks :
    (p13RemainderStateEntropyProfile realized).semanticChecks = 0
  arithmeticWork :
    (p13RemainderStateEntropyProfile realized).arithmeticWork ≤
      2 * p13RemainderStateCount realized + 1

/-- Construct node `[49]` without scanning any new family. -/
noncomputable def verifiedP13Node49FiniteEntropy
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24DensityHandoff ctx node21}
    (realized : P13CurvatureProductCostRealization ctx node21 node24) :
    VerifiedP13Node49FiniteEntropy ctx node21 node24 realized where
  previous := realized
  exactPrevious := rfl
  stateCountExact := (p13RemainderStateEntropyProfile realized).stateCount_eq_values_length
  bitCountExact := (p13RemainderStateEntropyProfile realized).bitCount_eq_log2_stateCount
  bitCountFloorRealLog :=
    (p13RemainderStateEntropyProfile realized).bitCount_eq_natFloor_logb
  normalizedEntropyExact :=
    (p13RemainderStateEntropyProfile realized).normalizedEntropy_eq
  countPos := by
    have terminalLeStart : realized.ledger.finalStates.length ≤
        realized.states.values.length :=
      realized.ledger.finalStates_sublist.length_le
    exact realized.finalNonempty.trans_le terminalLeStart
  countLeSkeleton := realized.states_length_le_baseline
  semanticChecks :=
    (p13RemainderStateEntropyProfile realized).semanticChecks_eq_zero
  arithmeticWork :=
    (p13RemainderStateEntropyProfile realized).arithmeticWork_le_two_mul_stateCount_add_one

end Erdos64EG.Internal
