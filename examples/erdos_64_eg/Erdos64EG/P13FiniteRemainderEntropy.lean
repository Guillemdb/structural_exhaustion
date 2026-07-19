import Erdos64EG.P13ForcedCurvatureCost
import StructuralExhaustion.Core.ExactHandoff
import StructuralExhaustion.Core.FiniteStateEntropyBookkeeping
import StructuralExhaustion.Graph.ConstrainedLabelledGraphFamily
import StructuralExhaustion.Graph.InducedPath

namespace Erdos64EG.Internal

open StructuralExhaustion
open scoped BigOperators

universe u

noncomputable instance p13RemainderVertexFintype
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Fintype (P13RemainderVertex ctx) :=
  @FinEnum.instFintype _ (p13RemainderVertexEnumeration ctx)

noncomputable instance p13RemainderVertexDecidableEq
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    DecidableEq (P13RemainderVertex ctx) :=
  Classical.decEq _

/-! ## The literal manuscript family `𝒢(R)` -/

/-- Vertices that belong to the paper's subcubic atom part, read from the
fixed node-[48] remainder rather than supplied by a caller. -/
noncomputable def p13RemainderAtomPart
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (vertex : P13RemainderVertex ctx) : Prop := by
  letI : FinEnum (P13RemainderVertex ctx) := p13RemainderVertexEnumeration ctx
  letI : DecidableRel (p13Remainder ctx).graph.Adj :=
    (p13Remainder ctx).input.decideAdj
  exact (p13Remainder ctx).graph.degree vertex ≤ 3

/-- Positive deficiency of one labelled candidate graph on the fixed
remainder vertex set. -/
noncomputable def p13CandidatePositiveDeficiency
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (graph : SimpleGraph (P13RemainderVertex ctx)) : Nat := by
  classical
  letI : Fintype (P13RemainderVertex ctx) :=
    @FinEnum.instFintype _ (p13RemainderVertexEnumeration ctx)
  letI : DecidableRel graph.Adj := Classical.decRel _
  exact Finset.univ.sum fun vertex : P13RemainderVertex ctx =>
    3 - graph.degree vertex

/-- Degree surplus of one labelled candidate graph above the cubic baseline. -/
noncomputable def p13CandidateSurplus
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (graph : SimpleGraph (P13RemainderVertex ctx)) : Nat := by
  classical
  letI : Fintype (P13RemainderVertex ctx) :=
    @FinEnum.instFintype _ (p13RemainderVertexEnumeration ctx)
  letI : DecidableRel graph.Adj := Classical.decRel _
  exact Finset.univ.sum fun vertex : P13RemainderVertex ctx =>
    graph.degree vertex - 3

/-- The numerator of the candidate's positive net-deficiency density. -/
noncomputable def p13CandidateNetDeficiency
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (graph : SimpleGraph (P13RemainderVertex ctx)) : Nat :=
  p13CandidatePositiveDeficiency graph - p13CandidateSurplus graph

/-- The candidate has no nonempty internal three-core.  This pointwise
finite-set formulation is equivalent to repeatedly finding a vertex of
internal degree at most two and does not enumerate supports. -/
noncomputable def p13CandidateInternalThreeCoreFree
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (graph : SimpleGraph (P13RemainderVertex ctx)) : Prop := by
  classical
  letI : Fintype (P13RemainderVertex ctx) :=
    @FinEnum.instFintype _ (p13RemainderVertexEnumeration ctx)
  letI : DecidableRel graph.Adj := Classical.decRel _
  exact ∀ vertices : Finset (P13RemainderVertex ctx), vertices.Nonempty →
    ∃ vertex ∈ vertices,
      (graph.neighborFinset vertex ∩ vertices).card ≤ 2

/-- Exactly the four already imposed constraints listed in the original
definition of `𝒢(R)`. -/
noncomputable def p13RemainderGraphAdmissible
    (residual : P13Node24RefinementResidual.{u})
    (graph : SimpleGraph (P13RemainderVertex residual.ctx)) : Prop := by
  classical
  letI : Fintype (P13RemainderVertex residual.ctx) :=
    @FinEnum.instFintype _ (p13RemainderVertexEnumeration residual.ctx)
  letI : DecidableRel graph.Adj := Classical.decRel _
  exact
    (∀ vertex, p13RemainderAtomPart residual.ctx vertex → graph.degree vertex ≤ 3) ∧
    Graph.InducedPathFree graph 13 ∧
    p13CandidateInternalThreeCoreFree graph ∧
    p13CandidateNetDeficiency graph ≤
      ((p13RemainderCurvatureProfile residual.ctx).positiveDeficiency -
        Graph.InducedPathWindowLedger.remainderSurplus residual.ctx.G.object)

/-- Framework profile for the paper's literal constrained labelled-graph
family.  Its subtype is finite symbolically; no graph list is constructed. -/
noncomputable def p13RemainderGraphFamilyProfile
    (residual : P13Node24RefinementResidual.{u}) :
    Graph.ConstrainedLabelledGraphFamily.Profile
      (P13RemainderVertex residual.ctx) := by
  letI : Fintype (P13RemainderVertex residual.ctx) :=
    @FinEnum.instFintype _ (p13RemainderVertexEnumeration residual.ctx)
  letI : DecidableEq (P13RemainderVertex residual.ctx) := Classical.decEq _
  exact {
    admissible := p13RemainderGraphAdmissible residual
    supportSize := (p13RemainderVertices residual.ctx).card
  }

/-- The exact `|𝒢(R)|` of the original paper. -/
noncomputable def p13RemainderGraphFamilyCount
    (residual : P13Node24RefinementResidual.{u}) : Nat := by
  letI : Fintype (P13RemainderVertex residual.ctx) :=
    @FinEnum.instFintype _ (p13RemainderVertexEnumeration residual.ctx)
  letI : DecidableEq (P13RemainderVertex residual.ctx) := Classical.decEq _
  exact (p13RemainderGraphFamilyProfile residual).stateCount

/-- Node `[49]`'s literal per-vertex remainder entropy. -/
noncomputable def p13ManuscriptRemainderEntropy
    (residual : P13Node24RefinementResidual.{u}) : ℝ := by
  letI : Fintype (P13RemainderVertex residual.ctx) :=
    @FinEnum.instFintype _ (p13RemainderVertexEnumeration residual.ctx)
  letI : DecidableEq (P13RemainderVertex residual.ctx) := Classical.decEq _
  exact (p13RemainderGraphFamilyProfile residual).normalizedEntropy

/-- Exact node-[48] to node-[49] handoff for the paper-defined family. -/
structure VerifiedP13Node49ManuscriptEntropy
    (residual : P13Node24RefinementResidual.{u})
    (branch : P13Node34Stage residual)
    (node47 : VerifiedP13Node47FullRankResidual residual branch)
    (node48 : VerifiedP13Node48FrontierCost residual branch node47) : Type (u + 4)
    extends Core.ExactHandoff node48 where
  entropyExact : p13ManuscriptRemainderEntropy residual =
    Real.logb 2 (p13RemainderGraphFamilyCount residual) /
      (p13RemainderVertices residual.ctx).card
  semanticChecks : Nat := 0
  semanticChecksZero : semanticChecks = 0

noncomputable def VerifiedP13Node48FrontierCost.node49
    {residual : P13Node24RefinementResidual.{u}}
    {branch : P13Node34Stage residual}
    {node47 : VerifiedP13Node47FullRankResidual residual branch}
    (node48 : VerifiedP13Node48FrontierCost residual branch node47) :
    VerifiedP13Node49ManuscriptEntropy residual branch node47 node48 where
  previous := node48
  previousExact := rfl
  entropyExact := by
    simp [p13ManuscriptRemainderEntropy,
      p13RemainderGraphFamilyCount,
      p13RemainderGraphFamilyProfile,
      Graph.ConstrainedLabelledGraphFamily.Profile.normalizedEntropy_eq]
  semanticChecks := 0
  semanticChecksZero := rfl

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
    Type (u + 5) extends Core.ExactHandoff realized where
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
  previousExact := rfl
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
