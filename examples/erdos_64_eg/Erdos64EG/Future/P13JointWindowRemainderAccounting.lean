import Erdos64EG.Future.P13Nodes47To51Refinement
import Erdos64EG.Future.P13Node24DensityArithmetic
import StructuralExhaustion.Core.ResidualRefinement

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Node [52]: local window--remainder feasibility accounting

The original paper assigns this node one arithmetic responsibility on the
exact high edge of node `[50]`: add the already established window and
remainder bit contributions, compare them with the inherited near-cubic
skeleton budget, and retain the resulting high-entropy packing inequality.

There is no graph search, completion type, Cartesian-product schedule, or
ambient context universe at this node.  The accumulated refinement ledger
retains all predecessors.  The sole Erdős-specific proposition added here is
the exact finite, error-bearing form of the paper's feasibility inequality,
already named by node `[24]` for its downstream consumer.
-/

/-- The exact local proposition owned by manuscript node `[52]` on node
`[51]`'s high edge.  Its indices force the inequality to concern the same
residual and the literal high-entropy predecessor retained by the framework.
-/
abbrev P13Node52Feasibility
    (residual : P13Node24RefinementResidual.{u}) : Prop :=
  P13Node24HighEntropyDownstreamRequirement residual.ctx residual.node21

/-- Node `[52]` adds only its local feasibility fact.  Every predecessor is
retrieved from the one accumulated framework state rather than copied into an
application-owned handoff. -/
abbrev P13Node52RefinementOutput
    (residual : P13Node24RefinementResidual.{u})
    (node50 : P13Node50RefinementStage residual)
    (_high : P13Node50RefinementHigh residual node50)
    (node51 : P13Node51RefinementOutput residual node50 _high) :=
  PLift (P13Node52Feasibility residual)

/-- The paper's independent/dependent split at node `[52]`, indexed by the
literal node-`[51]` high-entropy value.  The independent constructor is the
node-`[52]` payload consumed by `[54]`; its sibling retains the failed local
accounting statement for the dependent regime. -/
inductive P13Node52AccountingRoute
    (residual : P13Node24RefinementResidual.{u}) : Type (u + 4)
  | independent
      (feasible : P13Node24HighEntropyDownstreamRequirement
        residual.ctx residual.node21)
  | dependent
      (failed : ¬P13Node24HighEntropyDownstreamRequirement
        residual.ctx residual.node21)

/-- Execute the existing local split without inspecting any graph family. -/
noncomputable def routeP13Node52Accounting
    (residual : P13Node24RefinementResidual.{u}) :
    P13Node52AccountingRoute residual := by
  by_cases feasible : P13Node24HighEntropyDownstreamRequirement
      residual.ctx residual.node21
  · exact .independent feasible
  · exact .dependent feasible

theorem routeP13Node52Accounting_exhaustive
    (residual : P13Node24RefinementResidual.{u}) :
    (∃ feasible, routeP13Node52Accounting residual =
        .independent feasible) ∨
      (∃ failed, routeP13Node52Accounting residual =
        .dependent failed) := by
  cases route : routeP13Node52Accounting residual with
  | independent feasible => exact Or.inl ⟨feasible, rfl⟩
  | dependent failed => exact Or.inr ⟨failed, rfl⟩

/-- Ledger-owned execution of the same split on the exact node-`[51]` edge. -/
abbrev P13Node52RoutingStage
    (residual : P13Node24RefinementResidual.{u}) :=
  Core.ResidualRefinement.State.DependentDecisionYesSuccessor
    P13Node50RefinementStage P13Node50RefinementHigh P13Node50RefinementLow
    P13Node51RefinementOutput
    (fun residual _node50 _high _node51 => P13Node52AccountingRoute residual)
    residual

noncomputable def p13Node52RoutingRefinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node51RefinementStage) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node52RoutingStage :=
  Core.ResidualRefinement.State.StageNode.continueDependentDecisionYesAgain
    fun residual _node50 _high _node51 => routeP13Node52Accounting residual

/-- Framework-owned continuation of exactly the node-`[51]` high edge.  The
node-`[50]` low edge remains available to node `[53]`. -/
abbrev P13Node52RefinementStage
    (residual : P13Node24RefinementResidual.{u}) :=
  Core.ResidualRefinement.State.DependentDecisionYesSuccessor
    P13Node50RefinementStage P13Node50RefinementHigh P13Node50RefinementLow
    P13Node51RefinementOutput P13Node52RefinementOutput residual

/-- Retrieve the earlier window, forced-curvature, and entropy facts from the
single accumulated ledger through their registered theorem projections. -/
noncomputable def p13Node52InheritedQuery {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node24Stage) facts]
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node48RefinementStage) facts]
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node49RefinementStage) facts] :=
  ((Core.ResidualRefinement.State.LedgerQuery.entailedStage
      (facts := facts) (Stage := P13Node24Stage)
      (property := P13Node24WindowDensityFact)).andEntailedStage
    (Stage := P13Node48RefinementStage)
    (property := P13Node48ForcedCurvatureFact)).andEntailedStage
      (Stage := P13Node49RefinementStage)
      (property := P13Node49EntropyIdentityFact)

/-- Attach node `[52]` by giving only its new local arithmetic argument.
Every earlier mathematical premise and the immediate node-[51] branch value
are retrieved by the framework from the same accumulated state. -/
noncomputable def p13Node52RefinementFromLocalAccounting {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node51RefinementStage) facts]
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node24Stage) facts]
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node48RefinementStage) facts]
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node49RefinementStage) facts]
    (account : ∀ residual,
      P13Node24WindowDensityFact residual →
      P13Node48ForcedCurvatureFact residual →
      P13Node49EntropyIdentityFact residual →
      (node50 : P13Node50RefinementStage residual) →
      (high : P13Node50RefinementHigh residual node50) →
      (node51 : P13Node51RefinementOutput residual node50 high) →
      P13Node52Feasibility residual) :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node52RefinementStage :=
  Core.ResidualRefinement.State.StageNode.continueDependentDecisionYesAgainDerived
      (p13Node52InheritedQuery (facts := facts))
      fun residual inherited node50 high node51 =>
        ⟨account residual inherited.fst.fst inherited.fst.snd inherited.snd
          node50 high node51⟩

/-! ## Node [54]: the finite entropy-cap terminal -/

/-- The strict high-density alternative excluded by node `[52]` is the exact
strict reverse of its finite feasibility inequality. This is the integral,
error-bearing form of `theta > Theta(n) + o(1)` used by the paper. -/
abbrev P13Node54HighTheta
    (residual : P13Node24RefinementResidual.{u}) : Prop :=
  p13HighEntropySkeletonNumerator *
          residual.ctx.G.object.input.vertices.card *
          Nat.log 2 residual.ctx.G.object.input.vertices.card *
          p13ExactHotCertificateScale +
        p13SequentialHotNormalizationError residual.ctx residual.node21 <
    p13HighEntropyRateNumerator * p13 residual.ctx *
      Nat.log 2 residual.ctx.G.object.input.vertices.card *
        p13ExactHotCertificateScale

/-- Node `[54]` closes precisely the strict high-density leaf. It neither
closes node `[50]`'s low branch nor imports any later net-charge conclusion. -/
structure VerifiedP13Node54EntropyCap
    (residual : P13Node24RefinementResidual.{u}) : Type where
  highThetaImpossible : ¬P13Node54HighTheta residual

/-- The exact local entropy-cap contradiction supplied by node `[52]`. -/
theorem p13Node54_highTheta_impossible
    {residual : P13Node24RefinementResidual.{u}}
    {node50 : P13Node50RefinementStage residual}
    {high : P13Node50RefinementHigh residual node50}
    {node51 : P13Node51RefinementOutput residual node50 high}
    (node52 : P13Node52RefinementOutput residual node50 high node51) :
    ¬P13Node54HighTheta residual :=
  not_lt_of_ge (PLift.down node52)

/-- Close node `[54]` directly on the independent constructor of the exact
node-`[52]` split.  The dependent constructor is not inspected. -/
theorem p13Node54_independentRoute_closes
    {residual : P13Node24RefinementResidual.{u}}
    {node50 : P13Node50RefinementStage residual}
    {high : P13Node50RefinementHigh residual node50}
    {node51 : P13Node51RefinementOutput residual node50 high}
    {feasible : P13Node24HighEntropyDownstreamRequirement
      residual.ctx residual.node21}
    (_selected : routeP13Node52Accounting residual =
      .independent feasible) :
    ¬P13Node54HighTheta residual :=
  p13Node54_highTheta_impossible
    (node50 := node50) (high := high) (node51 := node51)
    (node52 := (⟨feasible⟩ :
      P13Node52RefinementOutput residual node50 high node51))

abbrev P13Node54RefinementOutput
    (residual : P13Node24RefinementResidual.{u})
    (_node50 : P13Node50RefinementStage residual)
    (_high : P13Node50RefinementHigh residual _node50)
    (_node51 : P13Node51RefinementOutput residual _node50 _high) :=
  VerifiedP13Node54EntropyCap residual

/-- Framework-owned realization of the existing `[52] → [54]` edge. The
node-[52] stage remains in the accumulated ledger, and the node-[50] low edge
passes through unchanged. -/
abbrev P13Node54RefinementStage
    (residual : P13Node24RefinementResidual.{u}) :=
  Core.ResidualRefinement.State.DependentDecisionYesSuccessor
    P13Node50RefinementStage P13Node50RefinementHigh P13Node50RefinementLow
    P13Node51RefinementOutput P13Node54RefinementOutput residual

noncomputable def p13Node54Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node52RefinementStage) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node54RefinementStage :=
  Core.ResidualRefinement.State.StageNode.closeDependentDecisionYesSuccessor
    fun (residual : P13Node24RefinementResidual.{u})
        (node50 : P13Node50RefinementStage residual)
        (high : P13Node50RefinementHigh residual node50)
        (node51 : P13Node51RefinementOutput residual node50 high)
        (node52 : P13Node52RefinementOutput residual node50 high node51) =>
      ⟨p13Node54_highTheta_impossible node52⟩

/-- The entropy-cap terminal is symbolic linear arithmetic and performs no
semantic scan. -/
def p13Node54LocalChecks : Nat := 0

@[simp] theorem p13Node54LocalChecks_eq_zero : p13Node54LocalChecks = 0 := rfl

/-- Node `[52]` is pure symbolic accounting and performs no local semantic
inspection. -/
def p13Node52LocalChecks : Nat := 0

@[simp] theorem p13Node52LocalChecks_eq_zero : p13Node52LocalChecks = 0 := rfl

end Erdos64EG.Internal
