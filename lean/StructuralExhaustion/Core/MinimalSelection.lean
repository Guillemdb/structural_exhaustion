import Mathlib.Data.Nat.Find
import StructuralExhaustion.Core.Context
import StructuralExhaustion.Core.ResidualRefinement

namespace StructuralExhaustion.Core

universe uAmbient uBranch

namespace AvoidingContext

/-!
Rank minimization is a proof-level use of the well-ordering of `Nat`.  It does
not enumerate ambient objects.  The caller supplies only the ordinary branch
state initializer required for the selected ambient object.
-/

/-- Every baseline target-avoiding branch has a rank-minimal baseline
target-avoiding representative when branch states can be initialized. -/
theorem exists_minimalCounterexample
    {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (stateOf : (G : P.Ambient) → P.BranchState G)
    (ctx : AvoidingContext P Target) :
    ∃ minimal : MinimalCounterexampleContext P Target,
      P.rank minimal.G ≤ P.rank ctx.G := by
  classical
  let ExistsAtRank : Nat → Prop := fun rank =>
    ∃ (G : P.Ambient) (baseline : P.Baseline G),
      ¬ Target G ∧ P.rank G = rank
  have existsWitness : ∃ rank, ExistsAtRank rank :=
    ⟨P.rank ctx.G, ctx.G, ctx.baseline, ctx.avoids, rfl⟩
  obtain ⟨G, baseline, avoids, rankEq⟩ := Nat.find_spec existsWitness
  let branch : BranchContext P := ⟨G, baseline, stateOf G⟩
  let avoiding : AvoidingContext P Target :=
    AvoidingContext.ofBranch branch avoids
  have minimality : MinimalityKernel P Target branch := by
    intro H smaller baselineH
    by_contra avoidsH
    have atRank : ExistsAtRank (P.rank H) :=
      ⟨H, baselineH, avoidsH, rfl⟩
    have leastLe := Nat.find_min' existsWitness atRank
    change P.rank H < P.rank G at smaller
    change Nat.find existsWitness ≤ P.rank H at leastLe
    rw [rankEq] at smaller
    exact Nat.not_lt_of_ge leastLe smaller
  refine ⟨MinimalCounterexampleContext.ofAvoiding avoiding minimality, ?_⟩
  change P.rank G ≤ P.rank ctx.G
  rw [rankEq]
  exact Nat.find_min' existsWitness
    ⟨ctx.G, ctx.baseline, ctx.avoids, rfl⟩

end AvoidingContext

/-! ## Accumulated-ledger minimal selection

Minimal-counterexample selection is a proof-producing successor, not a change
of residual carrier.  The selected context is therefore stored as the one new
stage payload while the framework keeps the complete incoming ledger.
-/

/-- The thin output of one rank-minimal counterexample selection.  The bound
is indexed by the stable residual rather than by a copied predecessor. -/
structure MinimalCounterexampleSelection
    (P : Problem.{uAmbient, uBranch}) (Target : P.Ambient → Prop)
    (rankBound : Nat) where
  context : MinimalCounterexampleContext P Target
  rank_le : P.rank context.G ≤ rankBound

namespace ResidualRefinement.State.StageNode

universe uResidual uInput

/-- Select a minimal counterexample from an exact target-avoiding stage already
present in the accumulated ledger.  Applications provide only the projection
from their branch-local input to the generic avoiding context and the equality
identifying its rank with the stable residual's declared bound. -/
noncomputable def selectMinimalCounterexample
    {P : Problem.{uAmbient, uBranch}} {Target : P.Ambient → Prop}
    {Residual : Type uResidual} {facts : List (Residual → Prop)}
    {Input : Residual → Sort uInput}
    (query : ResidualRefinement.State.LedgerQuery (facts := facts) Input)
    (avoiding : ∀ residual, Input residual → AvoidingContext P Target)
    (rankBound : Residual → Nat)
    (rank_eq : ∀ residual input,
      P.rank (avoiding residual input).G = rankBound residual)
    (stateOf : (G : P.Ambient) → P.BranchState G) :
    ResidualRefinement.State.StageNode (facts := facts)
      (fun residual => MinimalCounterexampleSelection P Target (rankBound residual)) :=
  ResidualRefinement.State.StageNode.derive query fun state input => by
    let witness :=
      (avoiding state.residual input).exists_minimalCounterexample stateOf
    let context := Classical.choose witness
    have rankLe := Classical.choose_spec witness
    exact ⟨context, rankLe.trans_eq (rank_eq state.residual input)⟩

end ResidualRefinement.State.StageNode

end StructuralExhaustion.Core
