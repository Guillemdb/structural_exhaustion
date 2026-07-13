import Mathlib.Data.Nat.Find
import StructuralExhaustion.Core.Context

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

end StructuralExhaustion.Core
