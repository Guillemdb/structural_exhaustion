namespace StructuralExhaustion.Core

universe uAmbient uBranch

/-!
The problem-wide vocabulary shared by every automation-first closure tactic.

Tactics are parameterized by this object instead of embedding one another's
framework records.  Consequently the ambient object, baseline predicate,
rank, and branch-state family agree definitionally across every registered
route.
-/

/-- Mathematical data shared by every tactic in one structural-exhaustion
proof instance. -/
structure Problem where
  Ambient : Type uAmbient
  Baseline : Ambient → Prop
  rank : Ambient → Nat
  BranchState : Ambient → Type uBranch

end StructuralExhaustion.Core
