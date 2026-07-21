import Hypostructure.Core.Prelude

/-!
# Problem kernel

The universal problem data contains only an ambient type, its baseline
predicate, and the branch state indexed by the current ambient object. Targets
and optional capabilities are supplied separately.
-/

namespace Hypostructure.Core

universe uAmbient uBranch

/-- Irreducible data shared by every tactic in one proof program. -/
structure Problem where
  Ambient : Type uAmbient
  Baseline : Ambient -> Prop
  BranchState : Ambient -> Type uBranch

end Hypostructure.Core
