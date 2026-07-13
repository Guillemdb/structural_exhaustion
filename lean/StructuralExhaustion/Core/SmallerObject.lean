import StructuralExhaustion.Core.Context

namespace StructuralExhaustion.Core

universe uAmbient uBranch

/-- An ambient object bundled with the rank decrease needed by every generic
minimality argument. -/
structure SmallerObject (P : Problem.{uAmbient, uBranch}) (G : P.Ambient) where
  value : P.Ambient
  decreases : P.rank value < P.rank G

namespace SmallerObject

/-- A smaller baseline object satisfies the target in a minimal-counterexample
context. -/
theorem target_of_baseline {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop} (ctx : MinimalCounterexampleContext P Target)
    (smaller : SmallerObject P ctx.G) (baseline : P.Baseline smaller.value) :
    Target smaller.value :=
  ctx.minimal smaller.value smaller.decreases baseline

/-- A smaller target-avoiding baseline object contradicts minimality. -/
theorem counterexample_impossible {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop} (ctx : MinimalCounterexampleContext P Target)
    (smaller : SmallerObject P ctx.G) (baseline : P.Baseline smaller.value)
    (avoids : ¬ Target smaller.value) : False :=
  avoids (target_of_baseline ctx smaller baseline)

end SmallerObject

end StructuralExhaustion.Core
