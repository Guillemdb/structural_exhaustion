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

/-!
`CertifiedReduction` is the tactic-independent semantic kernel shared by
certificate-driven closure profiles.  A CT may attach its own typed graph and
trace to this datum, while minimality, baseline preservation, and target
transport are proved only once here.
-/

/-- One explicitly supplied smaller object that retains the baseline and whose
target predicate transports back to the source object. -/
structure CertifiedReduction {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : MinimalCounterexampleContext P Target) where
  reduction : SmallerObject P ctx.G
  reducedBaseline : P.Baseline reduction.value
  targetMonotone : Target reduction.value → Target ctx.G

/-- The target-avoiding baseline witness forced by a certified reduction. -/
structure CertifiedReductionWitness {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : MinimalCounterexampleContext P Target)
    (input : CertifiedReduction ctx) : Prop where
  baseline : P.Baseline input.reduction.value
  avoids : ¬ Target input.reduction.value

namespace CertifiedReductionWitness

/-- A certified smaller counterexample contradicts the inherited minimality
kernel. -/
theorem contradiction {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {ctx : MinimalCounterexampleContext P Target}
    {input : CertifiedReduction ctx}
    (witness : CertifiedReductionWitness ctx input) : False :=
  SmallerObject.counterexample_impossible ctx input.reduction
    witness.baseline witness.avoids

end CertifiedReductionWitness

namespace CertifiedReduction

/-- Construct the target-avoiding witness using the source's avoidance and
the certified one-way target transport. -/
def witness {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {ctx : MinimalCounterexampleContext P Target}
    (input : CertifiedReduction ctx) :
    CertifiedReductionWitness ctx input where
  baseline := input.reducedBaseline
  avoids := fun reducedTarget => ctx.avoids (input.targetMonotone reducedTarget)

end CertifiedReduction

end StructuralExhaustion.Core
