import StructuralExhaustion.Core.Problem

namespace StructuralExhaustion.Core

universe uAmbient uBranch

/-- The inherited state of one branch, shared by dependent CT inputs and route
triggers. -/
structure BranchContext (P : Problem.{uAmbient, uBranch}) where
  G : P.Ambient
  baseline : P.Baseline G
  state : P.BranchState G

/-- A branch context on which the target has not yet been realized. -/
structure AvoidingContext (P : Problem.{uAmbient, uBranch})
    (Target : P.Ambient → Prop) extends BranchContext P where
  avoids : ¬ Target G

/-- The reusable minimality theorem attached to a fixed branch context. -/
def MinimalityKernel (P : Problem.{uAmbient, uBranch})
    (Target : P.Ambient → Prop) (ctx : BranchContext P) : Prop :=
  ∀ H : P.Ambient,
    P.rank H < P.rank ctx.G → P.Baseline H → Target H

/-- A target-avoiding branch equipped with the minimal-counterexample
principle. -/
structure MinimalCounterexampleContext (P : Problem.{uAmbient, uBranch})
    (Target : P.Ambient → Prop) extends AvoidingContext P Target where
  minimal : MinimalityKernel P Target toBranchContext

namespace AvoidingContext

/-- Extend a branch context with a target-avoidance proof. -/
def ofBranch {P : Problem.{uAmbient, uBranch}} {Target : P.Ambient → Prop}
    (ctx : BranchContext P) (avoids : ¬ Target ctx.G) :
    AvoidingContext P Target where
  toBranchContext := ctx
  avoids := avoids

end AvoidingContext

namespace MinimalCounterexampleContext

/-- Build a minimal-counterexample context without duplicating the inherited
branch fields. -/
def ofAvoiding {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop} (ctx : AvoidingContext P Target)
    (minimal : MinimalityKernel P Target ctx.toBranchContext) :
    MinimalCounterexampleContext P Target where
  toAvoidingContext := ctx
  minimal := minimal

end MinimalCounterexampleContext

end StructuralExhaustion.Core
