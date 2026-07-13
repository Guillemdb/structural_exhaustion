import StructuralExhaustion.Core.AutomationFirst

namespace StructuralExhaustion.CT12

universe uAmbient uBranch uState uPeeled uDemand uTier

/-- Restoration either produces a strictly smaller loop state or a semantic
residual.  The decrease proof is the only license for recursion. -/
inductive Restoration (State : Nat → Type uState)
    (Demand : Type uDemand) (Tier : Type uTier) (load : Nat) where
  | continue (next : Nat) (state : State next) (decreases : next < load)
  | demand (residual : Demand)
  | tier (residual : Tier)

/-- A finite restoration search space that is nonempty by construction.
The framework's reference policy always selects `first`; optimized policies
may inspect `remaining` only after proving refinement. -/
structure RestorationOptions (State : Nat → Type uState)
    (Demand : Type uDemand) (Tier : Type uTier) (load : Nat) where
  first : Restoration State Demand Tier load
  remaining : List (Restoration State Demand Tier load) := []

namespace RestorationOptions

def toList (options : RestorationOptions State Demand Tier load) :
    List (Restoration State Demand Tier load) :=
  options.first :: options.remaining

theorem first_mem (options : RestorationOptions State Demand Tier load) :
    options.first ∈ options.toList := by
  simp [toList]

end RestorationOptions

structure Capability (P : Core.Problem.{uAmbient, uBranch}) where
  State : Nat → Type uState
  DemandResidual : Type uDemand
  TierResidual : Type uTier
  Peeled : {n : Nat} → State (n + 1) → Type uPeeled
  peel : {n : Nat} → (state : State (n + 1)) → Peeled state
  restorations : {n : Nat} → {state : State (n + 1)} →
    Peeled state → RestorationOptions State DemandResidual TierResidual (n + 1)

structure Input {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability.{uAmbient, uBranch, uState, uPeeled, uDemand, uTier} P) where
  context : Core.BranchContext P
  load : Nat
  state : capability.State load

/-- Route-facing CT12 trigger.  The indexed loop state is the only seed added
to the inherited branch context. -/
structure Trigger {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability.{uAmbient, uBranch, uState, uPeeled, uDemand, uTier} P)
    (_context : Core.BranchContext P) where
  load : Nat
  state : capability.State load

namespace Input

def ofTrigger {P : Core.Problem.{uAmbient, uBranch}}
    {capability : Capability.{uAmbient, uBranch, uState, uPeeled, uDemand, uTier} P}
    (context : Core.BranchContext P) (trigger : Trigger capability context) :
    Input capability where
  context := context
  load := trigger.load
  state := trigger.state

end Input

def tacticInterface {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability.{uAmbient, uBranch, uState, uPeeled, uDemand, uTier} P) :
    Core.Routing.TacticInterface where
  Context := Core.BranchContext P
  Trigger := Trigger capability

end StructuralExhaustion.CT12
