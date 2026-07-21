import Hypostructure.Core.Prelude

/-!
# CT12 well-founded peeling specification

CT12 repeatedly peels one positive-load state.  The application supplies the
indexed state family and the local restoration alternatives.  The framework
selects an alternative, checks the embedded strict decrease, runs the
well-founded recursion, and owns every terminal and ledger update.
-/

namespace Hypostructure.CT12

universe uPrevious uState uPeeled uDemand uTier

/-- A restoration either continues at a strictly smaller load or emits one of
the two typed semantic residuals.  The decrease proof is the sole license for
another loop iteration. -/
inductive Restoration (State : Nat -> Type uState)
    (DemandResidual : Type uDemand) (TierResidual : Type uTier)
    (load : Nat) where
  | continue (next : Nat) (state : State next) (decreases : next < load)
  | demand (residual : DemandResidual)
  | tier (residual : TierResidual)

/-- A finite restoration family with a canonical first member.  Nonemptiness
is structural, so CT12 never invents a fallback or searches an ambient type. -/
structure RestorationOptions (State : Nat -> Type uState)
    (DemandResidual : Type uDemand) (TierResidual : Type uTier)
    (load : Nat) where
  first : Restoration State DemandResidual TierResidual load
  remaining : List (Restoration State DemandResidual TierResidual load) := []

namespace RestorationOptions

/-- Exact finite restoration schedule in policy order. -/
def toList (options : RestorationOptions State DemandResidual TierResidual load) :
    List (Restoration State DemandResidual TierResidual load) :=
  options.first :: options.remaining

/-- Framework restoration policy: use the first supplied admissible option. -/
def selected (options : RestorationOptions State DemandResidual TierResidual load) :
    Restoration State DemandResidual TierResidual load :=
  options.first

/-- The framework-selected restoration belongs to the supplied finite family. -/
theorem selected_mem
    (options : RestorationOptions State DemandResidual TierResidual load) :
    List.Mem options.selected options.toList := by
  exact List.Mem.head _

/-- Every restoration schedule is nonempty by construction. -/
theorem toList_nonempty
    (options : RestorationOptions State DemandResidual TierResidual load) :
    Not (options.toList = []) := by
  change Not (options.first :: options.remaining = [])
  exact List.cons_ne_nil options.first options.remaining

end RestorationOptions

/-- Domain-neutral local peeling semantics over one literal predecessor.

The predecessor may determine all carriers.  In particular, `State`,
`Peeled`, and both residual types need not come from ambient typeclasses or a
detached universe. -/
structure Spec (Previous : Type uPrevious) where
  State : Previous -> Nat -> Type uState
  Peeled : {previous : Previous} -> {load : Nat} ->
    State previous (load + 1) -> Type uPeeled
  DemandResidual : Previous -> Type uDemand
  TierResidual : Previous -> Type uTier
  peel : {previous : Previous} -> {load : Nat} ->
    (state : State previous (load + 1)) -> Peeled state
  restorations : {previous : Previous} -> {load : Nat} ->
    {state : State previous (load + 1)} -> (peeled : Peeled state) ->
      RestorationOptions (State previous) (DemandResidual previous)
        (TierResidual previous) (load + 1)

end Hypostructure.CT12
