import Hypostructure.Core.Progress

/-!
# Branch contexts

Contexts retain only the current ambient object, its baseline proof, and its
dependent branch state. Target avoidance and optional minimality are layered on
top without introducing a second residual carrier.
-/

namespace Hypostructure.Core

universe uAmbient uBranch uMeasure

/-- The inherited state of one branch. -/
structure BranchContext (P : Problem.{uAmbient, uBranch}) where
  G : P.Ambient
  baseline : P.Baseline G
  state : P.BranchState G

/-- A branch context on which the external target has not been realized. -/
structure AvoidingContext (P : Problem.{uAmbient, uBranch})
    (Target : P.Ambient -> Prop) extends BranchContext P where
  avoids : Not (Target G)

/-- Every strictly smaller baseline object satisfies the target. -/
def MinimalityKernel (P : Problem.{uAmbient, uBranch})
    (Target : P.Ambient -> Prop)
    (progress : Progress.{uAmbient, uBranch, uMeasure} P)
    (ctx : BranchContext P) : Prop :=
  forall H : P.Ambient,
    progress.Smaller H ctx.G -> P.Baseline H -> Target H

/-- A target-avoiding branch equipped with a minimal-counterexample principle
for one explicit progress profile. -/
structure MinimalCounterexampleContext (P : Problem.{uAmbient, uBranch})
    (Target : P.Ambient -> Prop)
    (progress : Progress.{uAmbient, uBranch, uMeasure} P)
    extends AvoidingContext P Target where
  minimal : MinimalityKernel P Target progress toBranchContext

namespace AvoidingContext

/-- Extend an existing branch context by its target-avoidance proof. -/
def ofBranch {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop} (ctx : BranchContext P)
    (avoids : Not (Target ctx.G)) : AvoidingContext P Target where
  toBranchContext := ctx
  avoids := avoids

/-- Select a minimal target-avoiding baseline object using only the registered
well-founded progress relation and a branch-state initializer. -/
theorem exists_minimalCounterexample
    {P : Problem.{uAmbient, uBranch}} {Target : P.Ambient -> Prop}
    (ctx : AvoidingContext P Target)
    (progress : Progress.{uAmbient, uBranch, uMeasure} P)
    (stateOf : (G : P.Ambient) -> P.BranchState G) :
    Nonempty (MinimalCounterexampleContext P Target progress) := by
  let IsCounterexample : P.Ambient -> Prop :=
    fun G => P.Baseline G ∧ Not (Target G)
  have nonempty : Set.Nonempty {G | IsCounterexample G} :=
    ⟨ctx.G, ctx.baseline, ctx.avoids⟩
  obtain ⟨G, hG, minimalG⟩ :=
    progress.wellFounded_smaller.has_min {G | IsCounterexample G} nonempty
  refine ⟨{
    toAvoidingContext := {
      toBranchContext := {
        G := G
        baseline := hG.1
        state := stateOf G
      }
      avoids := hG.2
    }
    minimal := ?_
  }⟩
  intro H smaller baselineH
  by_contra avoidsH
  exact minimalG H ⟨baselineH, avoidsH⟩ smaller

end AvoidingContext

namespace MinimalCounterexampleContext

/-- Build a minimal context from an avoiding context and its proved minimality
kernel without duplicating inherited fields. -/
def ofAvoiding {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Progress.{uAmbient, uBranch, uMeasure} P}
    (ctx : AvoidingContext P Target)
    (minimal : MinimalityKernel P Target progress ctx.toBranchContext) :
    MinimalCounterexampleContext P Target progress where
  toAvoidingContext := ctx
  minimal := minimal

/-- The target consequence for any strictly smaller baseline object. -/
theorem target_of_smaller
    {P : Problem.{uAmbient, uBranch}} {Target : P.Ambient -> Prop}
    {progress : Progress.{uAmbient, uBranch, uMeasure} P}
    (ctx : MinimalCounterexampleContext P Target progress) {H : P.Ambient}
    (smaller : progress.Smaller H ctx.G) (baseline : P.Baseline H) :
    Target H :=
  ctx.minimal H smaller baseline

/-- A strictly smaller avoiding branch contradicts minimality. -/
theorem contradiction_of_smaller
    {P : Problem.{uAmbient, uBranch}} {Target : P.Ambient -> Prop}
    {progress : Progress.{uAmbient, uBranch, uMeasure} P}
    (ctx : MinimalCounterexampleContext P Target progress)
    (candidate : AvoidingContext P Target)
    (smaller : progress.Smaller candidate.G ctx.G) : False :=
  candidate.avoids (ctx.target_of_smaller smaller candidate.baseline)

end MinimalCounterexampleContext

end Hypostructure.Core
