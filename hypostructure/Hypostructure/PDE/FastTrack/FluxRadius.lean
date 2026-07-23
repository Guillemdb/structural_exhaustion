import Hypostructure.PDE.Model
import Hypostructure.Core.Residual.Query
import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Strategy

/-!
# PDE flux-radius normal form

This is the PDE-facing registration boundary for the flux/sign stage of a
regularity proof.  Radii are represented observables supplied by the incoming
residual; the PDE layer never enumerates the continuum.  The analytic estimate
that proves a strict draining gap is supplied by the application.
-/

namespace Hypostructure.PDE.FastTrack.FluxRadius

universe uPrevious uModel uRadius

open Hypostructure

structure Profile {Previous : Type uPrevious}
    (M : PDE.LocalModel.{uModel}) where
  Radius : Previous -> Type uRadius
  radii : Core.Residual.Query Previous
    (fun previous => Core.Finite.Enumeration (Radius previous))
  flux : (previous : Previous) -> M.problem.Ambient ->
    Radius previous -> Int
  draining : (previous : Previous) -> M.problem.Ambient ->
    Radius previous -> Prop
  drainingDecidable : (previous : Previous) ->
    (object : M.problem.Ambient) -> (radius : Radius previous) ->
      Decidable (draining previous object radius)
  /-- The strict estimate is a semantic input, not a claimed consequence of
  registration. -/
  strictGap : (previous : Previous) -> M.problem.Ambient -> Prop
  strictGapDecidable : (previous : Previous) ->
    (object : M.problem.Ambient) -> Decidable (strictGap previous object)
  strictGapSound : (previous : Previous) -> (object : M.problem.Ambient) ->
    strictGap previous object ->
      forall radius, radius ∈ (radii.read previous).values ->
        draining previous object radius

inductive Outcome {Previous : Type uPrevious} {M : PDE.LocalModel.{uModel}}
    (profile : Profile (M := M) (Previous := Previous))
    (previous : Previous) (object : M.problem.Ambient) where
  | draining (proof : profile.strictGap previous object)
  | feeding (radius : profile.Radius previous)
      (member : radius ∈ (profile.radii.read previous).values)
      (notDraining : ¬ profile.draining previous object radius)
  | equality (radius : profile.Radius previous)
      (member : radius ∈ (profile.radii.read previous).values)

def classify {Previous : Type uPrevious} {M : PDE.LocalModel.{uModel}}
    (profile : Profile (M := M) (Previous := Previous))
    (previous : Previous) (object : M.problem.Ambient) :
    Sum (PLift (profile.strictGap previous object))
      (Core.Finite.Enumeration (profile.Radius previous)) :=
  @dite _ (profile.strictGap previous object)
    (profile.strictGapDecidable previous object)
    (fun h => Sum.inl ⟨h⟩)
    (fun _ => Sum.inr (profile.radii.read previous))

/-! ## Strategy execution

The row itself is an executable Core strategy.  A strict-gap branch closes
locally; its complementary branch retains the complete radius schedule as a
typed residual payload.  Later rows may consume that residual without
recomputing the radius scan.
-/

/-! The represented object is deliberately supplied as a residual query by
the caller; this keeps the strategy independent of any particular equation
model while retaining the literal predecessor. -/
def strategy {Previous : Type uPrevious} {M : PDE.LocalModel.{uModel}}
    (profile : Profile (M := M) (Previous := Previous))
    (state : Core.Residual.Query Previous (fun _ => M.problem.Ambient)) :
    Core.Strategy.Contract Previous :=
  Core.Strategy.binaryContract
    (fun previous => profile.strictGap previous (state.read previous))
    (fun previous => profile.strictGapDecidable previous (state.read previous))
    (fun previous => profile.radii.read previous)

end Hypostructure.PDE.FastTrack.FluxRadius
