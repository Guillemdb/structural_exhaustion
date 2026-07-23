import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Query
import Hypostructure.PDE.Model

/-!
# PDE connected-support packaging

This is the PDE counterpart of Graph support components.  The carrier is a
finite represented schedule supplied by the residual; the ambient continuum
and all analytic domains remain abstract.  Connectivity is supplied as an
analytic relation on that carrier.
-/

namespace Hypostructure.PDE.SupportComponents

universe uPrevious uModel uCarrier

inductive Reachable {Carrier : Type uCarrier}
    (adjacent : Carrier -> Carrier -> Prop) : Carrier -> Carrier -> Prop
  | refl (x) : Reachable adjacent x x
  | step {x y z} : Reachable adjacent x y -> adjacent y z ->
      Reachable adjacent x z

structure Component {Carrier : Type uCarrier}
    (adjacent : Carrier -> Carrier -> Prop)
    (support : Finset Carrier) where
  seed : Carrier
  seed_mem : seed ∈ support
  connected : forall carrier, carrier ∈ support ->
    Reachable adjacent seed carrier

structure Profile {Previous : Type uPrevious}
    (M : PDE.LocalModel.{uModel}) where
  Carrier : Previous -> Type uCarrier
  schedule : Core.Residual.Query Previous
    (fun previous => Core.Finite.Enumeration (Carrier previous))
  adjacent : (previous : Previous) ->
    Carrier previous -> Carrier previous -> Prop
  adjacentDecidable : (previous : Previous) ->
    (left right : Carrier previous) ->
      Decidable (adjacent previous left right)

def component {Previous : Type uPrevious}
    {M : PDE.LocalModel.{uModel}}
    (profile : Profile (M := M) (Previous := Previous))
    (previous : Previous)
    (support : Finset (profile.Carrier previous))
    (seed : profile.Carrier previous)
    (seed_mem : seed ∈ support)
    (connected : forall carrier, carrier ∈ support ->
      Reachable (profile.adjacent previous) seed carrier) :
    Component (profile.adjacent previous) support where
  seed := seed
  seed_mem := seed_mem
  connected := connected

end Hypostructure.PDE.SupportComponents
