import Hypostructure.Core.Closure
import Hypostructure.Graph.Target

/-!
Graph target-hit closure.

This module is a thin compatibility shim over `Hypostructure.Core.Closure`:
the API is core-owned and domain-agnostic, while this file only adds the graph
specialization used by graph nodes (including the cycle bridge).
-/

namespace Hypostructure.Graph.TargetClosure

open Hypostructure.Core

universe u v

abbrev AvoidsTarget (Target : FiniteObject.{u} -> Prop)
    (object : FiniteObject.{u}) := Core.Closure.TargetAvoidance Target object

abbrev HitBridge (Target : FiniteObject.{u} -> Prop)
    (object : FiniteObject.{u}) (Hit : Type v) :=
  Core.Closure.TargetWitnessBridge Target object Hit

def closeHit {Target : FiniteObject.{u} -> Prop}
    {object : FiniteObject.{u}} {Hit : Type v}
    (avoidance : AvoidsTarget Target object)
    (bridge : HitBridge Target object Hit) (hit : Hit) :
    Closure.Result False :=
  Closure.closeTargetHit avoidance bridge hit

def cycleHitBridge {object : FiniteObject.{u}} {LengthOK : Nat -> Prop} :
    HitBridge (HasCycleWithLength LengthOK) object
      (CycleCertificate object LengthOK) :=
  ⟨fun certificate => ⟨certificate⟩⟩

def closeCycleHit {object : FiniteObject.{u}} {LengthOK : Nat -> Prop}
    (avoidance : AvoidsTarget (HasCycleWithLength LengthOK) object)
    (certificate : CycleCertificate object LengthOK) :
    Closure.Result False :=
  closeHit avoidance cycleHitBridge certificate

end Hypostructure.Graph.TargetClosure
