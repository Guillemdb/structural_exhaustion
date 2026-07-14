import EvenCycleExample.Problem
import StructuralExhaustion.Graph.FanWindowCycle
import StructuralExhaustion.Graph.TwoWindowCycle

namespace EvenCycleExample.FanWindowCycle

open StructuralExhaustion

universe u

/-!
Non-Erdős transfer of the framework's direct fan-window CT1 profile.  The
even-cycle problem has a different branch-state type and a different target
predicate; the same graph profile retains that state and proves every exact
closed pair direct-cycle-free on an avoiding branch.
-/

def avoidingStage {V : Type u} (object : Graph.FiniteObject V)
    (baseline : Baseline object) (state : PathState object)
    (avoids : ¬HasEvenCycle object) :=
  Graph.FanWindowCycle.verifiedAvoidingStage (staticInput V) object baseline
    state avoids

theorem closedPair_directCycleFree {V : Type u}
    (object : Graph.FiniteObject V) (baseline : Baseline object)
    (state : PathState object) (avoids : ¬HasEvenCycle object)
    {order : Nat} {path : SimpleGraph.pathGraph order ↪g object.graph}
    (pair : Graph.FanWindowCycle.ClosedPair path) :
    Graph.FanWindowCycle.DirectCycleFree
      (staticInput V).LengthOK pair :=
  (avoidingStage object baseline state avoids).directFree pair

def twoWindowAvoidingStage {V : Type u} (object : Graph.FiniteObject V)
    (baseline : Baseline object) (state : PathState object)
    (avoids : ¬HasEvenCycle object) :=
  Graph.TwoWindowCycle.verifiedAvoidingStage (staticInput V) object baseline
    state avoids

theorem twoWindow_directCycleFree {V : Type u}
    (object : Graph.FiniteObject V) (baseline : Baseline object)
    (state : PathState object) (avoids : ¬HasEvenCycle object)
    {firstOrder secondOrder : Nat}
    {firstPath : SimpleGraph.pathGraph firstOrder ↪g object.graph}
    {secondPath : SimpleGraph.pathGraph secondOrder ↪g object.graph}
    (data : Graph.TwoWindowCycle.Data firstPath secondPath) :
    Graph.TwoWindowCycle.DirectCycleFree
      (staticInput V).LengthOK data :=
  (twoWindowAvoidingStage object baseline state avoids).directFree data

end EvenCycleExample.FanWindowCycle
