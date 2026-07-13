import Erdos64EG.InternalProblem

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# CT1: local target-certificate validation

The graph layer consumes one explicit Mathlib cycle certificate and constructs
the typed C1 execution directly.  No walk or graph universe is enumerated.
-/

abbrev ct1Spec (V : Type u) := (staticInput V).ct1Spec
abbrev ct1TargetBridge (V : Type u) := (staticInput V).ct1TargetBridge

def ct1Input {V : Type u} (object : Object V)
    (baseline : Baseline object) : CT1.Input (problem V) where
  context := {
    G := object
    baseline := baseline
    state := ()
  }

/-- Exact successful CT1 run from an explicit power-of-two cycle. -/
def runCT1 {V : Type u} (object : Object V)
    (baseline : Baseline object)
    (cycle : CycleWithLength object.graph PowerOfTwoLength) :
    CT1.CertifiedC1Run (ct1Spec V) (ct1Input object baseline) :=
  (staticInput V).targetEncoding.run (ct1Input object baseline) cycle trivial

end Erdos64EG.Internal
