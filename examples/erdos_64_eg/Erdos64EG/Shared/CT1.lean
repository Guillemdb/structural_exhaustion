import Erdos64EG.TargetAlgebra

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# CT1: Mersenne edge-rooted target execution

The target code is one edge-rooted Mersenne return.  The graph layer converts
that local certificate to the official power-of-two cycle target.  On a
hypothetical counterexample, the exact disjoint-return theorem constructs the
typed avoiding residual directly.  Neither path enumerates walks or graphs.
-/

/-- Problem name for the graph profile's edge-rooted target encoding. -/
abbrev mersenneReturnEncoding (V : Type u) :=
  (staticInput V).edgeRootedEncoding

abbrev ct1Spec (V : Type u) := (mersenneReturnEncoding V).spec
abbrev ct1TargetBridge (V : Type u) :=
  (mersenneReturnEncoding V).bridge

def ct1Input {V : Type u} (object : Object V)
    (baseline : Baseline object) : CT1.Input (problem V) :=
  (staticInput V).edgeRootedInput object baseline ()

/-- Exact successful CT1 run from an explicit Mersenne return. -/
def runMersenneCT1 {V : Type u} (object : Object V)
    (baseline : Baseline object)
    (certificate : MersenneReturn object.graph) :
    CT1.CertifiedC1Run (ct1Spec V) (ct1Input object baseline) :=
  (staticInput V).runRootedReturnCT1 object baseline () certificate

/-- A concrete power-of-two cycle is first converted to its local rooted
return and then validated through the same Mersenne CT1 contract. -/
def runCT1 {V : Type u} (object : Object V)
    (baseline : Baseline object)
    (cycle : CycleWithLength object.graph PowerOfTwoLength) :
    CT1.CertifiedC1Run (ct1Spec V) (ct1Input object baseline) :=
  (staticInput V).runCycleAsRootedReturnCT1 object baseline () cycle

/-- Exact zero-enumeration CT1 avoiding run for a target-avoiding branch. -/
def runAvoidingCT1 {V : Type u} (object : Object V)
    (baseline : Baseline object) (avoids : ¬ Target object) :
    CT1.CertifiedAvoidingRun (ct1Spec V) (ct1Input object baseline) :=
  (staticInput V).runAvoidingRootedReturnCT1 object baseline () avoids

theorem runAvoidingCT1_returnSets_disjoint {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬ Target object) :
    ∀ dart : object.graph.Dart,
      Disjoint (returnSet object.graph dart) MersenneSet :=
  by
    change ∀ dart : object.graph.Dart,
      Disjoint (edgeReturnSet object.graph dart)
        {length | (staticInput V).ReturnLengthOK length}
    exact (staticInput V).runAvoidingRootedReturnCT1_returnSets_disjoint
      object baseline () avoids

end Erdos64EG.Internal
