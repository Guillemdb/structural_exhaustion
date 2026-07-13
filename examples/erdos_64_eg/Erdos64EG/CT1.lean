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

/-- CT1 target encoding for the manuscript's local return certificate. -/
def mersenneReturnEncoding (V : Type u) :
    CT1.TargetCertificateEncoding (P := problem V) (@Target V) where
  Code := fun object => MersenneReturn object.graph
  Accepts := fun _object _return => True
  encode := by
    intro object target
    obtain ⟨certificate⟩ := (target_iff_hasMersenneReturn object).mp target
    exact ⟨certificate, trivial⟩
  decode := by
    intro object certificate _accepted
    exact (target_iff_hasMersenneReturn object).mpr ⟨certificate⟩

abbrev ct1Spec (V : Type u) := (mersenneReturnEncoding V).spec
abbrev ct1TargetBridge (V : Type u) :=
  (mersenneReturnEncoding V).bridge

def ct1Input {V : Type u} (object : Object V)
    (baseline : Baseline object) : CT1.Input (problem V) where
  context := {
    G := object
    baseline := baseline
    state := ()
  }

/-- Exact successful CT1 run from an explicit Mersenne return. -/
def runMersenneCT1 {V : Type u} (object : Object V)
    (baseline : Baseline object)
    (certificate : MersenneReturn object.graph) :
    CT1.CertifiedC1Run (ct1Spec V) (ct1Input object baseline) :=
  (mersenneReturnEncoding V).run (ct1Input object baseline)
    certificate trivial

/-- A concrete power-of-two cycle is first converted to its local rooted
return and then validated through the same Mersenne CT1 contract. -/
def runCT1 {V : Type u} (object : Object V)
    (baseline : Baseline object)
    (cycle : CycleWithLength object.graph PowerOfTwoLength) :
    CT1.CertifiedC1Run (ct1Spec V) (ct1Input object baseline) :=
  runMersenneCT1 object baseline (EdgeRootedReturn.ofCycle cycle)

/-- Exact zero-enumeration CT1 avoiding run for a target-avoiding branch. -/
def runAvoidingCT1 {V : Type u} (object : Object V)
    (baseline : Baseline object) (avoids : ¬ Target object) :
    CT1.CertifiedAvoidingRun (ct1Spec V) (ct1Input object baseline) :=
  (mersenneReturnEncoding V).runAvoiding
    (ct1Input object baseline) avoids

theorem runAvoidingCT1_returnSets_disjoint {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬ Target object) :
    ∀ dart : object.graph.Dart,
      Disjoint (returnSet object.graph dart) MersenneSet :=
  (not_target_iff_returnSets_disjoint object).mp
    ((mersenneReturnEncoding V).not_publicTarget_of_runAvoiding
      (ct1Input object baseline) avoids)

end Erdos64EG.Internal
