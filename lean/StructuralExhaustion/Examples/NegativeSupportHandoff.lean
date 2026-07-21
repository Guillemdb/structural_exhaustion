import StructuralExhaustion.Routes.NegativeSupportHandoff

namespace StructuralExhaustion.Examples.NegativeSupportHandoffK5

open StructuralExhaustion

/-!
# Transfer check on the textbook complete graph `K₅`

The full vertex support of `K₅` is connected, every vertex is a high center
above the explicitly supplied threshold, and its exact cubic-baseline net
charge is negative.  The example exercises the ordinary negative-support
handoff independently of the Erdős package.
-/

abbrev Vertex := Fin 5

def graph : SimpleGraph Vertex := ⊤

def input : Graph.FiniteInput graph where
  vertices := inferInstance
  decideAdj := by
    change DecidableRel fun left right : Vertex => left ≠ right
    infer_instance

def object : Graph.FiniteObject Vertex := ⟨graph, input⟩

def threshold : Nat := 4

def chargeParameters : Graph.AssignedSupportCharge.Parameters where
  baseline := 3
  scale := 4

def connected :
    Graph.NegativeSupportHandoff.ConnectedOn object Finset.univ := by
  constructor
  · exact ⟨0, by simp⟩
  · intro left right _leftMem _rightMem
    by_cases equal : left = right
    · subst right
      refine ⟨.nil, by simp, ?_⟩
      intro vertex member
      simp at member
      simp
    · let path : object.graph.Walk left right :=
        .cons (show object.graph.Adj left right by exact equal) .nil
      refine ⟨path, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_def]
        simp [path, equal]
      · intro vertex _member
        simp

def support :
    Graph.NegativeSupportHandoff.ConnectedNegativeSupportWith object
      chargeParameters threshold where
  core := Finset.univ
  connected := connected
  negative := by decide

def high : support.HighSurplusWitness where
  center := 0
  center_mem := by simp [support]
  high := by decide

def ordinary :=
  Routes.NegativeSupportHandoff.ordinaryAtLeast chargeParameters threshold
    support high

example : ordinary.highSurplus.center = 0 :=
  rfl

example : ordinary.highSurplus.center ∈
    Graph.NegativeSupportHandoff.highCentersAtLeast object threshold support.core := by
  letI : DecidableEq Vertex := inferInstance
  change (0 : Vertex) ∈
    Graph.NegativeSupportHandoff.highCentersAtLeast object threshold support.core
  exact Finset.mem_filter.mpr ⟨high.center_mem, high.high⟩

example :
    (Graph.NegativeSupportHandoff.chargeProfileWith object chargeParameters
      threshold support.core).netCharge < 0 :=
  support.negative

end StructuralExhaustion.Examples.NegativeSupportHandoffK5
