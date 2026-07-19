import StructuralExhaustion.Graph.FiniteLexFirstSimplePath

namespace StructuralExhaustion.Examples.FiniteLexFirstSimplePath

open StructuralExhaustion
open StructuralExhaustion.Graph

def lineGraph : SimpleGraph (Fin 4) := ⊤

def lineObject : FiniteObject (Fin 4) where
  graph := lineGraph
  input := {
    vertices := inferInstance
    decideAdj := by
      change DecidableRel fun left right : Fin 4 => left ≠ right
      infer_instance
  }

theorem zero_three_reachable : lineObject.graph.Reachable 0 3 := by
  letI : DecidableRel lineObject.graph.Adj := lineObject.input.decideAdj
  exact (show lineObject.graph.Adj 0 3 from by decide).reachable

noncomputable def profile :
    Graph.FiniteLexFirstSimplePath.Profile lineObject where
  source := 0
  target := 3
  reachable := zero_three_reachable

example : profile.firstPath.1.IsPath :=
  profile.firstPath_isPath

example : profile.firstPath.1.support.head? = some 0 :=
  profile.firstPath_head

example : profile.firstPath.1.support.getLast? = some 3 :=
  profile.firstPath_getLast

example (path : lineObject.graph.Path 0 3) :
    ¬ profile.code path < profile.code profile.firstPath :=
  profile.no_earlier_path path

example : profile.firstPath.1.length < 4 := by
  simpa [lineObject] using profile.firstPath_length_lt

end StructuralExhaustion.Examples.FiniteLexFirstSimplePath
