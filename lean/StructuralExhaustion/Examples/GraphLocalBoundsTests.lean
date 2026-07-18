import StructuralExhaustion.Graph.InducedPathDiameter
import StructuralExhaustion.Graph.SubcubicMooreBound

namespace StructuralExhaustion.Examples.GraphLocalBoundsTests

open StructuralExhaustion

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Non-Erdős transfer check for the shortest-path induced-path theorem. -/
example (preconnected : G.Preconnected) (free : Graph.InducedPathFree G 13)
    (left right : V) :
    ∃ path : G.Walk left right, path.IsPath ∧ path.length ≤ 11 :=
  Graph.InducedPathDiameter.diameterAtMostEleven_of_p13Free
    preconnected free left right

/-- Non-Erdős transfer check for the exact local subcubic Moore count. -/
example {object : Graph.FiniteObject V}
    (profile : Graph.OrderedBFSTree.Profile object)
    (preconnected : object.graph.Preconnected)
    (degreeLe : ∀ vertex, object.degree vertex ≤ 3)
    (radius : ∀ vertex : V,
      ∃ path : object.graph.Walk profile.root vertex,
        path.IsPath ∧ path.length ≤ 11) :
    object.input.vertices.card ≤ 6142 :=
  profile.card_vertices_le_6142_of_radius_eleven
    preconnected degreeLe radius

#print axioms Graph.InducedPathDiameter.diameterAtMostEleven_of_p13Free
#print axioms Graph.OrderedBFSTree.Profile.card_vertices_le_6142_of_radius_eleven

end StructuralExhaustion.Examples.GraphLocalBoundsTests
