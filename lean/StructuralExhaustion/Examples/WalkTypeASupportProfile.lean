import StructuralExhaustion.Graph.WalkTypeASupportProfile

namespace StructuralExhaustion.Examples.WalkTypeASupportProfile

open StructuralExhaustion

example {V : Type*} (object : Graph.FiniteObject V)
    {left right : V} (walk : object.graph.Walk left right) :
    Graph.NegativeSupportHandoff.ConnectedOn object
      (Graph.WalkTypeASupportProfile.support object walk) :=
  Graph.WalkTypeASupportProfile.connectedOn object walk

end StructuralExhaustion.Examples.WalkTypeASupportProfile
