import StructuralExhaustion.Graph.TypeACanonicalReceiverTrace

namespace StructuralExhaustion.Examples.TypeACanonicalReceiverTrace

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {V : Type u} (object : FiniteObject V)
variable (profile : Graph.TypeACanonicalReceiverTrace.SupportProfile object)

/-! Problem-independent transfer: every internal cubic source receives one
ordered-BFS trace, its endpoint is low-degree, and every strict prefix vertex
is internally cubic. -/

example (cubic : profile.Cubic object) :
    (profile.trace object cubic).IsPath :=
  profile.trace_isPath object cubic

example (cubic : profile.Cubic object) :
    (profile.supportObject object).degree
      (profile.receiverSelection object cubic).vertex ≤ 2 :=
  profile.receiver_degree_le_two object cubic

example (cubic : profile.Cubic object) (index : Nat)
    (before : index < ((profile.bfs object cubic).treeWalk
      (profile.preconnected object)
      (profile.receiverSelection object cubic).vertex).length) :
    (profile.supportObject object).degree
      (((profile.bfs object cubic).treeWalk
        (profile.preconnected object)
        (profile.receiverSelection object cubic).vertex).getVert index) = 3 :=
  profile.receiverSelection_internal_degree_eq_three object cubic index before

end StructuralExhaustion.Examples.TypeACanonicalReceiverTrace
