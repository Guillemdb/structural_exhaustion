import StructuralExhaustion.Graph.TypeAFirstEntryCoordinate

namespace StructuralExhaustion.Examples.TypeAFirstEntryCoordinate

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {V : Type u} (object : FiniteObject V)
variable (profile : TypeACanonicalReceiverTrace.SupportProfile object)
variable (port : TypeAAnchoredReturnCoordinate.Port object profile)
variable (anchored : TypeAAnchoredReturnCoordinate.AnchoredReturn object profile port)

open TypeAFirstEntryCoordinate

noncomputable example : FirstEntry object profile port anchored :=
  select object profile port anchored

example :
    let first := select object profile port anchored
    first.entry object profile port anchored ∈ profile.support ∧
      first.predecessor object profile port anchored ∉ profile.support ∧
      object.graph.Adj
        (first.predecessor object profile port anchored)
        (first.entry object profile port anchored) := by
  let first := select object profile port anchored
  exact ⟨first.entry_mem_support object profile port anchored,
    first.predecessor_outside object profile port anchored,
    first.predecessor_adjacent_entry object profile port anchored⟩

example :
    let first := select object profile port anchored
    (profile.supportObject object).degree
      (⟨first.entry object profile port anchored,
        first.entry_mem_support object profile port anchored⟩ : profile.Vertex) ≤ 2 := by
  let first := select object profile port anchored
  exact first.entry_internal_degree_le_two object profile port anchored

end StructuralExhaustion.Examples.TypeAFirstEntryCoordinate
