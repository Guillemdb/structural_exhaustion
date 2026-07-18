import StructuralExhaustion.Graph.WalkPrefixFiltration

namespace StructuralExhaustion.Examples.WalkPrefixFiltration

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {V : Type u} {G : SimpleGraph V} {start finish : V}
variable {path : G.Walk start finish}
variable (isPath : path.IsPath)

noncomputable def profile : Graph.WalkPrefixFiltration.Profile path := ⟨isPath⟩

example (stage : (profile isPath).Stage) :
    ((profile isPath).prefixSupport stage).Nodup :=
  (profile isPath).prefixSupport_nodup stage

example {earlier later : (profile isPath).Stage}
    (ordered : earlier.val ≤ later.val) :
    (profile isPath).prefixSupport earlier <+:
      (profile isPath).prefixSupport later :=
  (profile isPath).prefixSupport_prefix ordered

end StructuralExhaustion.Examples.WalkPrefixFiltration

