import Hypostructure.Core.Finite.Partition

/-!
# Domain-neutral ordered partition fixture

This uses a finite observable signature rather than a graph vertex type.  It
exercises the same Core schedule and partition laws that a PDE adapter can use
for finite profile classes.
-/

namespace Hypostructure.Fixtures.OrderedPartition

open Hypostructure.Core.Finite

def schedule : Enumeration (Fin 3) :=
  Enumeration.ofFinEnum (inferInstance : FinEnum (Fin 3))

def labelOf (value : Fin 3) : Fin 2 := ⟨value.1 % 2, by omega⟩

theorem labels_nodup :
    (Hypostructure.Core.Finite.OrderedPartition.labels schedule labelOf).Nodup :=
  Hypostructure.Core.Finite.OrderedPartition.labels_nodup schedule labelOf

theorem labels_cover (value : Fin 3) :
    value ∈ Hypostructure.Core.Finite.OrderedPartition.members schedule labelOf
      (labelOf value) :=
  Hypostructure.Core.Finite.OrderedPartition.members_cover schedule labelOf
    ((Enumeration.mem_ofFinEnum_values (inferInstance : FinEnum (Fin 3)) value))

theorem labels_length_bounded :
    (Hypostructure.Core.Finite.OrderedPartition.labels schedule labelOf).length ≤
      schedule.card :=
  Hypostructure.Core.Finite.OrderedPartition.labels_length_le schedule labelOf

end Hypostructure.Fixtures.OrderedPartition
