import StructuralExhaustion.Core.FiniteDeclaredSupportLedger

namespace StructuralExhaustion.Examples.FiniteDeclaredSupportLedger

open StructuralExhaustion

@[implicit_reducible] def keys : FinEnum (Fin 3) := inferInstance

def profile : Core.FiniteDeclaredSupportLedger.Profile (Fin 3) (Fin 7) where
  keys := keys
  vertexDecEq := inferInstance
  support
    | 0 => {0, 1}
    | 1 => {2, 3}
    | 2 => {4, 5}

theorem recognizes_exact_middle_key :
    ∃ hit : profile.Hit 3, profile.recognize 3 = some hit ∧
      hit.first.value = 1 := by
  native_decide

theorem misses_vertex_outside_declared_supports :
    profile.recognize 6 = none := by
  native_decide

end StructuralExhaustion.Examples.FiniteDeclaredSupportLedger
