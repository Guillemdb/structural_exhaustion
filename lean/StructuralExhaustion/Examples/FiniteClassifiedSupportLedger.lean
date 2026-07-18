import StructuralExhaustion.Core.FiniteClassifiedSupportLedger

namespace StructuralExhaustion.Examples.FiniteClassifiedSupportLedger

open StructuralExhaustion

@[implicit_reducible] def keys : FinEnum (Fin 3) := inferInstance

def profile : Core.FiniteClassifiedSupportLedger.Profile (Fin 3) (Fin 7) String where
  keys := keys
  vertexDecEq := inferInstance
  tokenDecEq := inferInstance
  support
    | 0 => {0, 1}
    | 1 => ∅
    | 2 => {4, 5}
  charge
    | 0 => some "type-B-0"
    | 1 => none
    | 2 => some "route-8-2"
  absent_support_empty := by intro key; fin_cases key <;> simp

theorem recognizes_charged_typeB_key :
    ∃ hit : profile.Hit 1, profile.recognize 1 = some hit ∧
      hit.first.value.1 = 0 := by
  native_decide

theorem absent_key_has_empty_support : profile.support 1 = ∅ := by
  exact profile.absent_key_support_empty 1 rfl

theorem charged_scan_ignores_absent_key : profile.recognize 3 = none := by
  native_decide

theorem scan_cost_at_most_declared_cost : profile.checks ≤ profile.keys.card :=
  profile.checks_le_declared

end StructuralExhaustion.Examples.FiniteClassifiedSupportLedger
