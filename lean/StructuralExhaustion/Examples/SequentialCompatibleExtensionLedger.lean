import StructuralExhaustion.Core.SequentialCompatibleExtensionLedger

namespace StructuralExhaustion.Examples.SequentialCompatibleExtensionLedger

open StructuralExhaustion.Core
open StructuralExhaustion.Core.SequentialCompatibleExtensionLedger

/-- A small non-Erdős transfer.  The aggregate is a counter and only marked
windows admit a compatible extension. -/
def windows : OrderedCollection (Fin 3) where
  values := [0, 1, 2]
  nodup := by decide
  decEq := inferInstance

def Extension (_ : Nat) (window : Fin 3) : Type :=
  if window = 1 then Empty else Unit

def profile : Profile where
  Window := Fin 3
  windows := windows
  Aggregate := Nat
  Valid := fun _ => True
  initial := 0
  initialValid := trivial
  Extension := Extension
  extend := fun {aggregate window} (_extension : Extension aggregate window) => aggregate + 1
  extendValid := by simp

/-- The generic runner checks exactly the three scheduled windows. -/
theorem checks_three : checks profile = 3 := by
  native_decide

/-- The runner partitions the scheduled local work into accepted and rejected
windows without duplication. -/
theorem runner_partition :
    (run profile).hot.length + (run profile).cold.length = 3 := by
  simpa [profile, windows] using (run profile).length_partition

theorem runner_hot_nodup : (run profile).hot.Nodup := by
  exact (run profile).hot_nodup profile.windows.nodup

theorem runner_cold_nodup : (run profile).cold.Nodup := by
  exact (run profile).cold_nodup profile.windows.nodup

/-- Every accepted extension preserves validity through the entire run. -/
theorem runner_final_valid : profile.Valid (run profile).finalAggregate :=
  (run profile).finalValid

end StructuralExhaustion.Examples.SequentialCompatibleExtensionLedger
