import StructuralExhaustion.Core.FinitePriorityOptionScanWork

namespace StructuralExhaustion.Examples.FinitePriorityOptionScanWork

open StructuralExhaustion.Core

example (codes : FinEnum (Fin 7)) :
    FinitePriorityOptionScanWork.checks (some true) codes = 1 := rfl

example (codes : FinEnum (Fin 7)) :
    FinitePriorityOptionScanWork.checks (none : Option Bool) codes ≤
      codes.card + 1 :=
  FinitePriorityOptionScanWork.checks_le_codes_add_one none codes

end StructuralExhaustion.Examples.FinitePriorityOptionScanWork
