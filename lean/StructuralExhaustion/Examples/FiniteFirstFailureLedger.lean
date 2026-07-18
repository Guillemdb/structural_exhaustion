import StructuralExhaustion.Core.FiniteFirstFailureLedger
import StructuralExhaustion.Examples.FiniteColdGermLedger

namespace StructuralExhaustion.Examples.FiniteFirstFailureLedger

open StructuralExhaustion
open StructuralExhaustion.Core

/-!
Small non-Erdős transfer fixture for the exact five-way ledger bookkeeping.
It executes the existing three-stage cold-germ profile on two explicit sources;
the example exercises the same aggregate runner, provenance and partition
theorems used by the P13 cold branch.
-/

def sources : List Unit := [(), ()]

noncomputable def ledger :=
  Core.FiniteFirstFailureLedger.run FiniteColdGermLedger.firstFailure sources

example : ledger.length = 2 := by
  simpa [ledger, sources] using
    Core.FiniteFirstFailureLedger.run_length
      FiniteColdGermLedger.firstFailure sources

example :
    (Core.FiniteFirstFailureLedger.withTag
        FiniteColdGermLedger.firstFailure sources .f1).length +
      (Core.FiniteFirstFailureLedger.withTag
        FiniteColdGermLedger.firstFailure sources .f2).length +
      (Core.FiniteFirstFailureLedger.withTag
        FiniteColdGermLedger.firstFailure sources .f3).length +
      (Core.FiniteFirstFailureLedger.withTag
        FiniteColdGermLedger.firstFailure sources .f4).length +
      (Core.FiniteFirstFailureLedger.withTag
        FiniteColdGermLedger.firstFailure sources .f5).length = sources.length := by
  exact Core.FiniteFirstFailureLedger.partition
    FiniteColdGermLedger.firstFailure sources

end StructuralExhaustion.Examples.FiniteFirstFailureLedger
