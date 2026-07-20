import StructuralExhaustion.Core.ChunkedArrayLookup

namespace StructuralExhaustion.Examples.ChunkedArrayLookup

open Core

/-- Non-problem-specific fixture with two full width-three chunks and one
short tail. -/
def sevenNaturals : Core.ChunkedArrayLookup.Table Nat where
  width := 3
  chunks := #[#[10, 11, 12], #[20, 21, 22], #[30]]
  fallback := 99

example : sevenNaturals.getD 0 = 10 := by decide
example : sevenNaturals.getD 4 = 21 := by decide
example : sevenNaturals.getD 6 = 30 := by decide
example : sevenNaturals.getD 7 = 99 := by decide

example : Core.ChunkedArrayLookup.Table.workBudget.checks 6 = 2 :=
  Core.ChunkedArrayLookup.Table.workBudget_checks 6

end StructuralExhaustion.Examples.ChunkedArrayLookup
