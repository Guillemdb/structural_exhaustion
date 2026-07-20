import StructuralExhaustion.Core.WorkBudget

namespace StructuralExhaustion.Core.ChunkedArrayLookup

universe u

/-!
# Constant-depth lookup in fixed-width finite tables

Large literal arrays are often stored in small independently audited chunks.
`Table` owns the quotient/remainder bookkeeping for that representation, so an
application never unfolds a long chain of array appends merely to read one
entry.  The lookup examines one entry of the chunk directory and one entry of
the selected chunk; it never scans or flattens the table.
-/

/-- A finite chunk directory with one common nominal width.  The last chunk
may be shorter.  `fallback` makes lookup total, matching `Array.getD`. -/
structure Table (α : Type u) where
  width : Nat
  chunks : Array (Array α)
  fallback : α

namespace Table

/-- The selected chunk number for one flat index. -/
def chunkIndex (table : Table α) (index : Nat) : Nat :=
  index / table.width

/-- The selected within-chunk offset for one flat index. -/
def localIndex (table : Table α) (index : Nat) : Nat :=
  index % table.width

/-- Total constant-depth lookup. -/
def getD (table : Table α) (index : Nat) : α :=
  (table.chunks.getD (table.chunkIndex index) #[]).getD
    (table.localIndex index) table.fallback

/-- The public lookup is definitionally just the two safe array reads. -/
theorem getD_eq (table : Table α) (index : Nat) :
    table.getD index =
      (table.chunks.getD (index / table.width) #[]).getD
        (index % table.width) table.fallback :=
  rfl

/-- One lookup performs two bounded array accesses and no carrier scan. -/
def workBudget : PolynomialCheckBudget Nat :=
  PolynomialCheckBudget.constant id 2

theorem workBudget_checks (index : Nat) :
    workBudget.checks index = 2 :=
  rfl

end Table

end StructuralExhaustion.Core.ChunkedArrayLookup
