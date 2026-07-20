import StructuralExhaustion.Core.EnumerationCombinators

namespace StructuralExhaustion.Core.ChunkedFiniteCount

universe u

/-!
# Kernel-checkable chunked counts for fixed finite predicates

`chunkedCount` changes only the reduction shape of a finite filter count.
The generic theorem below proves that it is exactly the ordinary count.  A
fixed application may therefore certify a moderately large local table with
small chunks, avoiding both `native_decide` and one deeply nested reduction.
-/

/-- Count accepted entries in at most `fuel` leading chunks, then count the
remaining suffix.  The suffix clause makes the definition exact for every
fuel; clients need no coverage side condition. -/
def chunkedCount (accepts : α → Bool) (chunkSize : Nat) :
    Nat → List α → Nat
  | 0, values => (values.filter accepts).length
  | fuel + 1, values =>
      ((values.take chunkSize).filter accepts).length +
        chunkedCount accepts chunkSize fuel (values.drop chunkSize)

theorem chunkedCount_eq_filter_length (accepts : α → Bool)
    (chunkSize fuel : Nat) (values : List α) :
    chunkedCount accepts chunkSize fuel values =
      (values.filter accepts).length := by
  induction fuel generalizing values with
  | zero => rfl
  | succ fuel ih =>
      rw [chunkedCount, ih]
      rw [← List.length_append, ← List.filter_append]
      simp only [List.take_append_drop]

/-- Exact subtype cardinality through the deterministic source enumeration
and a chunked Boolean count. -/
theorem subtype_card_eq_chunkedCount
    (enumeration : FinEnum α) (predicate : α → Prop)
    (decidePredicate : ∀ value, Decidable (predicate value))
    (accepts : α → Bool)
    (accepts_iff : ∀ value, accepts value = true ↔ predicate value)
    (chunkSize fuel : Nat) :
    (Enumeration.subtype enumeration predicate decidePredicate).card =
      chunkedCount accepts chunkSize fuel enumeration.orderedValues := by
  rw [chunkedCount_eq_filter_length]
  rw [Enumeration.subtype_card_eq_filter]
  letI : DecidableEq α := enumeration.decEq
  letI : DecidablePred predicate := decidePredicate
  have univ_eq :
      (@Finset.univ α (@FinEnum.instFintype α enumeration)) =
        enumeration.orderedValues.toFinset := by
    ext value
    simp
  rw [univ_eq]
  have filter_equiv :
      enumeration.orderedValues.filter accepts =
        enumeration.orderedValues.filter fun value => decide (predicate value) := by
    apply List.filter_congr
    intro value _member
    apply Bool.eq_iff_iff.mpr
    simpa using accepts_iff value
  rw [filter_equiv]
  rw [← List.toFinset_card_of_nodup
    (enumeration.nodup_orderedValues.filter _)]
  simp

/-- Express an exact predicate-subtype cardinality in the numeric coordinate
of the enumeration's canonical equivalence.  This is the bridge used by
independent interval certificates. -/
theorem subtype_card_eq_sum_fin
    (enumeration : FinEnum α) (predicate : α → Prop)
    (decidePredicate : ∀ value, Decidable (predicate value)) :
    (Enumeration.subtype enumeration predicate decidePredicate).card =
      ∑ index : Fin enumeration.card,
        if predicate (enumeration.equiv.symm index) then 1 else 0 := by
  rw [Enumeration.subtype_card_eq_filter]
  letI : Fintype α := @FinEnum.instFintype α enumeration
  letI : DecidablePred predicate := decidePredicate
  calc
    ((Finset.univ.filter predicate).card : Nat) =
        ∑ value : α, if predicate value then 1 else 0 := by
      classical
      simp_rw [Finset.card_eq_sum_ones]
      rw [Finset.sum_filter]
    _ = ∑ index : Fin enumeration.card,
          if predicate (enumeration.equiv.symm index) then 1 else 0 := by
      exact Fintype.sum_equiv enumeration.equiv _ _ (fun value => by
        simp)

/-- Variant with a caller-supplied exact numeric encoding.  The framework
owns all subtype/Fintype bookkeeping; applications provide only the finite
encoding already natural for their local table. -/
theorem subtype_card_eq_sum_equiv {count : Nat}
    (enumeration : FinEnum α) (predicate : α → Prop)
    (decidePredicate : ∀ value, Decidable (predicate value))
    (encoding : α ≃ Fin count) :
    (Enumeration.subtype enumeration predicate decidePredicate).card =
      ∑ index : Fin count,
        if predicate (encoding.symm index) then 1 else 0 := by
  rw [Enumeration.subtype_card_eq_filter]
  letI : Fintype α := @FinEnum.instFintype α enumeration
  letI : DecidablePred predicate := decidePredicate
  calc
    ((Finset.univ.filter predicate).card : Nat) =
        ∑ value : α, if predicate value then 1 else 0 := by
      classical
      simp_rw [Finset.card_eq_sum_ones]
      rw [Finset.sum_filter]
    _ = ∑ index : Fin count,
          if predicate (encoding.symm index) then 1 else 0 := by
      exact Fintype.sum_equiv encoding _ _ (fun value => by simp)

/-- Sum one fixed-width interval of a natural-indexed finite table. -/
def intervalSum (value : Nat → Nat) (start width : Nat) : Nat :=
  ∑ offset ∈ Finset.range width, value (start + offset)

/-- Partition an exact multiple-width prefix into independent fixed-width
intervals.  Applications may certify each interval separately and compose
the stored counts by rewriting this identity. -/
theorem sum_range_mul_eq_sum_intervalSum (value : Nat → Nat)
    (chunks width : Nat) :
    (∑ index ∈ Finset.range (chunks * width), value index) =
      ∑ chunk ∈ Finset.range chunks, intervalSum value (chunk * width) width := by
  induction chunks with
  | zero => simp
  | succ chunks ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      rw [Finset.sum_range_succ]
      simp [intervalSum, Nat.add_comm]

/-! ## Exact interval partitions

The following identities separate a finite sum into fixed-width pieces and a
single tail.  They are algebraic identities: in particular, their proofs do
not evaluate the entries of the table.  Applications can therefore prove the
small interval equalities in independent modules and use the composition
theorems at the end without reducing the whole finite carrier.
-/

/-- Split a natural-indexed finite prefix into fixed-width intervals and its
possibly shorter tail. -/
theorem sum_range_eq_chunkIntervals_add_tail (value : Nat → Nat)
    (total width : Nat) :
    (∑ index ∈ Finset.range total, value index) =
      (∑ chunk ∈ Finset.range (total / width),
        intervalSum value (chunk * width) width) +
      intervalSum value ((total / width) * width) (total % width) := by
  conv_lhs =>
    rw [← Nat.div_add_mod total width]
  rw [Nat.mul_comm width (total / width)]
  rw [Finset.sum_range_add]
  rw [sum_range_mul_eq_sum_intervalSum]
  rfl

/-- Extend a finite natural-valued family by zero.  This is framework-owned
bounded-index plumbing for independently checked interval files. -/
def finZeroExtension {total : Nat} (value : Fin total → Nat)
    (index : Nat) : Nat :=
  if inBounds : index < total then value ⟨index, inBounds⟩ else 0

@[simp] theorem finZeroExtension_val {total : Nat}
    (value : Fin total → Nat) (index : Fin total) :
    finZeroExtension value index.1 = value index := by
  simp [finZeroExtension]

/-- Finite-type form of `sum_range_eq_chunkIntervals_add_tail`.  The
framework zero-extends the finite summand, so independently generated
interval files can remain natural-indexed without manufacturing bounded
indices. -/
theorem finSum_eq_chunkIntervals_add_tail {total : Nat}
    (value : Fin total → Nat) (width : Nat) :
    (∑ index : Fin total, value index) =
      (∑ chunk ∈ Finset.range (total / width),
        intervalSum (finZeroExtension value) (chunk * width) width) +
      intervalSum (finZeroExtension value)
        ((total / width) * width) (total % width) := by
  calc
    (∑ index : Fin total, value index) =
        ∑ index : Fin total, finZeroExtension value index.1 := by simp
    _ =
        (∑ chunk ∈ Finset.range (total / width),
          intervalSum (finZeroExtension value) (chunk * width) width) +
        intervalSum (finZeroExtension value)
          ((total / width) * width) (total % width) := by
      rw [Fin.sum_univ_eq_sum_range]
      exact sum_range_eq_chunkIntervals_add_tail
        (finZeroExtension value) total width

/-- Compose independently certified interval totals.  Only each displayed
interval and the final tail have to be checked by the caller. -/
theorem finSum_eq_certifiedIntervals_add_tail
    {total : Nat} (value : Fin total → Nat) (certified : Nat → Nat)
    (width certifiedTail : Nat)
    (chunkExact : ∀ chunk ∈ Finset.range (total / width),
      intervalSum (finZeroExtension value) (chunk * width) width =
        certified chunk)
    (tailExact :
      intervalSum (finZeroExtension value)
          ((total / width) * width) (total % width) = certifiedTail) :
    (∑ index : Fin total, value index) =
      (∑ chunk ∈ Finset.range (total / width), certified chunk) +
        certifiedTail := by
  calc
    (∑ index : Fin total, value index) =
        (∑ chunk ∈ Finset.range (total / width),
          intervalSum (finZeroExtension value) (chunk * width) width) +
        intervalSum (finZeroExtension value)
          ((total / width) * width) (total % width) :=
      finSum_eq_chunkIntervals_add_tail value width
    _ = (∑ chunk ∈ Finset.range (total / width), certified chunk) +
          certifiedTail :=
      congrArg₂ Nat.add (Finset.sum_congr rfl chunkExact) tailExact

/-! ## Exact rectangle partitions -/

/-- Sum one finite rectangle of a doubly natural-indexed table. -/
def rectangleSum (value : Nat → Nat → Nat)
    (rowStart rowWidth columnStart columnWidth : Nat) : Nat :=
  intervalSum
    (fun row => intervalSum (value row) columnStart columnWidth)
    rowStart rowWidth

/-- Exchange a fixed row interval with a finite family of fixed column
intervals.  This is the small Fubini step used by the rectangle partition. -/
theorem intervalSum_chunkIntervals_eq_sum_rectangles
    (value : Nat → Nat → Nat)
    (rowStart rowWidth columnChunks columnWidth : Nat) :
    intervalSum
        (fun row => ∑ columnChunk ∈ Finset.range columnChunks,
          intervalSum (value row) (columnChunk * columnWidth) columnWidth)
        rowStart rowWidth =
      ∑ columnChunk ∈ Finset.range columnChunks,
        rectangleSum value rowStart rowWidth
          (columnChunk * columnWidth) columnWidth := by
  simp only [intervalSum, rectangleSum]
  rw [Finset.sum_comm]

/-- Split both coordinates of a finite rectangle into fixed-size rectangles,
then retain the bottom strip, right strip, and bottom-right corner exactly.
No table entry is evaluated by this proof. -/
theorem sum_range_sum_range_eq_chunkRectangles_add_tails
    (value : Nat → Nat → Nat)
    (rows columns rowWidth columnWidth : Nat) :
    (∑ row ∈ Finset.range rows,
      ∑ column ∈ Finset.range columns, value row column) =
      ((∑ rowChunk ∈ Finset.range (rows / rowWidth),
          ∑ columnChunk ∈ Finset.range (columns / columnWidth),
            rectangleSum value
              (rowChunk * rowWidth) rowWidth
              (columnChunk * columnWidth) columnWidth) +
        (∑ columnChunk ∈ Finset.range (columns / columnWidth),
          rectangleSum value
            ((rows / rowWidth) * rowWidth) (rows % rowWidth)
            (columnChunk * columnWidth) columnWidth)) +
      ((∑ rowChunk ∈ Finset.range (rows / rowWidth),
          rectangleSum value
            (rowChunk * rowWidth) rowWidth
            ((columns / columnWidth) * columnWidth) (columns % columnWidth)) +
        rectangleSum value
          ((rows / rowWidth) * rowWidth) (rows % rowWidth)
          ((columns / columnWidth) * columnWidth) (columns % columnWidth)) := by
  calc
    (∑ row ∈ Finset.range rows,
        ∑ column ∈ Finset.range columns, value row column) =
        (∑ row ∈ Finset.range rows,
          ((∑ columnChunk ∈ Finset.range (columns / columnWidth),
              intervalSum (value row)
                (columnChunk * columnWidth) columnWidth) +
            intervalSum (value row)
              ((columns / columnWidth) * columnWidth)
              (columns % columnWidth))) := by
      apply Finset.sum_congr rfl
      intro row _row_mem
      exact sum_range_eq_chunkIntervals_add_tail
        (value row) columns columnWidth
    _ =
        (∑ row ∈ Finset.range rows,
          ∑ columnChunk ∈ Finset.range (columns / columnWidth),
            intervalSum (value row)
              (columnChunk * columnWidth) columnWidth) +
        (∑ row ∈ Finset.range rows,
          intervalSum (value row)
            ((columns / columnWidth) * columnWidth)
            (columns % columnWidth)) := by
      rw [Finset.sum_add_distrib]
    _ =
        (((∑ rowChunk ∈ Finset.range (rows / rowWidth),
            intervalSum
              (fun row =>
                ∑ columnChunk ∈ Finset.range (columns / columnWidth),
                  intervalSum (value row)
                    (columnChunk * columnWidth) columnWidth)
              (rowChunk * rowWidth) rowWidth) +
          intervalSum
            (fun row =>
              ∑ columnChunk ∈ Finset.range (columns / columnWidth),
                intervalSum (value row)
                  (columnChunk * columnWidth) columnWidth)
            ((rows / rowWidth) * rowWidth) (rows % rowWidth)) +
        ((∑ rowChunk ∈ Finset.range (rows / rowWidth),
            intervalSum
              (fun row => intervalSum (value row)
                ((columns / columnWidth) * columnWidth)
                (columns % columnWidth))
              (rowChunk * rowWidth) rowWidth) +
          intervalSum
            (fun row => intervalSum (value row)
              ((columns / columnWidth) * columnWidth)
              (columns % columnWidth))
            ((rows / rowWidth) * rowWidth) (rows % rowWidth))) := by
      exact congrArg₂ Nat.add
        (sum_range_eq_chunkIntervals_add_tail
          (fun row =>
            ∑ columnChunk ∈ Finset.range (columns / columnWidth),
              intervalSum (value row)
                (columnChunk * columnWidth) columnWidth)
          rows rowWidth)
        (sum_range_eq_chunkIntervals_add_tail
          (fun row => intervalSum (value row)
            ((columns / columnWidth) * columnWidth)
            (columns % columnWidth))
          rows rowWidth)
    _ =
        ((∑ rowChunk ∈ Finset.range (rows / rowWidth),
            ∑ columnChunk ∈ Finset.range (columns / columnWidth),
              rectangleSum value
                (rowChunk * rowWidth) rowWidth
                (columnChunk * columnWidth) columnWidth) +
          (∑ columnChunk ∈ Finset.range (columns / columnWidth),
            rectangleSum value
              ((rows / rowWidth) * rowWidth) (rows % rowWidth)
              (columnChunk * columnWidth) columnWidth)) +
        ((∑ rowChunk ∈ Finset.range (rows / rowWidth),
            rectangleSum value
              (rowChunk * rowWidth) rowWidth
              ((columns / columnWidth) * columnWidth) (columns % columnWidth)) +
          rectangleSum value
            ((rows / rowWidth) * rowWidth) (rows % rowWidth)
            ((columns / columnWidth) * columnWidth) (columns % columnWidth)) := by
      simp_rw [intervalSum_chunkIntervals_eq_sum_rectangles]
      rfl

/-- Nested `Fin`/Fubini form for a natural-indexed table. -/
theorem finDoubleSumOfNat_eq_chunkRectangles_add_tails
    (value : Nat → Nat → Nat)
    (rows columns rowWidth columnWidth : Nat) :
    (∑ row : Fin rows, ∑ column : Fin columns, value row.1 column.1) =
      ((∑ rowChunk ∈ Finset.range (rows / rowWidth),
          ∑ columnChunk ∈ Finset.range (columns / columnWidth),
            rectangleSum value
              (rowChunk * rowWidth) rowWidth
              (columnChunk * columnWidth) columnWidth) +
        (∑ columnChunk ∈ Finset.range (columns / columnWidth),
          rectangleSum value
            ((rows / rowWidth) * rowWidth) (rows % rowWidth)
            (columnChunk * columnWidth) columnWidth)) +
      ((∑ rowChunk ∈ Finset.range (rows / rowWidth),
          rectangleSum value
            (rowChunk * rowWidth) rowWidth
            ((columns / columnWidth) * columnWidth) (columns % columnWidth)) +
        rectangleSum value
          ((rows / rowWidth) * rowWidth) (rows % rowWidth)
          ((columns / columnWidth) * columnWidth) (columns % columnWidth)) := by
  have inner (row : Fin rows) :
      (∑ column : Fin columns, value row.1 column.1) =
        ∑ column ∈ Finset.range columns, value row.1 column := by
    exact Fin.sum_univ_eq_sum_range
      (fun column => value row.1 column) columns
  calc
    (∑ row : Fin rows, ∑ column : Fin columns, value row.1 column.1) =
        ∑ row : Fin rows,
          ∑ column ∈ Finset.range columns, value row.1 column := by
      exact Finset.sum_congr rfl fun row _ => inner row
    _ = ∑ row ∈ Finset.range rows,
          ∑ column ∈ Finset.range columns, value row column := by
      exact Fin.sum_univ_eq_sum_range
        (fun row => ∑ column ∈ Finset.range columns,
          value row column) rows
    _ = _ := sum_range_sum_range_eq_chunkRectangles_add_tails
      value rows columns rowWidth columnWidth

/-- Compose independently certified full rectangles, boundary strips, and
the corner into the exact double finite sum. -/
theorem finDoubleSumOfNat_eq_certifiedRectangles_add_tails
    (value : Nat → Nat → Nat)
    (rows columns rowWidth columnWidth : Nat)
    (certifiedRectangle : Nat → Nat → Nat)
    (certifiedBottom certifiedRight : Nat → Nat)
    (certifiedCorner : Nat)
    (rectangleExact :
      ∀ rowChunk ∈ Finset.range (rows / rowWidth),
        ∀ columnChunk ∈ Finset.range (columns / columnWidth),
          rectangleSum value
              (rowChunk * rowWidth) rowWidth
              (columnChunk * columnWidth) columnWidth =
            certifiedRectangle rowChunk columnChunk)
    (bottomExact :
      ∀ columnChunk ∈ Finset.range (columns / columnWidth),
        rectangleSum value
            ((rows / rowWidth) * rowWidth) (rows % rowWidth)
            (columnChunk * columnWidth) columnWidth =
          certifiedBottom columnChunk)
    (rightExact :
      ∀ rowChunk ∈ Finset.range (rows / rowWidth),
        rectangleSum value
            (rowChunk * rowWidth) rowWidth
            ((columns / columnWidth) * columnWidth) (columns % columnWidth) =
          certifiedRight rowChunk)
    (cornerExact :
      rectangleSum value
          ((rows / rowWidth) * rowWidth) (rows % rowWidth)
          ((columns / columnWidth) * columnWidth) (columns % columnWidth) =
        certifiedCorner) :
    (∑ row : Fin rows, ∑ column : Fin columns, value row.1 column.1) =
      ((∑ rowChunk ∈ Finset.range (rows / rowWidth),
          ∑ columnChunk ∈ Finset.range (columns / columnWidth),
            certifiedRectangle rowChunk columnChunk) +
        (∑ columnChunk ∈ Finset.range (columns / columnWidth),
          certifiedBottom columnChunk)) +
      ((∑ rowChunk ∈ Finset.range (rows / rowWidth),
          certifiedRight rowChunk) + certifiedCorner) := by
  have rectangles :
      (∑ rowChunk ∈ Finset.range (rows / rowWidth),
        ∑ columnChunk ∈ Finset.range (columns / columnWidth),
          rectangleSum value
            (rowChunk * rowWidth) rowWidth
            (columnChunk * columnWidth) columnWidth) =
        ∑ rowChunk ∈ Finset.range (rows / rowWidth),
          ∑ columnChunk ∈ Finset.range (columns / columnWidth),
            certifiedRectangle rowChunk columnChunk := by
    apply Finset.sum_congr rfl
    intro rowChunk rowChunk_mem
    exact Finset.sum_congr rfl (rectangleExact rowChunk rowChunk_mem)
  have bottoms :
      (∑ columnChunk ∈ Finset.range (columns / columnWidth),
        rectangleSum value
          ((rows / rowWidth) * rowWidth) (rows % rowWidth)
          (columnChunk * columnWidth) columnWidth) =
        ∑ columnChunk ∈ Finset.range (columns / columnWidth),
          certifiedBottom columnChunk :=
    Finset.sum_congr rfl bottomExact
  have rights :
      (∑ rowChunk ∈ Finset.range (rows / rowWidth),
        rectangleSum value
          (rowChunk * rowWidth) rowWidth
          ((columns / columnWidth) * columnWidth) (columns % columnWidth)) =
        ∑ rowChunk ∈ Finset.range (rows / rowWidth),
          certifiedRight rowChunk :=
    Finset.sum_congr rfl rightExact
  calc
    (∑ row : Fin rows, ∑ column : Fin columns, value row.1 column.1) =
        ((∑ rowChunk ∈ Finset.range (rows / rowWidth),
            ∑ columnChunk ∈ Finset.range (columns / columnWidth),
              rectangleSum value
                (rowChunk * rowWidth) rowWidth
                (columnChunk * columnWidth) columnWidth) +
          (∑ columnChunk ∈ Finset.range (columns / columnWidth),
            rectangleSum value
              ((rows / rowWidth) * rowWidth) (rows % rowWidth)
              (columnChunk * columnWidth) columnWidth)) +
        ((∑ rowChunk ∈ Finset.range (rows / rowWidth),
            rectangleSum value
              (rowChunk * rowWidth) rowWidth
              ((columns / columnWidth) * columnWidth) (columns % columnWidth)) +
          rectangleSum value
            ((rows / rowWidth) * rowWidth) (rows % rowWidth)
            ((columns / columnWidth) * columnWidth) (columns % columnWidth)) :=
      finDoubleSumOfNat_eq_chunkRectangles_add_tails
        value rows columns rowWidth columnWidth
    _ =
        ((∑ rowChunk ∈ Finset.range (rows / rowWidth),
            ∑ columnChunk ∈ Finset.range (columns / columnWidth),
              certifiedRectangle rowChunk columnChunk) +
          (∑ columnChunk ∈ Finset.range (columns / columnWidth),
            certifiedBottom columnChunk)) +
        ((∑ rowChunk ∈ Finset.range (rows / rowWidth),
            certifiedRight rowChunk) + certifiedCorner) :=
      congrArg₂ Nat.add
        (congrArg₂ Nat.add rectangles bottoms)
        (congrArg₂ Nat.add rights cornerExact)

/-! ## Bounded-index rectangle interface -/

/-- Extend a doubly finite natural-valued family by zero in each coordinate.
Applications state their summands on the exact finite carriers; the framework
owns all conversion to the natural indices used by `rectangleSum`. -/
def finDoubleZeroExtension {rows columns : Nat}
    (value : Fin rows → Fin columns → Nat)
    (row column : Nat) : Nat :=
  if rowInBounds : row < rows then
    if columnInBounds : column < columns then
      value ⟨row, rowInBounds⟩ ⟨column, columnInBounds⟩
    else 0
  else 0

@[simp] theorem finDoubleZeroExtension_val {rows columns : Nat}
    (value : Fin rows → Fin columns → Nat)
    (row : Fin rows) (column : Fin columns) :
    finDoubleZeroExtension value row.1 column.1 = value row column := by
  simp [finDoubleZeroExtension]

/-- Exact rectangle partition for an arbitrary doubly finite summand. -/
theorem finDoubleSum_eq_chunkRectangles_add_tails
    {rows columns : Nat} (value : Fin rows → Fin columns → Nat)
    (rowWidth columnWidth : Nat) :
    (∑ row : Fin rows, ∑ column : Fin columns, value row column) =
      ((∑ rowChunk ∈ Finset.range (rows / rowWidth),
          ∑ columnChunk ∈ Finset.range (columns / columnWidth),
            rectangleSum (finDoubleZeroExtension value)
              (rowChunk * rowWidth) rowWidth
              (columnChunk * columnWidth) columnWidth) +
        (∑ columnChunk ∈ Finset.range (columns / columnWidth),
          rectangleSum (finDoubleZeroExtension value)
            ((rows / rowWidth) * rowWidth) (rows % rowWidth)
            (columnChunk * columnWidth) columnWidth)) +
      ((∑ rowChunk ∈ Finset.range (rows / rowWidth),
          rectangleSum (finDoubleZeroExtension value)
            (rowChunk * rowWidth) rowWidth
            ((columns / columnWidth) * columnWidth) (columns % columnWidth)) +
        rectangleSum (finDoubleZeroExtension value)
          ((rows / rowWidth) * rowWidth) (rows % rowWidth)
          ((columns / columnWidth) * columnWidth) (columns % columnWidth)) := by
  simpa only [finDoubleZeroExtension_val] using
    finDoubleSumOfNat_eq_chunkRectangles_add_tails
      (finDoubleZeroExtension value) rows columns rowWidth columnWidth

/-- Compose independently certified rectangle subtotals for an arbitrary
doubly finite summand. -/
theorem finDoubleSum_eq_certifiedRectangles_add_tails
    {rows columns : Nat} (value : Fin rows → Fin columns → Nat)
    (rowWidth columnWidth : Nat)
    (certifiedRectangle : Nat → Nat → Nat)
    (certifiedBottom certifiedRight : Nat → Nat)
    (certifiedCorner : Nat)
    (rectangleExact :
      ∀ rowChunk ∈ Finset.range (rows / rowWidth),
        ∀ columnChunk ∈ Finset.range (columns / columnWidth),
          rectangleSum (finDoubleZeroExtension value)
              (rowChunk * rowWidth) rowWidth
              (columnChunk * columnWidth) columnWidth =
            certifiedRectangle rowChunk columnChunk)
    (bottomExact :
      ∀ columnChunk ∈ Finset.range (columns / columnWidth),
        rectangleSum (finDoubleZeroExtension value)
            ((rows / rowWidth) * rowWidth) (rows % rowWidth)
            (columnChunk * columnWidth) columnWidth =
          certifiedBottom columnChunk)
    (rightExact :
      ∀ rowChunk ∈ Finset.range (rows / rowWidth),
        rectangleSum (finDoubleZeroExtension value)
            (rowChunk * rowWidth) rowWidth
            ((columns / columnWidth) * columnWidth) (columns % columnWidth) =
          certifiedRight rowChunk)
    (cornerExact :
      rectangleSum (finDoubleZeroExtension value)
          ((rows / rowWidth) * rowWidth) (rows % rowWidth)
          ((columns / columnWidth) * columnWidth) (columns % columnWidth) =
        certifiedCorner) :
    (∑ row : Fin rows, ∑ column : Fin columns, value row column) =
      ((∑ rowChunk ∈ Finset.range (rows / rowWidth),
          ∑ columnChunk ∈ Finset.range (columns / columnWidth),
            certifiedRectangle rowChunk columnChunk) +
        (∑ columnChunk ∈ Finset.range (columns / columnWidth),
          certifiedBottom columnChunk)) +
      ((∑ rowChunk ∈ Finset.range (rows / rowWidth),
          certifiedRight rowChunk) + certifiedCorner) := by
  simpa only [finDoubleZeroExtension_val] using
    finDoubleSumOfNat_eq_certifiedRectangles_add_tails
      (finDoubleZeroExtension value) rows columns rowWidth columnWidth
      certifiedRectangle certifiedBottom certifiedRight certifiedCorner
      rectangleExact bottomExact rightExact cornerExact

end StructuralExhaustion.Core.ChunkedFiniteCount
