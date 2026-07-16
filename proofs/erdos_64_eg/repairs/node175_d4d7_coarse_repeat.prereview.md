# Adversarial pre-review contract: node [175]

## Status and intended boundary

This is a read-only acceptance contract for the future node `[175]`
implementation.  It does not modify Lean, the manuscript, the diagram, or the
web export.

Node `[175]` is downstream only of the repaired node `[174]`.  Its purpose is
to consume the exact cyclic D1--D3 ledger split without upgrading coarse state
equality to full response equivalence.  It may either derive genuine D4--D7
semantics from the supplied local graph clauses or expose the exact coarse
repeat/reconstruction obstruction to a typed downstream consumer.

## Mandatory predecessor type

The public Erdős runner must require all of the following, dependently typed
on the same branch:

- `transition : P13SameWindowFirstTransitionBoundaryInput computed`;
- `source : P13SameWindowComponentD1D3LedgerSource transition`, retaining
  node `[173]` and `source.node173Exact`;
- equality to the actual node-`[174]` execution, or an output literally
  obtained by matching `transition.runD1D3Ledger source`.

Accepting an arbitrary `D1D3LedgerOutput`, rebuilding the source from node
`[170]`, or calling the generic graph ledger independently is a provenance
failure.

The two exact incoming constructors are:

1. `repeated repetition`, where `repetition.collision` supplies two distinct
   rows from the actual cyclic schedule and equality only of their
   `State (Fin 0)` values;
2. `bounded lengthLe`, where the same actual incident schedule has length at
   most `Qbase = 4^2 * 13^2 * 2^13`.

No third node-`[174]` branch exists.  The bounded branch does not carry a
repeat, while the repeated branch does not carry full response equivalence.

## Required branch reconstruction

### Repeated input

The consumer must retain, without reselection:

- the exact first and second stored rows selected by node `[174]`;
- their distinct schedule stubs and equal coarse D1--D3 states;
- both re-anchored node-`[170]` inputs, true cyclic successors, declared-order
  BFS connectors, and `MissingD4D7Reconstruction` witnesses;
- whether either selected row is the retained node-`[173]` anchor row.

An acceptable result is one of:

- a graph-derived common finite D4--D7 response interface for the two rows,
  followed by an exact response comparison; or
- a typed `CoarseRepeatResidual` carrying the unchanged pair and its missing
  D4--D7 obligation to a CT10/refinement producer.

If full responses are derived, equality may route to CT8 only after an actual
smaller-object/remove map and all compatible response contexts are proved.
A first distinguishing context must be returned as a CT3/CT7/CT10 residual;
it cannot be discarded.

### Bounded input

The consumer must retain the exact `lengthLe`; it may not infer that a coarse
repeat exists.  It must scan only the actual bounded row schedule and return
one of:

- a `ReconstructedFamily` giving graph-derived D4--D7 semantics for every
  observed row over one common finite coordinate/context interface; or
- the first exact observed row whose D4--D7 semantics cannot yet be derived,
  retaining its connector and `MissingD4D7Reconstruction`, routed as a typed
  CT10/refinement residual.

Merely defining an arbitrary `DeclaredLocalSemantics` is insufficient.  That
existing structure permits any finite coordinate type and Boolean map; an
implementation must prove that its coordinates and responses are complete
for the authored D4--D7 compatible-context tests.  In particular, choosing
`Fin 0`, `Unit`, or a constant response is not a reconstruction.

## Minimum branch-total output

The green result must distinguish at least these terminals:

```text
repeated + full responses equal
repeated + first response separator
repeated + D4--D7 reconstruction residual
bounded  + complete reconstructed observed family
bounded  + first D4--D7 reconstruction residual
```

Terminals may be combined through a reusable classifier, but none may be
proved impossible without a theorem from the exact incoming data.  Every
terminal must name its next typed consumer.  A result that simply returns the
node-`[174]` constructor unchanged is not sufficient progress.

Node `[175]` may stop at reconstruction/refinement.  It is not required to
prove a cycle, target closure, density, or termination.  If it invokes CT8,
all CT8 terminals must remain visible: no repetition, removal, and response
separation.

## Local-universe rule

Permitted executable schedules are only:

- node `[174]`'s stored incident rows;
- the two selected repeated rows;
- each row's already computed connector support and local incidences;
- an explicitly derived finite D4--D7 coordinate list;
- an explicitly derived finite compatible-context list.

Forbidden executable universes include:

- `Fintype.elems (State ...)` or any enumeration of all coarse/full states;
- all graphs, subgraphs, vertex subsets, paths, return paths, or support
  families;
- a Cartesian product of one semantic choice per row;
- all Boolean functions on coordinates or contexts;
- all possible D4--D7 alphabets;
- all cold subfamilies or all window assignments.

`Qbase` is a proof-level cardinal bound only.  It must not become a loop bound
over all possible states.  Path candidates must not be generated: each row
already owns one declared-order BFS path.

## Forbidden semantic overclaims

The following claims fail review unless separately proved from exact local
data:

- equal `State (Fin 0)` implies equal full D4--D7 response;
- a coarse collision is a CT8 removal certificate;
- bounded schedule length implies D4--D7 reconstructibility;
- `MissingD4D7Reconstruction` is a proof of nonexistence rather than a marker
  that semantics have not been supplied;
- one arbitrary finite response map is complete for compatible contexts;
- the short first-transition branch belongs to the selected cold family;
- any edge from this branch enters incompatible long-branch node `[164]`;
- a second connector, return iteration, periodicity, termination, CT3
  compression, Boolean realization, target closure, bounded-germ promotion,
  or density estimate.

The repeated branch may be called only a *coarse observed repeat* until the
missing response interface is proved.

## Framework ownership

- **Core:** reusable finite reconstruction/first-missing classifier and finite
  response comparison.  Extend existing Core logic rather than embedding an
  Erdős-specific search.
- **Graph:** derive the D4--D7 coordinate and compatible-context semantics from
  one exact connector, prove completeness, and retain local support/path
  provenance.  This is where graph-specific reconstruction belongs.
- **CT10/Routes:** own the finite missing-label/refinement residual and typed
  route.  A coarse finite label is CT10 recovery, not CT8 equivalence.
- **CT8:** may be instantiated only after exact types, a finite common response
  context list, an actual response evaluator, and a genuine smaller-object
  removal map exist.  Preserve its no-repetition/removal/separation outcomes.
- **Erdős adapter:** supply `PowerOfTwoLength`, exact node-`[174]` data, and
  thin graph instantiations only.  It must not accept D4--D7 completeness,
  response equality, or removability as author fields.

A non-Erdős transfer must exercise the same reconstruction/refinement or
response-comparison machinery without importing an Erdős declaration.

## Work ledger required for green

Let:

- `m` be the actual incident-row count;
- `W_i` be the local reconstruction work for row `i` on its stored connector;
- `q` be the derived D4--D7 coordinate count;
- `r` be the derived compatible-response-context count.

The implementation must state an exact or conservative visible ledger before
giving a polynomial bound.  Acceptable shapes include

```text
sum_i W_i + m*q                 -- reconstruct all observed rows
sum_i W_i + m*q + m^2*r        -- plus observed-pair response comparison
W_first + W_second + 2*q + r   -- consume one retained collision pair
```

The ledger must account for finite-set/list membership costs when they are not
constant-time.  It must not contain `|State|`, `2^q`, `2^r`, a path-family
cardinality, or a graph/subset-universe cardinality as executable work.
Early-stopping scans should be described as upper ledgers, not exact executed
comparison counts.

## Required tests and review evidence

### Provenance tests

- The node-`[175]` runner cannot be called without the dependent `source` and
  actual node-`[174]` result/equality.
- The retained anchor state is definitionally the node-`[173]` value.
- Both repeated rows are members of the exact node-`[174]` row list, distinct,
  and retain the same cyclic schedule.
- The bounded result retains the original `lengthLe` without manufacturing a
  repeat.

### Branch tests

- A repeated fixture reaches coarse-reconstruction residual when no full
  semantics are derivable.
- A full-semantics fixture reaches response equality/removal only with a proved
  remove map.
- A separator fixture returns the first actual distinguishing context.
- A bounded fixture reconstructs all actual rows or returns the first exact
  missing row.
- Every public result has an exhaustive-constructor theorem and every generic
  CT execution has validity and trace proofs.

### Locality and transfer tests

- A wraparound row uses the first schedule entry as the last entry's
  `List.next` successor.
- Instrumented work depends on actual row/coordinate/context schedules only.
- Source audit contains no `Fintype.elems State`, powerset, path-family, or
  Boolean-function enumeration.
- A theorem-independent non-Erdős example executes all materially different
  generic branches.

### Trust and synchronization gate

- Focused Core/Graph/Route/transfer/P13 builds pass, followed by affected
  umbrella packages and tests.
- `#print axioms` reports only standard Lean axioms and the repository's
  explicitly allowed external theorem set; no new application axiom.
- Placeholder scan finds no `sorry`, `admit`, unsafe proof shortcut, or
  caller-supplied semantic theorem.
- TeX, diagram row 16r, theorem index, web node, tests, README/log, and node
  count describe the exact implemented split.
- Node `[164]` remains disconnected and node `[175]` is not described as
  proving any later target/density conclusion.

## Pre-review decision rule

Node `[175]` is green only if it makes the missing D4--D7 interface explicit
and branch-total.  The shortest acceptable implementation is a local,
graph-derived reconstruction classifier with a typed first-missing residual;
the shortest unacceptable implementation is a wrapper that renames node
`[174]`'s coarse collision as full equivalence or supplies an arbitrary
`DeclaredLocalSemantics` field.
