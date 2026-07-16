# Adversarial pre-review contract: node [164]

## Scope

This is a read-only acceptance contract for the future long-prefix semantic
consumer at node `[164]`.  It changes no Lean or synchronized artifact.

Node `[164]` belongs exclusively to the node-`[161]` long constructor through
node `[163]`.  It must not consume node `[170]`, `[173]`, `[174]`, or `[175]`
application payloads.  Reusable Core or Graph refinement machinery developed
for node `[175]` may be imported only as theorem-independent infrastructure.

## Exact incoming provenance

The public runner must dependently retain:

- `fork`, `quiet`, and `long : P13SameWindowLongOutput fork quiet`;
- the actual `prefix : P13SameWindowLongSupportPrefix fork quiet long`;
- equality `prefix = runP13SameWindowLongSupportPrefix fork quiet long`, or a
  result obtained by matching that actual run.

From that exact source it may use only:

- the identical corridor return support
  `((p13SelectedWindowCorridorProducer ctx).ambientReturn quiet.stub).support`;
- the strict inequality `Qbase < support.length`;
- the order-preserving embedding of `Fin (Qbase + 1)` into the literal support;
- the exact base/overflow and prefix/after-prefix classifiers.

An arbitrary `LongFiniteSupportHandoff.Source`, a caller-selected list of
positions, or a fresh long-support proof is not an acceptable predecessor.

The generic node-`[163]` handoff stores lengths and position indices, not the
vertices at those indices.  Node `[164]` must therefore define and prove the
index-to-literal-support-entry map using the exact corridor list retained by
`quiet`; it may not treat `Fin (Qbase + 1)` as semantic graph data by itself.

## Non-vacuous state-label contract

Every forced prefix occurrence must be a record containing at least:

- its exact `PrefixPosition` and embedded full-support position;
- the literal corridor support entry at that position;
- the graph-derived local interface/cut rooted at that entry;
- all local connector, boundary, and context data used to evaluate its label;
- proofs that every datum comes from the same selected graph and corridor.

The coarse exact-type label must be graph-derived and have a proved finite
enumeration of cardinality at most

```text
Qbase = 4^2 * 13^2 * 2^13.
```

The intended safe pattern is:

- the exact type is the sound D1--D3 coarse state of the occurrence;
- D4--D7 compatible-context behavior is the separate finite response map used
  by CT8 after a coarse type repeats.

Putting D4--D7 coordinates into the exact-type alphabet is allowed only if the
new alphabet is still proved to have cardinality at most `Qbase`.  Finiteness
alone is insufficient: increasing the alphabet invalidates the
`Qbase + 1` pigeonhole step.

The following labels are vacuous and fail review:

- the position index itself;
- `Unit`, `Fin 0`, or a constant Boolean without a completeness theorem;
- a caller-supplied arbitrary `State` or response function;
- a hash/code without injectivity or exact decoding to the authored state;
- a `DeclaredLocalSemantics` value whose coordinates are not proved complete
  for the local D4--D7 compatible contexts.

If generic node-`[175]` refinement APIs are reused, node `[164]` must construct
their local graph inputs independently from the long corridor.  A short-branch
node-`[175]` source, row, connector, or theorem specialized to node `[174]`
cannot cross the mutually exclusive branch boundary.

## Exact CT8 contract

The CT8 state type should retain occurrence identity—normally the prefix
position plus its local graph record.  `exactType` projects the finite coarse
label; it must not include the position.  This lets CT8 detect equal types at
two distinct occurrences while preserving both positions for later splicing.

The CT8 sequence must be exactly the declared-order list of all
`Qbase + 1` forced prefix occurrences.  Prove:

- sequence length is `Qbase + 1`;
- its occurrence positions are duplicate-free and exhaust the prefix;
- every entry maps to the exact literal corridor support position;
- `exactTypes.card <= Qbase`.

Consequently CT8's `noRepetition` terminal must be contradicted by the exact
length/cardinality theorem, not ignored.

For a repeated coarse type, CT8 additionally requires:

- one common finite `ResponseContext` enumeration derived from actual local
  compatible contexts;
- a response evaluator proved complete for the authored D4--D7/target tests;
- a graph-defined `remove first second : SmallerObject` using the two retained
  positions in correct order.

The generic CT8 `SmallerObject` field proves rank decrease only.  Before an
equal-response branch closes by minimality, Graph/Erdős code must also produce
a `CertifiedReduction`: reduced baseline and target transport back to the
source graph.  Supplying an arbitrary rank-smaller object to `CT8.Input.remove`
is semantic injection.

All three CT8 terminals must be handled:

1. `noRepetition`: impossible by `Qbase + 1 > exactTypes.card`;
2. `removal`: retain the exact ordered pair and response equality, then close
   only through the certified reduction/minimality theorem;
3. `separation`: retain the first actual distinguishing response context and
   route it to a typed CT3, CT7, or CT10 consumer.

## Acceptable node-[164] output boundary

A minimum branch-total result is:

```text
certifiedRemoval
  exact repeated positions
  all finite-context responses equal
  certified smaller reduction

distinguishingContext
  exact repeated positions
  first derived compatible context
  proved response difference

labelRefinementResidual
  exact occurrence/local interface
  first missing or incomplete semantic label
  typed CT10 consumer
```

The third branch is needed if local D1--D7 semantics are not unconditionally
derivable.  A green node may not accept label completeness as an author field.
If the implementation proves label construction total, it may eliminate this
branch by theorem.

Node `[164]` may stop at a typed separating/refinement residual.  It need not
prove density or the later cold-family aggregate.  It may close the equal case
only when the certified reduction is complete.

## Allowed local computation

Executable scans may range over only:

- the exact `Qbase + 1` prefix positions;
- the literal corridor support entries at those positions;
- each occurrence's explicitly constructed bounded local support/incidences;
- one derived finite exact-type code per occurrence;
- derived compatible response contexts for the retained repeated pair.

The long branch supplies a support sequence, not a family of paths or graph
states.  Any connector/path required for a label must be computed from one
declared local input and retained; do not enumerate candidate paths.

Forbidden executable universes include:

- all `State` values or all exact types merely because a `FinEnum` exists;
- all graphs, subgraphs, vertex subsets, paths, returns, cuts, or supports;
- all Boolean response functions, truth tables, or coordinate subsets;
- all D4--D7 alphabets or all compatible contexts;
- a product of one label/reconstruction choice per prefix occurrence;
- any node-`[174]` observed-row schedule or node-`[175]` P13 payload.

The finite alphabet may be used through cardinality in the pigeonhole proof;
it must not be materialized as the executable search universe.

## Practical collision search and work ledger

Here `Qbase` is about twenty-two million, so an observed-list quadratic scan is
formally local but not practically acceptable without an explicit
justification.  Prefer a one-pass observed-code dictionary keyed by a proved
exact code.  The dictionary must store only codes already encountered; a
preallocated table over all `Qbase` states counts as ambient state-universe
materialization and fails this contract.

Let:

- `m = Qbase + 1` be the actual prefix length;
- `L_i` be local label-construction work at occurrence `i`;
- `d` be the cost of one observed-code dictionary operation;
- `r` be the number of derived response contexts for the retained pair;
- `R` be graph work for the proposed reduction and its proofs.

The visible ledger should have a form such as

```text
sum_i L_i + m*d + r + R.
```

If the existing list-based collision classifier is used, the implementation
must honestly record its `O(m^2)` equality work and explain why it is practical
at this concrete threshold; otherwise it is not PASS-ready.  Work must also
charge list/finset membership comparisons and local connector construction.

No executable work term may contain a graph/subset/path/Boolean-function
universe or an enumeration of the full state alphabet.  Early stopping is an
upper bound unless an exact executed comparison counter is returned.

## Forbidden semantic promotions

Reject any implementation asserting, without new graph theorems, that:

- long support length alone supplies state labels;
- two positions have a common boundary interface;
- equal D1--D3 labels imply equal D4--D7/full target response;
- a repeated label yields a removable segment;
- deleting/splicing the intervening corridor preserves baseline or transports
  a target;
- the prefix positions are CT17 survivors, offsets, orbit values, or
  compatibility witnesses;
- this long branch joins nodes `[170]`--`[175]`;
- a Boolean product, cold-family membership, target closure, termination,
  bounded-germ conclusion, or density estimate follows.

The selected node-`[159]` window and its corridor are exact, but they are not
automatically the manuscript's global selected cold subfamily.

## Framework ownership

- **Core:** observed-code dictionary/collision logic; generic first-missing
  semantic refinement; finite response comparison.  Reuse node-`[175]` generic
  APIs here if their types are branch-neutral.
- **Graph:** map literal long-prefix positions to graph entries; construct the
  local interfaces and sound D1--D7 response semantics; construct and certify
  the splice/removal reduction.
- **CT8:** own repeated exact-type search and finite response comparison only
  after all capability data are derived.
- **CT10/Routes:** own missing/incomplete label refinement and the first
  distinguishing semantic class when the coarse alphabet is insufficient.
- **Core certified reduction/minimality:** own closure of the equal-response
  removal branch.
- **Erdős adapter:** retain the actual node-`[163]` output, instantiate
  `PowerOfTwoLength` and authored local predicates, and compose the generic
  stages.  It must contain no caller-supplied state labels, response equality,
  or reduction correctness.

## Required transfer and tests

### Provenance and branch-separation tests

- The runner cannot be called without an exact node-`[163]` result/equality.
- Every semantic occurrence exposes its prefix index and exact corridor entry.
- Imports/types do not mention node-`[170]`, `[173]`, `[174]`, or P13
  node-`[175]` sources.
- A type-level regression demonstrates that short first-transition data cannot
  inhabit the long-prefix input.

### Label and pigeonhole tests

- A small non-Erdős fixture constructs nonconstant graph-derived labels.
- Label-code injectivity/decoding and alphabet-cardinality theorems are tested.
- Prefix enumeration is exact, ordered, duplicate-free, and has length
  `Qbase + 1` in the P13 adapter.
- The no-repetition outcome is formally impossible from the exact card bound.
- No test succeeds with a constant/empty label unless the underlying local
  semantics genuinely has that complete one-class behavior.

### CT8 consumer tests

- Equal-response fixture returns the exact pair and a real certified smaller
  reduction; minimality closure uses baseline and target transport.
- Distinguishing fixture returns the first actual context and typed route.
- Missing-label fixture returns the exact first occurrence and CT10 residual.
- Exhaustiveness, validity, trace, and determinism are proved for every generic
  runner used.

### Locality, work, transfer, and trust

- Instrumentation depends only on prefix/local-interface/context schedules.
- Source scan rejects `Fintype.elems State`, powersets, Boolean-function
  tables, path families, and ambient graph/subset enumeration.
- A theorem-independent non-Erdős example exercises equal, distinguishing,
  and missing-refinement branches using the same reusable API.
- Focused Core/Graph/Routes/transfer/P13 builds and affected umbrella tests
  pass.
- `#print axioms` reports only standard Lean axioms and the repository's
  allowed external theorem set.
- No `sorry`, `admit`, unsafe shortcut, opaque native oracle, or author field
  carrying semantic correctness appears.

## Green decision rule

Node `[164]` is green only when `Qbase + 1` literal long-prefix occurrences
receive sound, non-vacuous graph labels; the `Qbase` pigeonhole theorem is
valid for that exact alphabet; and the repeated pair is routed through full
finite response comparison to either a certified removal or a typed
distinguishing/refinement consumer.  Length plus an arbitrary label function
is not a proof.
