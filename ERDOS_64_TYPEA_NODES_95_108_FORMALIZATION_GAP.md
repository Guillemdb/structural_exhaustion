# Type-A nodes [95]–[108]: exact remaining formalization gap

This note concerns the Lean translation of
`lem:typeA-unpeeled-visible-routing` through
`lem:typeA-high-degree-handoff` in
`proofs/erdos_64_eg/erdos_64_proof.tex`.  It does not assert that the
manuscript statement is false.

## Implemented exact pieces

- The existing `TypeAReceiverEntryChannels.spectral_pressure` theorem, now
  exposed as `TypeANodes107To108Handoff.node95_exit1_closed`, proves that each
  actual stored connector/channel return cannot have Mersenne length.  This is
  the target-avoiding closure of original exit (1).
- `Graph.TypeADeclaredContinuationCoordinate.Family.classify` scans one finite
  supplied same-fibre coordinate family and returns either exact connector
  coincidence or an actual first separator.  It compares only the stored
  connector words.
- `Graph.TypeASeparatorHandoff` turns the two sides of an actual first
  separator into literal simple ambient arms.  It proves first-entry into the
  counted core and avoidance of the separator center from the stored simple
  connector paths.
- `TypeANodes107To108Handoff.VerifiedNode107Residual.node108` constructs a
  genuine `TypeBEntryRouting.Exit7Handoff`.  Its source is the identical
  node-[61] negative support, its center and arms are the actual separator
  data, and its semantic fields are exactly the surviving node-[107]
  conclusions.  It creates no additional diagram outcome.

## First missing predecessor producer

`TypeANode93VisibleFamily.VerifiedNode93Residual` now gives the correct typed
yes-payload used by node [95]: four *unpeeled visible routed loads through one
completion port*, together with their receiver-entry returns and declared
response coordinates.  Its `firstFour` projection and continuation-family
classifier are kernel proved.

The payload itself is not graph-owned yet.  Its `schedule` field is a supplied
`Graph.TypeAFourVisibleContinuation.Schedule`; in particular, the schedule's
entry type, load map, unpeeled predicate, visibility predicate, response
labels, declared supports, values, and boundary-degree fibre are all supplied
by the caller.  `TypeANode89SaturationDecision.run` computes the first actual
saturated receiver and its exact load threshold, but no theorem converts that
receiver fibre into the complete finite family of actual visible-return
coordinates required by node [93].

This conversion cannot be replaced by choosing one bridgelessness return per
completion port.  A routed load is visible when its canonical trace is carried
by some receiver-entry channel through that port; one selected return may miss
another actual visible return.  Nor can a schedule be indexed only by ports:
several load/return occurrences may use the same port, and node [107] must
preserve those distinct occurrences through its first-separator computation.

Consequently there is not yet a dependency-ready graph-owned family on which
to execute the original sequential tests at nodes [95], [97], and [99].
Supplying an arbitrary four-element family, filtering a caller-provided return
list, or selecting one survivor per port would lose the exact unpeeled-load and
response-support provenance required by exit (4) and by the grouped node-[108]
accounting.

## Missing semantic types for cubic-switch absorption

The Lean graph layer can find a first connector separator, but the application
does not yet define proof-carrying representations of the three absorbed
outcomes:

1. a target-defective quotient in the canonical exit-(4) family, with declared
   support containing an unpeeled routed load;
2. a nontrivial target-complete response compression on the same boundary
   degree profile;
3. proper or global delocalization of that response equality.

These are the exact original exits (4), (5), and (6), not new cases.  Until
their types and the context-universality classifier are connected, Lean cannot
derive the manuscript implication

`ambient degree = 3 at the first separator -> exit (4), (5), or (6)`.

Therefore `center_high` and the five-clause pairwise fan-safety conclusion are
currently fields of the exact node-[107] survivor contract.  The node-[108]
constructor consumes those conclusions without strengthening them.  The next
paper-faithful implementation step is to build the graph-owned node-[93]
visible fibre from the exact saturated receiver/load schedule and the declared
response signature, then connect the exit-(4)/(5)/(6) response classifiers.
After that, these fields should be proved by the original cubic-switch and
fan-safety arguments.

## Why no complete `[107] -> [108]` schedule can yet be formed

A complete handoff schedule must retain each actual occurrence, not merely
each ambient center or completion port.  Its occurrence key has to contain at
least the canonical Type-A core identity, saturated receiver, port, four
unpeeled load/return coordinates, and selected first-separator occurrence.
None of those dependent occurrence records is emitted globally by the current
node-[89]/node-[93] code.

The local declaration

```text
VerifiedNode107Residual.node108 : one supplied node-[107] survivor -> one handoff
```

therefore cannot be lifted to a coverage theorem for all actual handoffs.  A
finite runner becomes implementable only after the graph-owned node-[93]
schedule exists and every earlier exit returns a typed result on the identical
occurrence.  The runner may then scan that produced occurrence list and only
that list; it must not enumerate paths, supports, contexts, or ambient vertex
subsets.

## Locality

All implemented computations inspect the supplied finite receiver/connector
data.  No graph universe, path universe, quotient universe, context universe,
or connected-subgraph universe is enumerated.
