# Red-team: first weighted-hot graph interpretation obligation

## Frozen contract

For one exact hot package, quantify only over states and coordinates belonging
to its duplicate-free supplied schedules.  Every `(state, coordinate)` must
produce a `P13Node160LocalGraphCompletion` for the identical selected window,
whose fifteen connector vertices equal the package's stored connector and
whose graph response at that coordinate equals `package.accepts`.

The coordinate index is necessary.  A node-[160] local completion stores one
connector sequence, but `P13WeightedLiveWindowPackage.connector` has type
`State -> Coordinate -> Fin 15 -> Vertex`; distinct coordinates need not use
the same connector.  A state-only adapter would add a false uniform-connector
assumption.

## Provenance audit

Node [21] supplies the packing, finite barrier table, and exact counts.  A
weighted package additionally supplies symbolic connector sequences and the
original-graph predicate `P13BarrierConnectorValid`.  Neither supplies a
completed finite graph, a support, preservation outside that support,
minimum-degree preservation, target avoidance for the completion, or equality
between the completion response and the weighted predicate.

Therefore the interpretation cannot be constructed from current predecessor
data.  Adding it as a field of a public verified node would inject the missing
semantic conclusion.

## Lean boundary

`P13WeightedLocalGraphInterpretation` records the minimal positive producer,
indexed by scheduled states and coordinates.  Its derived lemmas prove:

- every exact connector vertex belongs to the interpreted support;
- every vertex of the identical selected window belongs to that support.

`P13WeightedLocalGraphInterpretationRequirement` is the honest negative
residual.  No classical dichotomy is exported as a completed public endpoint.

## Comparison with node [160]

The existing `P13Node160LocalGraphCompletion` is reusable as the semantic
codomain: it already owns graph finiteness, exact window copy, complete declared
support, outside preservation, simple adjacent connector, all safe barriers,
baseline, and target avoidance.  It does not provide the map from weighted
scheduled states/coordinates, nor response reflection.  The new adapter adds
only those two application-specific bridges.

## Verdict

**FAIL for unconditional production; PASS for the exact interface and
dependency-ready ownership lemmas.**  The smallest remaining producer is a
coordinate-indexed local completion constructor plus `connectorExact` and
`responseExact`.  Cross-window commutation and skeleton injection remain
strictly downstream.  No product, Boolean cube, graph universe, or context
universe is enumerated.

Focused check:

```text
lake env lean Erdos64EG/P13WeightedLocalGraphInterpretation.lean
```

passes.  No TeX or web status was changed.
