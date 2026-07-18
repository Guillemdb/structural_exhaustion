# Red-team audit: selected-slot connector

## Verdict

Selected active-slot provenance is absent at the node-[144] separator.  The
implementation correctly exposes the missing dependent port equalities and
executes the existing blocker consumer only conditionally on a transported
literal candidate.

## Provenance checks

1. A collision item is an exact scheduled pair of selected active slots.
2. Each canonical germ targets the full `PortSupport` of the first slot of one
   collided pair, not specifically its buffer endpoint.
3. `firstLands` and `secondLands` prove membership in those three-vertex
   supports.  They do not prove a role equality.
4. Root and after-edge separator incidences are edges along the canonical BFS
   tree paths.  An internal separator vertex or its outgoing edge need not be
   the center or port edge of either selected demand.
5. Hence neither center equality nor `portOfSlot` equality follows from the
   retained comparison.

## Typed residual

`SlotIdentification` requires an actual selected slot, its center equality,
and `HEq` between its center-indexed `portOfSlot` and the raw separator port.
`PairIdentification` requires two such identities and selected-slot
distinctness.  The heterogeneous equality prevents an invalid cast between
ports at different centers.

The frontier names `PairIdentification` as its exact missing consumer.  It
does not contain a proof of that type.

## Conditional execution

Given pair identification, `blockerPair` constructs the existing
`SurplusPairBlocker.Pair`.  Given a role-transported candidate with both
membership and `Blocks`, `execute` invokes the existing finite scan.  Its
`absent` branch contradicts the supplied candidate, so the theorem returns the
proof-carrying first `found` blocker.  No replacement scan is introduced.

## Rejected inferences

- support membership is not buffer equality;
- a BFS-tree edge is not automatically a selected surplus port;
- sharing a raw separator carrier does not place the carrier in the selected
  demand ledger;
- no Type-B assignment or response equivalence follows from this branch.

Closing this connector requires a new upstream theorem tying the particular
separator incidences to selected slots.  Such a theorem is not true for an
arbitrary internal BFS divergence and would require an additional manuscript
case split or a different consumer for internal separator ports.
