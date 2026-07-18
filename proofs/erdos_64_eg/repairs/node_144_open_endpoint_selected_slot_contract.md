# Node [144]: selected-slot connector for the open endpoint residual

## Provenance trace

The coarse collision is a collision of `SurplusPairResponse.ScheduledPair`
values.  Hence the collision itself retains four selected active slots: two
slots in each collided scheduled pair.

The two canonical germs do not terminate specifically at the buffer endpoint
of one of those slots.  For each collided pair, the germ target is
`endpointSupport pair true`, which is the full three-vertex `PortSupport` of
the pair's first slot.  The selected target may therefore be its left
shoulder, right shoulder, or cubic buffer.  A root or after-edge divergence
then records edges along the two BFS tree paths.  Its separator ports are
incident edges at an internal tree vertex; they need not be the original
selected surplus ports and may have unrelated centers.

Therefore the exact node-[144] source supplies:

- the two collided scheduled pairs and all their selected slots;
- membership of each final germ target in one selected three-vertex support;
- the complete BFS path comparison and separator incidences; and
- the locally activated open-endpoint failure at the separator.

It does **not** supply an equality between either separator raw port and any
selected active slot.

## Exact missing connector

For a raw separator port `(h,x)`, selected-slot provenance must contain:

1. an actual `SurplusPortActivation.Slot setup`;
2. equality of its center with `h`; and
3. heterogeneous equality of its dependent `portOfSlot` with the raw port.

For the two raw ports, the slots must also be distinct.  These fields are the
minimal input needed to transport the literal buffer/shoulder coincidence to
the role-labelled `SurplusPairBlocker.Pair` scan.

## Conditional blocker execution

Once exact selected-pair identification and a transported shared-role
candidate are supplied, the existing `SurplusPairBlocker.Pair.run` is the
unique consumer.  A proved candidate membership and `Blocks` fact exclude the
`absent` result and yield a proof-carrying `found` result.  No new blocker scan
or ambient enumeration is required.

## Result

The current upstream branch stops at the typed selected-pair identification
residual.  It cannot construct that value merely from membership in a
three-vertex endpoint support.  In particular, support membership must not be
silently strengthened to equality with the buffer role, and a BFS separator
edge must not be silently reclassified as a selected surplus port.
