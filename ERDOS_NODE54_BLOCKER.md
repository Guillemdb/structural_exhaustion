# Erdős nodes 31–54: unresolved conditional-fibre producer

The exact node-[53] small branch can close at node [54] once the incoming
ledger contains

```text
543958 ^ r ≤ 111286 ^ r * stateCount.
```

The present node-[31] certificate proves survival/nonidentification for a
target-rank coordinate set.  That statement does not imply the displayed
simultaneous conditional-fibre inequality.  Coordinatewise activity alone is
insufficient: a state set can realize both values in every coordinate without
realizing independent combinations.

The existing generic Core theorem
`ConditionalFibreProductCost.Certificate.power_le_flat_mul_skeleton` proves
the required inequality from an ordered conditional-fibre ledger, a starting
capacity, and a nonempty final fibre.  What is still absent is the
problem-specific producer, on the literal incoming completion carrier, of the
per-prefix inequalities

```text
543958 * nextCount ≤ 111286 * currentCount
```

and terminal nonemptiness.  It must be produced on the node-[31]/[32]
residual and accumulated by Core; it cannot be supplied to node [54], encoded
as a new node-local family, or inferred from quotient injectivity.

No new diagram node or edge is required.  Once this producer exists, node
[48] can attach the powered inequality, node [53]'s small constructor is
contradictory by symbolic powered transport, and its complementary constructor
is exactly node [55]'s Residual C.
