# Proposed node [161]: D1--D3 base-scale split

The Lean-only candidate compiled and received independent review PASS.  It has
therefore been synchronized narrowly as green node `[161]`.  Nodes `[160]`,
`[162]`, and `[163]` remain white.

## Residual-flow ledger

| Incoming branch | Exact retained residual | Local inspection | Short output | Long output |
|---|---|---|---|---|
| computed node-[159] quiet constructor | node-[158] fork, exact selected window, canonical stub, same-window equality, absence of every corridor event, structural germ, and equality to `runP13SameWindowStructuralFrontier` | compare the literal return-support length once with `Q_base` | the same indexed quiet input and `support.length ≤ Q_base` | the same indexed quiet input and `Q_base < support.length` |

Here

```text
Q_base = 4^2 * 13^2 * 2^13.
```

This is exactly the cardinality of the normalized fixed two-boundary state
with the D4--D7 coordinate alphabet specialized to `Fin 0`.  The
specialization records only the already proved D1--D3 factors: two capped
boundary degrees, two window offsets, and thirteen target-response bits.
It does **not** claim that an empty alphabet is semantically complete for
D4--D7.

## Both-sides audit

- The short constructor contains only the existing graph-owned
  `BoundedSameInterfaceResidual` at `Q_base`.
- The long constructor contains only the existing graph-owned
  `LongSupportResidual` at `Q_base`.
- Both constructors retain the entire proof-carrying node-[159] quiet input as
  an index.  In particular, no arbitrary germ can enter: the input requires an
  equality to the computed node-[159] run output.

No repetition, finite response-table completeness, `ColdBoundedGerm`, CT3
compression, density estimate, or D4--D7 conclusion is present.  The visible
work is one natural-number comparison; the corridor construction and scan are
charged to node `[159]`.
