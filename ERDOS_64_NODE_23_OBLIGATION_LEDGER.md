# Node [23] obligation ledger

## Frozen topology and exact incoming branch

In `original_erdos_64_proof.tex`, Part I has exactly one incoming edge for
node `[23]`:

```text
[22] -- yes --> [23] P13 window entropy overflow
```

Node `[23]` is a local Part-I density-overflow cell.  Its responsibility is to
retain the exact strict reverse finite-cap payload produced by node `[22]` on
the identical node `[21]` packing.  The later hot/cold closure and bounded-germ
analysis belong to their own Part-XI nodes and must not be counted as node
`[23]` obligations.

The exact Lean predecessor is `VerifiedP13MultiScaleCurvaturePrefix ctx`,
retained by `VerifiedP13Node23FiniteOverflow.previous` and
`VerifiedP13Node23FiniteOverflow.previousExact`.  The node-[22] producer is
`runP13Node22FiniteDensityDecision`; its `.tooLarge` constructor contains the
node-[23] payload.

## Complete obligation ledger

| Task ID | Original-paper obligation/property | Exact predecessor | Lean evidence | Status | Missing producer or resolution |
|---|---|---|---|---|---|
| 23.1 | Retain the exact node-[21] packing/package context selected by the yes edge of node `[22]`; do not rebuild a look-alike packing. | `[22].tooLarge`, itself computed from the exact `[21]` prefix | `VerifiedP13Node23FiniteOverflow.previous`, `previousExact`; `runP13Node22FiniteDensityDecision` | proved | --- |
| 23.2 | Record the strict reverse of the corrected finite window-cap comparison, including the explicit scale-loss and skeleton-normalization errors. | `[22].tooLarge` | `P13WindowDensityFiniteCapWithError`; `VerifiedP13Node23FiniteOverflow.failedCap`; `VerifiedP13Node23FiniteOverflow.strict` | proved | --- |
| 23.3 | Keep the computation local and polynomial.  The node uses only the already selected packing and one exact natural-number comparison, with no graph, context, Boolean-state, or universe-family enumeration. | exact node `[22]` decision on the node `[21]` prefix | `runP13Node22FiniteDensityDecision_exhaustive`; `VerifiedP13Node23FiniteOverflow.strict` | proved | --- |

## Downstream work not owned by node [23]

The Part-XI hot/cold branch, nodes `[145]`--`[157]`, consumes related density
payloads later.  Its F1--F5 and G1--G3 obligations remain tracked at their own
nodes.  They are not prerequisites for marking node `[23]` green, because node
`[23]` has the single input/output responsibility above.

## Verdict

Node `[23]` is **3/3 proved** as a local Part-I cell.  It consumes the literal
node-[22] yes edge and proves the strict corrected finite-overflow payload on
the same predecessor context.
