# Node 48 conditional-fibre cost repair

## Defect freeze

- Defect: `EG-N48-RANK-PRODUCT`.
- Stable node: `[48]`, `cor:forced-curvature-cost`.
- Failed implication: CT15 absence of a functional admissible rank drop on
  each literal wedge coordinate implies simultaneous product realization of
  all curvature responses, hence a factor
  `(543958 / 111286)^rank` in the graph-state count.
- Classification: quantifier error (rank/nonidentification versus product
  realization), level-3 producer/consumer repair.
- Smallest verified ancestor: the same-context node-[24] coverage output and
  node-[47] CT15 full-rank prefix.
- Blast radius: nodes `[49]`--`[54]` may not spend curvature entropy; the
  independent large-budget route `[55]` remains available only after its
  separate strict-quarter producer.
- The source manuscript is unchanged by this sketch.

## Directed branch state

The active path is the bounded constructor of node `[19]`, followed by
`[21]`, the realized/within-cap `[22]`--`[24]` branch, the exact remainder
`[25]`--`[30]`, and the CT15 rank route `[31]`--`[47]`.  Its inherited data are:

- the literal selected packing and exact partition
  `|R| + 13 p13 = n`;
- the exact finite density cap at node `[24]`;
- the positive-deficiency incidence bound and exact wedge floor;
- the literal wedge-coordinate enumeration (at most `n^3` coordinates);
- CT15 no-drop and `rankCount = wedgeCount` on the same graph;
- the bounded-surplus residual from node `[19]`, with its runtime scale
  parameters retained but not silently treated as fixed constants.

The exact unconditional finite output is

```text
250825743018 |R|
  <= 98608581006 W2(R) + 2*98608581006 sigma(G).
```

The unavailable fact is simultaneous conditional-fibre factorization.  No
node on this path supplies it.

## Quantifier normalization

The current CT15 result is

```text
for every coordinate c, c is not target-dependent,
and the coordinate count equals W2(R).
```

The manuscript entropy use needs a statement over one common finite state
family: at every coordinate prefix, the surviving flat fibre has relative
capacity at most `111286 / 543958`, so the ratios telescope over the entire
ordered wedge schedule.  Pairwise separating contexts do not supply this.

The exact negation is the absence of a graph-owned conditional-fibre
certificate.  The repaired node retains that absence as a typed requirement;
it is never coerced to a cost payload.

## Both-sides invariant

| Predicate | Positive account | Negative residual | Measurable from | Consumer |
|---|---|---|---|---|
| A graph-owned conditional-fibre certificate exists | Generic telescoping yields `543958^r <= 111286^r * skeletonCount`; combine with the exact finite wedge/rank magnitude | Named missing conditional-fibre producer, retaining node `[24]` and `[47]` | Proof-level dichotomy; the certificate checker itself scans only the supplied local state list and coordinate schedule | Positive: nodes `[49]`--`[54]`; negative: closure-robust `[55]` only after an independent `P13QuarterNetBudget` |

This is the earliest ladder-ready invariant.  The negative side cannot enter
the entropy branch.

## Reusable contract

The level-3 Graph contract contains:

- a supplied finite local state list;
- an ordered coordinate schedule;
- exact survivor counts for every prefix;
- nested-prefix persistence;
- one local inequality
  `safe * nextCount <= flat * currentCount` per coordinate;
- a starting skeleton-capacity bound and a nonempty final fibre.

Its theorem proves `safe^r <= flat^r * skeletonCount` by induction.  Its
checker work is `O(states * coordinates)`.  It enumerates neither assignments,
subsets, ambient graphs, paths, contexts, nor a Boolean cube.

## Leaf table

| Branch | Output | Route |
|---|---|---|
| certificate present | exact finite node-[48] magnitude plus conditional-fibre product-cost certificate | `[49]` |
| certificate absent | typed missing-producer requirement retaining the exact finite magnitude | `[55]` only after a separately proved strict-quarter budget; otherwise remains the declared open handoff |

## Parameter caveat

The bounded-surplus node-[19] residual stores arbitrary runtime
`windowSize`, `remainderSize`, and `primitiveSize`.  It proves the displayed
finite inequality with explicit `sigma(G)` error, but not the asymptotic
`o(|R|)` notation until a separate adapter proves those sizes equal fixed
authored thresholds.  The Lean node must not call the raw residual a fixed
near-cubic estimate.

## Synchronization gate

The original TeX, diagram color, WebExport status, and implementation log may
be changed only after the generic certificate, non-Erdos transfer example,
Erdos instantiation, focused builds, and an independent red-team PASS all
exist.
