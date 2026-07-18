# Repair sketch: nodes [22]--[24] weighted-hot aggregation

## Frozen defect

- Stable nodes: `[145]`, `[148]`, `[149]`, `[150]`, then `[22]`--`[24]`.
- Smallest verified ancestor: `VerifiedP13MultiScaleCurvaturePrefix`, including
  the exact node-[21] bounded-surplus inequality, and the exact selected
  induced-`P13` packing.
- Verified local split: every selected window is classified exactly once as
  `P13WeightedHotWindow` or `P13WeightedColdWindow`; both constructors retain
  the identical selected window.
- Failed implication: the existence of one complete conditional-fibre ledger
  per hot window does not by itself prove that the product over all hot
  windows embeds into one target-testable family bounded by the labelled
  skeleton count.
- Blast radius: without that aggregate producer, strict density overflow at
  node [23] cannot force a quantitative cold family and node [24] cannot be
  reached unconditionally.

The source specification is `original_erdos_64_proof.tex`, especially
`lem:p13-window-package`, `lem:hot-failure-cold-mass`, and
`prop:p13-density`.  The source file remains read-only.

## Exact directed branch state

The active state contains:

1. the selected graph, baseline, target avoidance, and minimality context;
2. node [21]'s 91 exact safe/flat rows and bounded-surplus field;
3. the duplicate-free selected `P13` packing;
4. the exact weighted hot/cold partition of that packing;
5. for every hot window, its complete sequential conditional-fibre package;
6. on the node-[23] branch, the strict finite inequality
   `skeletonNumerator * n < rateNumerator * p13`.

No Boolean cube, family of all graphs, family of all outside contexts, or
simultaneous realization premise is available.

## Required producer: aggregate target-test package

The manuscript's independence paragraph must be represented by a producer
whose output contains the following data, not merely a cardinal inequality.

`P13WeightedHotAggregatePackage` should contain:

- the exact list `p13WeightedHotWindows ctx node21`;
- a finite type of aggregate states and its duplicate-free enumeration;
- a finite type of aggregate coordinates and its duplicate-free enumeration;
- an owner map from every coordinate to its exact hot window;
- an interpretation of each owner-coordinate by that window's stored
  conditional-fibre package;
- a graph-owned target-response predicate for each coordinate;
- a total dependent `glue` map defined on every tuple of one listed local
  state per exact hot window, together with a restriction map and the
  componentwise recovery theorem
  `restrict (glue choice) owner = choice owner`; hence `glue` is injective;
- a commuting theorem saying that changing the state owned by one selected
  window preserves every coordinate owned by another selected window;
- a target-test soundness theorem for the combined response family;
- an injection from aggregate response vectors into the labelled skeleton
  state family used by `lem:skeleton-dominates`;
- the exact finite product/rate inequality and a checker bounded by the sum of
  the local fibre scans plus the supplied coordinate count.

The commuting theorem is the load-bearing missing lemma.  Vertex-disjointness
of the thirteen window vertices alone is insufficient if the outside
connector supports overlap.  A valid producer must either prove disjointness
of the complete declared supports, or assign overlapping coordinates to a
canonical owner and prove response preservation for the non-owner windows.

## Missing-lemma ledger

| Lemma | Exact inputs | Required conclusion | Intended owner |
|---|---|---|---|
| `hotCoordinate_owner_exact` | aggregate coordinate | owner belongs to exact hot list and local coordinate belongs to its package | Erdős adapter |
| `hotSupport_owner_or_overlap` | two owned local coordinates | disjoint supports or canonical overlap owner with retained response | Graph |
| `hotResponse_commutes` | aggregate state, two distinct owners | changing one owner preserves the other response | Graph/Routes |
| `hotGlue_recovers` | every dependent tuple of listed local hot states and every owner | restricting its glued graph recovers the selected local state; hence the glue is injective | Graph plus Core finite product |
| `hotAggregate_target_sound` | aggregate coordinate and state | response equals the declared target test on the graph-owned completion | Erdős semantic bridge |
| `hotAggregate_skeleton_injective` | two aggregate response vectors | equal skeleton code implies equal vector | Erdős semantic bridge |
| `hotAggregate_budget` | completed aggregate package | `rate * hotCount <= skeletonBudget` | entropy/counting consumer |
| `p13ExactWeightedRate` | exact safe/flat products from node [21] | certified lower rate `118108581006 / 10^9`, by integer/fixed-point power inequalities only | Core numerical certificate/Erdős instantiation |
| `hotFailure_cold_payment` | exact partition and `hotAggregate_budget` | `rate * p13 <= skeletonBudget + rate * coldCount` | Core arithmetic/Erdős thin theorem |
| `overflow_forces_cold_nonempty` | node-[23] strict overflow and previous payment | positive cold count | Erdős arithmetic consumer |

The last two rows are pure finite arithmetic and are dependency-ready.  The
preceding rows are the semantic construction that must not be replaced by an
author-supplied `hotAggregate_budget` assumption at a claimed public endpoint.

## Both-sides test

Predicate `P`: the graph-owned aggregate package exists and its response map
commutes across all exact hot-window owners.

- Positive side: its injective target responses pay
  `rateNumerator * hotCount` into the finite skeleton budget.
- Negative side: select the first owner/coordinate/state pair where support
  ownership, response commutation, target soundness, or skeleton injection
  fails.  This is a typed local residual, not an unstructured absence proof.
- Measurability: the selector scans the supplied hot list, its stored finite
  coordinate lists, and the proof-specified support certificates only.
- Route: support overlap first enters its own typed two-live-window overlap
  residual.  It may enter the cold F first-failure/ownership analysis only
  after an adapter proves the exact F trigger; overlap alone is not package
  absence and is not a cold window.  Target-response mismatch enters CT3/CT7
  only with one concrete compatible distinguishing context; skeleton-code
  collision enters CT9/CT10 only after the concrete collision is proved to
  satisfy the selected tactic's label/refinement trigger.

The negative route is not yet discharged merely by defining the package.
The producer becomes unconditional only when every first failure has the
declared typed consumer above.

## Exact arithmetic consumer

For arbitrary natural `rate` and `budget`, the partition identity and

`rate * hotCount <= budget`

imply

`rate * p13 <= budget + rate * coldCount`.

Combining this with strict node-[23] overflow gives `0 < coldCount` whenever
`0 < rate`.  More generally the difference between total demand and the
skeleton budget is paid by `rate * coldCount`.  This proof uses only `omega`
or semiring arithmetic and performs no enumeration.

## Leaf-totality target

| Branch | Exact residual | Consumer |
|---|---|---|
| aggregate package succeeds | injective combined target responses | skeleton entropy budget |
| support ownership fails | first collided support/owner pair | F1--F5 ownership/corridor route |
| response commutation fails | concrete coordinate and two local states | CT3/CT7 distinguishing-context payload |
| skeleton injection fails | concrete pair with equal skeleton code | CT9/CT10 refinement |
| hot budget plus node-[23] overflow | positive cold family | nodes [150]--[157] |
| cold branch closes | node-[23] impossible | construct node-[24] and reuse nodes [25]--[26] |

No row may be marked closed until its consumer is kernel-checked from the
exact predecessor state.

## Practicality

All scans are over the exact selected packing, the stored local coordinate
lists, and proof-supplied finite supports.  Work must be bounded by the sum of
local fibre checks plus a polynomial overlap/ownership scan.  No ambient graph
universe or all-context universe is materialized.
