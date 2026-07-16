# Node [22] repair laboratory: sequential realization and commuting gluing

## Status and frozen source

- Defect: `EG-P13-N22-SIMULTANEOUS-REALIZATION`.
- Source node: `[22]`, `lem:p13-window-package`.
- Smallest verified predecessor: `VerifiedP13MultiScaleCurvaturePrefix` at
  node `[21]`.
- Original manuscript SHA-256 at this iteration:
  `6cea87715450176e2b3e611a347c7147764730866c7174122e5be0445235c671`.
- Verdict after the red-team pass below: **FAIL/blocking**.
- The source manuscript, web descriptor, and concurrent Lean files are not
  edited by this laboratory.

The literal manuscript interface asks, for one selected window, for a finite
state family `S` and response map

```text
rho : S -> (P13BarrierIndex -> Bool)
```

that realizes every Boolean assignment. For several packed windows it also
asks for a commuting gluing theorem preserving all responses. Node `[21]`
proves neither statement. It proves 91 finite label-table rows, their exact
safe and flat counts, and

```text
2^118 * flatProduct < safeProduct.
```

## Directed branch state

The incoming state contains:

- the exact selected minimal target-avoiding graph;
- the exact CT12 maximum induced-`P13` packing and selected windows;
- 399 legal attachment labels and their symbolic compatibility theorem;
- 91 accepted barrier indices;
- exact safe/flat counts for every row;
- the strict integer product-rate certificate;
- literal outside vertices and their 13 adjacency coordinates;
- the graph-owned connector classifier returning all-present or the first
  missing actual connector.

It does not contain:

- a graph modification or completion move for either value of a barrier bit;
- an admissible completion-state family at one scale;
- a separated dyadic scale schedule;
- a response-reflection theorem from completions to the node-`[21]` rows;
- a nonempty terminal fibre;
- support-disjoint or commuting local modifications;
- a global state injection after several windows are combined.

The actual-attachment system cannot fill this interface: it has 13 adjacency
coordinates, not 91 barrier coordinates. The actual connector systems cannot
fill it either: target avoidance proves every retained flat connector bit is
true, and even the product of unrelated per-coordinate connector choices
cannot realize the all-false assignment.

## Candidate invariant: canonical partial completion schedule

Order the pairs `(window, barrier)` lexicographically. A proposed partial
schedule would carry:

1. one exact graph-owned local completion piece for every processed pair;
2. its finite support and declared boundary;
3. the requested response bit and a reflection theorem;
4. a gluing result containing all processed pieces;
5. preservation of every earlier response and of admissibility.

At the next pair, define the first failed clause among:

- `R`: neither requested bit has a reflected local realization;
- `B`: the new piece has a boundary-profile mismatch;
- `O`: its interior overlaps an earlier piece;
- `E`: a cross-edge or shared boundary incidence prevents owned gluing;
- `T`: gluing changes an earlier target response;
- `A`: the glued result is not an admissible completion state.

If no clause fails, extend the schedule. The schedule length is at most
`91 * p13`, so it gives a well-founded local iteration once the pieces exist.

### Both-sides table

| Predicate | Positive payment | Canonical negative residual | Intended consumer | Verdict |
|---|---|---|---|---|
| Reflected realization for both bits | one usable local toggle | first missing requested bit and row | CT10 refinement | Rejected: CT10 can record the row but cannot construct a graph-semantic promotion |
| Same boundary profile | gluing remains typed | concrete profile discrepancy | CT3 target-defect audit | Expressible only after the two actual pieces exist |
| Interior-disjoint support | add one schedule entry | first overlapping earlier piece and overlap vertex | CT7/CT3 | Bare overlap gives neither two response objects nor a distinguishing context |
| No cross-edge/shared incidence | owned gluing | first offending incidence | CT7 local exchange | No exchange or target semantics follows from the incidence alone |
| Earlier responses persist | multiplicative/sequential account | first changed coordinate with before/after states | CT7 distinguishing response | Needs both admissible states and a finite exact context generator |
| Final schedule is nonempty | terminal state pays the telescoping ratio | first empty conditional fibre | CT6/CT10 | Empty fibre supplies arithmetic failure only, not a semantic trigger |
| Windows commute | cross-window state injection | first noncommuting window pair plus failed clause | CT3/CT7 | No current consumer accepts only a gluing failure |

The invariant is not admitted. Its positive side would be sufficient only
after a graph-owned toggle producer and response reflection theorem are
proved. Its negative residuals are finite and canonical, but their proposed
consumers require semantic fields not derivable from overlap or incidence.

## Why the existing sequential filtration does not repair the gap

`FiniteSequentialFiltration` correctly computes either a complete retention
ledger or the first ratio-failing conditional fibre for a supplied finite
state table and supplied predicates. It proves the exact telescoping
inequality. For node `[22]`:

- no graph-owned state table is supplied;
- no 91 executable completion predicates are supplied;
- terminal nonemptiness is not supplied;
- a first ratio failure contains no piece, context, replacement, target hit,
  or finite refinement promotion;
- a per-window complete ledger contains no cross-window injection.

Thus the arithmetic runner is a useful checker but not the missing producer.

## First-incompatibility residual schemas

The following payloads are the smallest honest records exposed by the
partial-schedule attempt.

### `MissingToggle`

```text
(ctx, node21, window, barrier, requestedBit,
 allActualCandidatesReject, node21RowSemantics)
```

This is not a CT10 promotion. A promotion must construct a new finite datum or
response object; `allActualCandidatesReject` does not do so.

### `SupportOverlap`

```text
(ctx, partialSchedule, earlierIndex, nextIndex,
 earlierPiece, nextPiece, overlapVertex, membershipProofs)
```

This is not a CT7 trigger. CT7 needs two comparison objects and an exact
realization/distinction/neutrality semantics over its declared contexts.

### `NoncommutingGluing`

```text
(ctx, partialSchedule, earlierIndex, nextIndex,
 firstFailedClause, beforeCompletion, attemptedCompletion,
 preservedBoundaryData)
```

This becomes a CT3 or CT7 payload only if `firstFailedClause` additionally
carries a concrete target-distinguishing context or a certified smaller
target-complete replacement. Neither follows from a failed gluing equality.

### `EmptyTerminalFibre`

```text
(ctx, orderedSchedule, firstEmptyStage, nonemptyBefore,
 emptyAfter, exactResponsePredicate)
```

This is a semantic missing-completion residual, but it has no current closing
consumer. Treating it as a cold window simply renames the gap.

## Locality and work audit

The proposed iteration scans only the selected windows, 91 barriers, and
supports of proof-supplied local pieces. With maximum support size `s`, it
would require `O(91 * p13 * s^2)` membership/incidence comparisons plus the
local response checks. No ambient graph, subgraph, coloring, context, or graph
family is enumerated.

The existing literal connector search instead ranges over length-15 vertex
sequences, with an `n^15` candidate envelope. Although formally polynomial of
fixed degree, it is not a practical realization algorithm and, more
importantly, its accepted responses are fixed true by target avoidance. It
does not produce the missing two-valued local moves.

## CT worksheet

- **Instance:** node `[22]`, first `(window, barrier)` insertion failure.
- **Input:** exact node-`[21]` prefix and the CT12-selected packing.
- **S-Def:** fails at the graph-owned two-valued completion piece.
- **S-Dich:** the six first-failure clauses are finite and exhaustive only
  after S-Def.
- **S-Equiv:** missing; no completion-response reflection theorem.
- **S-Pers:** expressible through owned gluing but unproved without pieces.
- **S-Det:** lexicographic schedule and first failed clause are deterministic.
- **S-Rout/S-Trig:** no exact CT10/CT7/CT3 trigger follows from the honest
  residuals above.
- **S-Comp:** telescoping is available from the generic filtration once its
  premises exist.
- **S-Rest/S-Meas:** remaining schedule length decreases.
- **S-Comp work:** local polynomial bound above; no global enumeration.

## Red-team rerun

### Provenance attack

All positive graph-completion fields in the proposed schedule lack producers.
The node-`[21]` label table cannot be used as a graph completion, and selected
window disjointness cannot be used as support-disjointness of outside pieces.

### Quantifier attack

- Per-coordinate existence is not simultaneous realization: response set
  `{00, 11}` omits `{01, 10}`.
- Pairwise compatible pieces need not have one simultaneous gluing when three
  pieces share a resource.
- One local completion per assignment is not one canonical graph-to-state map.
- A complete local product is not a cross-window product.
- Quotient-rank or injectivity is not a Boolean cube.

### Consumer attack

- CT10 classifies supplied data and promotions; it does not invent the missing
  completion piece.
- CT7 requires exact comparison semantics, not overlap alone.
- CT3 requires a concrete context defect or certified smaller replacement.
- CT15 requires a target-relative dependence certificate, not statistical or
  cardinality correlation.
- The registered CT9-to-CT7 route has the wrong source residual.

### Scope classification

This is not yet a methodology-level scope obstruction. A completion piece,
finite support, boundary profile, response certificate, and owned gluing are
all expressible in the current proof language. The defect is a level-3
producer/pattern gap: no theorem constructs such pieces from the node-`[21]`
rows, and no theorem consumes their first incompatibility if construction
fails.

No generic route or transfer example is added. Any route implemented now
would have to take the missing semantic certificate as caller input and would
therefore validate proof injection rather than node `[22]`.

## Verdict

**FAIL/blocking.** The canonical partial-schedule invariant makes the first
simultaneous-realization and commuting-gluing failures finite and explicit,
but neither side passes the both-sides test. The first exact failed obligation
is S-Def: construct one graph-owned, response-reflected two-valued completion
move for a selected window and barrier. Node `[22]` remains white.
