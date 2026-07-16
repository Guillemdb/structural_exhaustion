# Nodes 21--24: weighted live/cold handoff

## Defect freeze

- Defect ID: `EG64-P13-WEIGHTED-LIVE-COLD`.
- Stable nodes: `[21]`, `[22]--[24]`, with negative output consumed by
  `[145]--[157]`.
- Failed implication: the 91 coordinatewise safe/flat counts do not imply
  realization of the Boolean cube `(P13BarrierIndex -> Bool)`, and that cube
  is not the product-cost object used by the manuscript.
- Repair level: level 2, using the already declared hot/cold residual and the
  local conditional-fibre invariant.
- Smallest verified ancestor: `VerifiedP13MultiScaleCurvaturePrefix` at
  `[21]`, retaining the exact selected packing and all 91 safe/flat rows.
- Blast radius: the statement of `lem:p13-window-package`, the definition of
  hot/cold windows, the proof of `prop:p13-density`, and the auxiliary node
  `[160]` inserted between `[21]` and `[22]`.

## Directed branch state

The incoming state contains the same minimal counterexample, the CT12-selected
maximum induced-`P13` packing, its order, target avoidance, the 91 accepted
barrier indices, and their exact safe and flat counts.  It does not contain a
Boolean response cube or commuting product of arbitrary local modifications.

For one exact selected window `P`, a live package is a finite graph-owned state
list and an ordered list of separated scale/barrier tests.  Each test filters
only the fibre retained by its predecessors and carries the local inequality

`safe(i) * |next fibre| <= flat(i) * |current fibre|`.

The final fibre must be nonempty, and the initial states must inject into the
declared skeleton family.  The variable-factor conditional-fibre theorem then
telescopes the local inequalities.  It enumerates neither Boolean assignments
nor graphs, contexts, or universes.

Failure of `Nonempty (LivePackage P)` defines a cold residual.  This residual
stores the same selected window `P`; it does not claim that a particular
Boolean assignment is missing.  The graph-owned cold consumer classifies that
same window by degree, retains a strict-surplus position when present, and
otherwise constructs its exact cubic external-stub/corridor route.

## Quantifier normalization

The repaired split is

`forall P in packing, Nonempty (LivePackage P) or not Nonempty (LivePackage P)`.

It is not

`forall epsilon : P13BarrierIndex -> Bool, exists state, response state = epsilon`.

The positive witness is one complete sequential fibre certificate.  The
negative witness is its exact logical negation paired with `P`.  Classical
case selection does not inspect or materialize any ambient family.

## Both-sides test

| Predicate | Positive payment | Negative residual | Consumer |
|---|---|---|---|
| `Nonempty (LivePackage P)` | the complete variable-factor product cost for `P` | `not Nonempty (LivePackage P)` with the identical `P` | selected-window surplus/corridor route, then `[151]--[157]` |

The full constant `c13 = 118.108581006...` is charged only for positive
packages.  If the hot comparison does not close, exact partition counting
gives `C >= (theta - theta_win)n - o(n)`.  No fraction of `c13` is assigned to
a cold window.

## CT and route worksheet

- S-Def: exact selected window, ordered local scale/barrier schedule, exact
  retained fibres, per-test safe/flat factors.
- S-Dich: live certificate or its negation; exhaustive by classical logic.
- S-Pers: both constructors retain node `[21]` and the identical selected
  packing member.
- S-Det: packing order and all later stub/corridor tie-breaks are inherited.
- S-Rout: the cold constructor forgets only certificate absence and supplies
  its stored window to `routeSelectedWindowCorridor`.
- S-Trig: that runner accepts every exact selected window; no realization fact
  is needed by its graph-geometric classifier.
- S-Comp: the hot side uses conditional-fibre multiplication; the cold side
  uses the existing 15-stub and 13-excess ledgers.
- S-Meas: no recursive call occurs in this handoff.

## Leaf totality and current boundary

| Branch | Local result | Consumer | Status |
|---|---|---|---|
| live | variable-factor product inequality | hot entropy count | interface implemented; graph-owned package construction remains to be proved |
| cold/noncubic | strict surplus position on the same window | surplus ledger | implemented |
| cold/cubic | exact same-window first-failure corridor result | F1--F5 refinement | implemented up to the existing structural-germ boundary |

This repair corrects the statement and the typed handoff.  It does not declare
the cold branch closed: the existing quiet corridor result still lacks the
bounded D4--D7 response/context data needed for F2, F3, and the final
same-interface compression.  Accordingly nodes `[22]--[24]` may expose their
local arithmetic split, but `prop:p13-density` remains pending until
`[145]--[157]` closes.

## Practicality

The product checker visits each retained state at most once per supplied local
coordinate.  The cold handoff performs one degree classification on 13 path
positions and then uses the fixed 15-stub local schedule.  No step enumerates
all graphs, all contexts, all state subsets, or a Boolean cube.

