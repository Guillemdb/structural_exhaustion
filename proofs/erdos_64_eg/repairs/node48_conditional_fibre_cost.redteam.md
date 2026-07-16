# Red-team audit: node 48 conditional-fibre cost

## Baseline

- Repair sketch: `node48_conditional_fibre_cost.md`.
- Repository commit: `5190f9717bab55b485b0220604bf9e0b37a1c27b`.
- Manuscript SHA-256 at audit time:
  `20a27d8ce729a42a34553b21f6456d542d361cbe709cbc76006372fb6ecbf9b7`.
- Failed node and claim: `[48]`, `cor:forced-curvature-cost`.
- Methodology consulted: residual-class extension, legal residual exit,
  target-test equivalence, legal payload exit, C1--C5, and leaf totality.
- Current verdict: **FAIL**.

## Provenance matrix

| Used fact | Producer | Earlier on path? | Independent? | Verdict |
|---|---|---:|---:|---|
| selected packing and bounded-surplus residual | node `[21]` | yes | yes | pass |
| exact density cap | node `[24]` | yes | yes | pass |
| exact remainder partition and wedge floor | nodes `[25]`--`[30]` | yes | yes | pass |
| CT15 coordinate count equals wedge count | node `[47]` through `VerifiedP13Node24DensityHandoff.globalRankPrefix` | yes | yes | pass |
| near-cubic error control needed by the printed corollary | node `[21]`'s bounded-surplus predecessor / authored scale specialization | yes | yes | **not consumed** |
| simultaneous conditional-fibre realization | new realization payload | no producer | independent of CT15 | correctly left conditional |

The node-`[24]` connector stays on the same `ctx`, selected packing, and
coverage residual.  The exact integer arithmetic is valid.  In particular,
eliminating `n = |R| + 13p` from the window cap gives
`98608581006 p <= 1500000000 |R|`, and the wedge ledger gives the stated
numerators `250825743018` and, conditionally on the sharper cap,
`253825743018`.

## Quantifier attack

| Claim | Literal quantified form | Countermodel attempted | Result |
|---|---|---|---|
| CT15 full rank supplies product realization | every coordinate is nondependent | pairwise/nondependent does not construct one common state family | correctly rejected by repair |
| realization states count distinct skeletons | `State -> Context` with no injectivity | two distinct state tags map to the same context; one-coordinate `2 -> 1` ledger passes | **blocking** |
| `skeletonStateCount` is manuscript skeleton cardinality | arbitrary `Nat` plus `states.length <= skeletonStateCount` | choose the number independently of any graph/skeleton collection | **blocking** |
| all coordinate filters are on one nested fibre | one supplied state list filtered in schedule order | inspected directly | pass |

The reusable telescoping theorem has the correct direction:
`safe * next <= flat * current` at every prefix and a nonempty terminal fibre
imply `safe^r <= flat^r * skeletonCount`.  The missing point is semantic, not
arithmetic: the Erdős payload does not identify `skeletonStateCount` with an
enumerated graph-owned skeleton family and does not inject states into that
family.  Therefore the positive constructor cannot yet be spent as the
manuscript entropy cost.

## Branch and invariant audit

- Positive side: carries exact finite wedge magnitude and a valid abstract
  conditional-fibre certificate.
- Negative side: carries exact absence of that payload.
- Cross-branch leakage: none found in the Lean arithmetic.
- Theorem weakened: yes relative to the current manuscript.  The printed
  node `[48]` remains an unconditional near-cubic asymptotic cost, while Lean
  proves an explicit-surplus finite inequality plus a realized/open split.
- Missing persistence: the realized payload does not pin the skeleton family;
  the open payload does not contain a declared consumer trigger.

## CT and residual obligations

| Block | Trigger | Unfilled obligation | Verdict |
|---|---|---|---|
| existing CT15 full-rank prefix | node `[24]` same-context coverage | none in the connector | pass |
| conditional-fibre theorem | supplied literal states and coordinates | graph-owned skeleton interpretation/injection | **fail** |
| open realization residual | absence of the realization payload | typed consumer, routing, and trigger | **fail** |

The comment naming node `[55]` is not a route.  The open requirement carries
neither an independently proved strict-quarter budget nor a destination type
whose trigger accepts the payload.  Under the methodology, an unconsumed
residual is not a legal completed leaf.

## Leaf totality

| Leaf | Certificate or consumer | Practical checker | Verdict |
|---|---|---:|---|
| realized | abstract product inequality | `O(states * coordinates)` | semantic consumer incomplete |
| open requirement | no typed consumer | proof-level split only | **fail** |

## Practicality and ownership

- Largest enumerated universe: the supplied local state list times the
  supplied wedge-coordinate schedule.
- Coordinate schedule bound: at most `n^3` from the existing CT15 prefix.
- Checker bound: at most `states.length * coordinates.length`, and quadratic
  in the combined explicit input size.
- Hidden global enumeration: none found.
- Ownership defect: `ConditionalFibreProductCost.Profile` contains only
  generic finite collections, Boolean filtering, natural arithmetic, and a
  work budget.  It has no graph object.  Under the repository ownership rule
  it belongs in `Core`, unless the contract is strengthened with genuinely
  graph-specific skeleton semantics.
- Transfer defect: the file under the Mantel package is a `Fin 4`/`Bool`
  fixture.  It does not instantiate the profile in the proof of Mantel's
  theorem or another named textbook graph theorem, so it does not satisfy the
  external transfer gate.

## TeX--Lean--web correspondence

- Exact statement match: **fail**.  The manuscript still says full rank plus
  the wedge lower bound unconditionally yields the curvature cost.
- Diagram branch match: **fail**.  Part IV has only `[47] -> [48] -> [49]`;
  it contains no realized/open split or open-realization successor.
- Web mapping: **fail**.  Node `[48]` is not formalized and no proof-step
  descriptor exposes the new declarations.
- Generic ownership: **fail**, as above.
- Trust search: no `sorry`, `admit`, unsafe declaration, or new axiom in the
  reviewed files.  The generic theorem reports only `propext`; the Erdős
  declarations report Mathlib/Lean's ordinary `propext`, `Classical.choice`,
  and `Quot.sound`.  The tiny transfer fixture uses `native_decide`.

## Validation run

Passed:

- focused Lean compilation of the generic profile;
- focused Lean compilation of the Mantel fixture;
- focused Lean compilation of `P13ForcedCurvatureCost`;
- `make framework-build`;
- `make mantel-example-build`;
- `make erdos-example-build`.

## Findings

### Blocking

1. No graph-owned enumerated skeleton family or injective state-to-skeleton
   interpretation fixes `skeletonStateCount` to the manuscript count.
2. The open requirement has no legal typed consumer route and trigger.
3. The finite explicit-surplus theorem does not consume the bounded-surplus
   scale to prove the near-cubic conclusion printed at node `[48]`.
4. TeX, the Part-IV diagram, WebExport, and the green-node set do not describe
   the repaired split.

### Required cleanup

1. Move the graph-independent finite-fibre machinery to `Core`, or add actual
   graph semantics that justify `Graph` ownership.
2. Replace the abstract Mantel-package fixture with a use in a named textbook
   graph theorem through the same public profile.

### Advisory

- Keep the exact ordinary and sharper integer inequalities; both checked and
  are useful predecessor arithmetic for a repaired node.

## FAIL disposition

- First obligation returned to the repair loop: bind the positive payload to
  an explicit graph-owned skeleton collection by construction, with a proved
  injection/cardinality bridge, and make the product theorem conclude against
  that literal cardinality.
- Negated residual: retain absence of that strengthened payload, but emit it
  to a named successor with a typed trigger rather than ending the branch.
- Re-entered methodology: target-test equivalence, legal payload exit, and
  leaf totality.
- Complete audit rerun after repair: no.

Node `[48]` must remain non-green at this revision.
