# Red-team audit: node [131] Boolean-product repair

## Baseline

- Repair sketch: `proofs/erdos_64_eg/repairs/node_131_boolean_product_branch.tex`
- Original manuscript baseline: `4e7db39e6bc8defa1a5150b912eba4fe0208d09289db4cfdddf8f8b9d2fa7680`
- Failed node: `[131]`
- Failed claim: admitted-quotient label injectivity entails simultaneous realization of every mixed Boolean response vector.
- Methodology used: branch-state reconstruction, both-sides test, rejection of
  the CT10–CT15–CT6 first-conflict candidate, CT9 total anchor-token
  accounting, typed handoff and dependency-cone checks, S-Rout/S-Trig.
- Verdict: **PASS for the node-[131] routing repair**. The Boolean-product
  implication is removed from the Part-X route; downstream nodes `[134]` and
  `[143]` remain independent proof-frontier consumers.

## Provenance matrix

| Used fact | Producer | Earlier on this path? | Independent of defect? | Verdict |
|---|---|---:|---:|---|
| Sparse upper envelope and slack identity | nodes `[125]`–`[126]` | yes | yes | usable |
| Full active surplus family and activation supports | nodes `[127]`–`[128]` | yes | yes | usable |
| Baseline independently target-testable family | node `[129]` | yes | yes | usable as the initial prefix |
| Pair-local blocker partition | node `[130]` | yes | yes | usable |
| Admitted-quotient label injectivity | current CT15 quotient profile | yes | yes | usable only as quotient injectivity |
| Complete mixed Boolean realization | no producer | no | no | unavailable |
| Near-cubic spine | node `[138]`, downstream of `[131]` | no | no | forbidden in repair |
| Type B fan-mass bound | nodes `[75]`, `[84]`, using near-cubic spine | no | no | forbidden as generic handoff closure |
| Exact all-pair anchor partition | `CT9.AnchoredPairLedger.noOvercounting` | yes: consumes node `[130]` schedule | yes | verified |
| Anchor-token supply equals `σ(G)` | `allPairAnchor_tokenSupply_eq_sigma` | yes: node `[127]` slot count | yes | verified |
| Anchor fibres are stars | `allPairAnchor_sameAnchor` | yes | yes | verified bookkeeping only |

## Quantifier attack

| Claim | Literal form | Countermodel | Result |
|---|---|---|---|
| Quotient labels survive | every response-preserving identification code is injective | response set `{00,01,10}` | true |
| Each coordinate takes both values | `∀ c, ∃s₀, val s₀ c = 0 ∧ ∃s₁, val s₁ c = 1` | response set `{00,01,10}` | true |
| Full cube is realized | `∀ ε, ∃s, val s = ε` | assignment `11` | false |
| Missing vector gives functional coordinate dependence | one coordinate is a function of a proper coordinate subset | response set `{00,01,10}` | false |

The finite countermodel is checked by:

- `StructuralExhaustion.Examples.BooleanStateEntropy.everyContext_responsePreservingCode_injective`
- `StructuralExhaustion.Examples.BooleanStateEntropy.true_true_not_realized`
- `StructuralExhaustion.Examples.BooleanStateEntropy.responsePreservingInjectivity_does_not_realize_cube`

## Both-sides audit

- Positive side: a uniform, prefix-preserving one-coordinate extension operation composes by finite induction into complete mixed realization. This is valid and does not enumerate assignments.
- Negative side: the least failed extension is a finite positive residual.
- Measurability: the ordered coordinate scan and remaining-coordinate measure are valid.
- Blocking issue: the current graph API has no theorem classifying a failed extension as an existing sparse-exit payload or an admitted blocker with a capacity token.
- No theorem was weakened and no realization assumption was added.

## CT obligations

| CT block | Trigger | Unfilled schema | Verdict |
|---|---|---|---|
| CT10 | next scheduled response coordinate | none for scheduling | pass |
| CT15 | target-relative extension/full-realization datum | the current admissible-quotient profile tests pair-identifying quotient injectivity, not Boolean extension rank | blocking |
| CT6 | first failed extension | requires a locally decidable extension audit and retained bounded failure certificate | blocking |
| CT3/CT7/CT16 handoff | target defect, exchange/compression, or whole-support type | no map from the first failed extension to any exact payload | blocking |
| CT4/CT9 blocker route | admitted blocker, canonical token, role | no map from the first failed extension to the existing blocker/token types | blocking |

## Reused closed branches

| Handoff | Exact trigger proved from the repair residual? | State transported | Dependency cone | Verdict |
|---|---:|---:|---|---|
| target-defect sparse exit | no | pre-`[131]` state is sufficient if trigger exists | independent | not yet legal |
| proper compression sparse exit | no | pre-`[131]` state is sufficient if representative exists | independent | not yet legal |
| proper/closed delocalization | no | pre-`[131]` state is sufficient if determination certificate exists | independent minimality closure | not yet legal |
| suppression arithmetic exit | no | pre-`[131]` state is sufficient if cycle certificate exists | independent | not yet legal |
| existing blocker ledger | no new blocker/token constructed | exact state can be transported | downstream but compatible with repaired partition | not yet legal |
| curvature rank-drop closure | no; functional dependence is not implied | n/a | route itself is earlier, trigger absent | illegal |
| Type B fan-mass closure | no | would require near-cubic data unavailable here | returns transitively through node `[131]` | circular |
| node `[138]` near-cubic closure | no | n/a | direct descendant of `[131]` | circular |
| HSS target closure | no induced-`P₁₃`-free minimum-degree-three object constructed | n/a | independent | not yet legal |

## Leaf totality and practicality

| Leaf | Certificate | Practical checker | Verdict |
|---|---|---|---|
| all extensions succeed | uniform constructor proof | one symbolic fold over the coordinate schedule | pass |
| failed extension gives sparse exit | missing classifier | intended local support check | blocking |
| failed extension gives admitted blocker/token | missing classifier | intended local support and token check | blocking |

- Largest intended executable universe: the existing ordered pair schedule.
- Ambient complexity: polynomial in the graph order and retained certificate sizes.
- Boolean assignments are not enumerated.
- Labelled graphs, outside contexts, paths, and subgraphs are not enumerated.
- Re-entry measure: number of unprocessed pair coordinates; strict decrease is proved once each failed coordinate is routed.

## Second-iteration audit: all-pair anchor tokens

The first-conflict candidate is rejected rather than retained as an unproved
lemma. The replacement candidate assigns every canonically ordered pair to
its first activated surplus slot.

| Claim | Formal source | Audit result |
|---|---|---|
| every pair receives exactly one anchor | CT9.AnchoredPairLedger.noOvercounting | pass |
| the token universe has size sigma(G) | allPairAnchor_tokenSupply_eq_sigma | pass |
| one token fibre is a literal star | CT9.AnchoredPairLedger.same_anchor_of_mem_fibre | pass |
| pair generation is polynomial | CT9.AnchoredPairLedger.pairCount_le_square | pass |
| bounded fibres imply a near-cubic bound | elementary choose(sigma,2) versus L sigma comparison | pass |
| every overloaded anchor star has a legal consumer | no producer theorem | blocking |

The transfer fixture
StructuralExhaustion.Examples.CT9AnchoredPairLedger verifies the new CT9
contract independently of the Erdős problem. Focused builds pass.

### Both-sides test

- Bounded side: if every anchor fibre has size at most a fixed L, the exact
  ledger yields choose(sigma,2) at most L sigma, hence sigma at most 2L+1
  when sigma is positive.
- Overloaded side: CT9 returns a concrete finite star of scheduled pairs with
  a common first surplus slot. This residual is measurable and local.
- Consumer failure: the existing blocked-token route additionally requires a
  canonical blocker, blocker capacity token, and blocker role. A free member
  of the anchor star supplies none of those fields.
- Type B failure: the existing decorated handoff requires a connected
  negative induced-P13-free remainder core, an exterior high decoration,
  first-entry arms, pairwise fan safety, context safety, forbidden-freeness,
  core-freeness, and uncompressibility. Common anchor equality supplies none
  of these fields.
- Circular route rejected: the generic Type B bridge-mass bound consumes the
  near-cubic estimate whose producer is downstream of node [131].

### Attack on the manuscript same-token consumer

The current prose for parallel and cubic first-separator germs is not a legal
consumer for the new overload residual. It infers a proper compression from a
target-complete coordinate identification. The repository definition of an
admissible rank quotient instead requires a certified strictly smaller
representative. No such representative is constructed from
target-completeness. Therefore importing that prose would repeat the original
quotient-versus-realization error in a different form.

## Findings

### Blocking

1. Prove a graph-owned **sparse pair product-or-route theorem**. From a realized mixed prefix, the next pair-response coordinate, an arbitrary prefix assignment, and a requested bit, it must either construct a prefix-preserving state extension or construct the exact payload of an upstream sparse exit or the exact admitted blocker/token payload consumed by the existing ledger.
2. Prove exhaustiveness of that classifier from the exact activation and pair-support data already present before node `[131]`.
3. If the negative output needs a new blocker kind, prove a linear-size token supply and the corresponding overload closure at Graph/Core/Routes level, with a non-Erdős transfer example. Merely naming `realizationConflict` is not sufficient.
4. The second iteration discharges the linear token-supply and exact-ledger
   portions of item 3. Its remaining blocking leaf is the concrete
   blocker-free anchor-star overload. No registered consumer accepts that
   payload, and adding the missing Type B fields to the payload would be an
   assumption rather than a derivation.

### Required cleanup

None before the mathematical blocker is resolved; the original manuscript correctly remains unchanged during this repair attempt.

### Advisory

The successful sequential-extension lemma should eventually live in Core, and the product-or-first-conflict runner should live in CT15/Routes rather than in the Erdős example.

## Verdict after repair iteration 2

**FAIL after repair iteration 2.** The first-conflict candidate has been
replaced, not carried. The exact residual is now an overloaded finite star of
actual scheduled surplus pairs with one common first activated slot.

The reusable CT9 ledger, exact `σ(G)` token supply, star-fibre theorem,
quadratic work bound, and non-Erdős transfer fixture are all verified. The
remaining leaf has no legal existing consumer: blocker-free star membership
does not construct a canonical blocker, and it does not construct the
negative-core and fan-safety fields of the Type B entry.

For historical clarity, the rejected first-iteration target was

```text
failed prefix-preserving extension of r_π
  -> sparse-exit payload OR admitted blocker + canonical capacity token
```

It is no longer the selected invariant. The source manuscript remains frozen;
routing directly to Type B fan-mass or node `[138]` would be circular, and
treating either Boolean realization or decorated Type B data as input would
add an assumption.

## Third-iteration audit: free-anchor route

The selected invariant is now the exact total pair token route. A canonically
oriented free pair `(p_i,p_j)`, `i<j`, is assigned to the already existing
primitive selected-port token `p_i` with the distinct role `freeAnchor`.
Blocked pairs retain their canonical first blocker and enter the existing
capacity-token computation at node `[134]`.

| Obligation | Formal witness | Result |
|---|---|---|
| every scheduled pair occurs once | `SurplusPairTokenRouting.noOvercounting` | pass |
| dispatch does not assume a blocker | `free_role`, `free_of_role_eq` | pass |
| blocked dispatch does not invent a token subtype | `blocked_role`, with the four admitted structural kinds in `PairRouteRole` | pass |
| free fibre has the claimed primitive token | `fields_of_mem_fibre`, `freeAnchorFibre_member_first` | pass |
| every free-fibre member is genuinely blocker-free | `freeAnchorFibre_member_is_free` | pass |
| retained pair connector is transported | `FreeAnchorMember.connector`, `firstGamma_subset_connectorSupport`, `secondGamma_subset_connectorSupport` | pass |
| blocked branch retains the complete first hit | `blocked_retains_canonical_blocker` | pass |
| finite role alphabets are exact | `pairRouteRole_card = 5`, `totalRole_card = 25` | pass |
| local cap aggregation is framework-owned | `CT9.TokenRoleLedger.bounded_total` | pass |
| executable work is local and polynomial | `checks_eq`; previous pair schedule is at most `n^4` | pass |
| transfer independent of Erdős data | `Examples.CT9TokenRoleLedger` and `Examples.SurplusTokenRole` | pass |

### Both-sides test

- Positive blocker decision: the item carries the canonical first-hit record,
  including failure of all earlier candidates, and routes to `[134]`.
- Negative blocker decision: the item carries no blocker field. Its first
  selected port is an element of `P_exc ⊆ T_prim`, so the complete CT9 fibre
  is the exact primitive selected-port input of `[143]`.
- The alternatives are exhaustive because they are the two constructors of
  the decidable blocker scan; no realization, near-cubic, or Type-B premise is
  added.

### Dependency and circularity attack

The free route consumes only the activated slot schedule, the canonical
blocker decision, and the shortest connector retained for a free pair at
`[130]`. It does not consume `[138]`, a near-cubic bound, or any Type-B
fan-mass theorem. Node `[143]` is a downstream residual audit, not a fact used
to construct the route. Its later fixed-cap outcome may route to `[138]`; that
direction is acyclic. The Type-B fan ledger may be entered only after the
geometric audit constructs its complete handoff payload.

### Quantifier and assumption attack

The route contains no Boolean assignment and asserts no joint realization.
`freeAnchor` is definitionally the false side of `HasBlocker`; it is not a
named hypothesis. A blocked pair is labelled initially only by its actual
canonical blocker kind. The later token subtype is computed by the existing
capacity-token map, so no fictitious `primitivePort` label is carried.

### Practicality

CT9 filters the authored ordered pair list by the product label. There are
five dispatch roles, and the final combined role alphabet has 25 elements.
No graph, subgraph, path family, context family, quotient family, or Boolean
cube is materialized. The retained connector is reused instead of searched
again.

## Current verdict

**PASS for merging the node-[131] route.** The exact local leaves are typed
handoffs to `[134]` and `[143]`; neither leaf is silently treated as a theorem
or as closed. This audit does not mark the downstream primitive geometric
closure `[144]` verified. It establishes that the Boolean-product gap no
longer lies on the Part-X accounting path and that its replacement route is
unconditional, local, polynomial, and acyclic.
