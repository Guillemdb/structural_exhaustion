# Red-team audit: node [172] owner-block dichotomy

## Baseline

- Repair sketch: `node172_owner_block_dichotomy.md`.
- Original manuscript baseline: Git `164ac892da194510c119e4dc95c6ce1705df5445`;
  SHA-256 `fbd3c423e68150f12cd896589d42e6b8791fb0c4a2453de7dabe8e35175b18bc`.
- Failed node and claim: proposed node [172], after the verified node-[171]
  cross-window token-pair handoff.
- Methodology consulted: repair protocol, typed residual and no-unnamed-
  residual rules, S-Def/S-Dich/S-Rout/S-Trig/S-Comp/S-Meas, and the
  red-team checklist.
- Verdict: **FAIL**. The sketch is correctly marked not merge-ready.

## Provenance matrix

| Used fact | Producer | Earlier and independent? | Verdict |
|---|---|---:|---|
| normalized simple return and support bound | [167]--[168] | yes | pass |
| exact stored owner and position at every return index | [169] owner table | yes | pass |
| at least one owner change and its exact opposite tokens | [169]--[171] | yes | pass |
| pairwise-disjoint selected-window supports | selected packing profile | yes | pass |
| induced literal `P13` internal path | selected-window embedding | yes | pass |
| cold-family membership, density, successor, D4--D7 | no producer | explicitly excluded | pass |

The eventual Lean input must retain the actual node-[169] table and equality
with the node-[171] run. The current node-[171] adapter is a dependent run,
not yet a `result + runExact` computed wrapper; node [172] must introduce that
wrapper or accept both the exact predecessor and its run equality.

## Quantifier attack

| Claim | Literal form and attack | Result |
|---|---|---|
| least repeated block | least `b` with `exists a < b, omega_a = omega_b` | valid; minimality makes the prefix pairwise distinct and hence makes `a` unique |
| repeated owner forces target | repeated owner implies a connector cycle, not a dyadic length | false shortcut correctly rejected; length `3` is a countermodel |
| all-distinct closes | pairwise-distinct finite owner list implies only a bounded survivor | no closure follows; sketch correctly retains a residual |
| owner equality realizes a response state | equality is only identity of stored packing owners | no Boolean/context realization is claimed |

No injection/surjection, pairwise/simultaneous, rank/Boolean-cube, or context-
generator exchange occurs in the stated repair.

## Geometry audit of the repeated-owner cycle

For the least repeated pair `a < b`, minimality implies that no block strictly
between `a` and `b` has owner `W`. Thus the internal vertices of
`Gamma'[e_a .. s_b]` do not have owner `W`. Every vertex of the selected
window segment does have owner `W`; owner uniqueness therefore gives interior
disjointness. Path simplicity gives distinct endpoints and embedding
injectivity gives `alpha != beta`, hence the internal distance lies in
`{1,...,12}`. Since equal owners cannot occur in consecutive maximal blocks,
`s_b-e_a >= 2`; therefore the connector length is at least three. With
`L+1 <= Q_base`, the upper bound `L+12 <= Q_base+11` is correct.

One statement is not yet construction-ready: both the return segment and the
window segment are described from the first endpoint to the second. A closed
walk requires one of them reversed. The reusable constructor must specify,
for example,

```text
Gamma'[e_a .. s_b] ++ reverse(P13[alpha .. beta])
```

and prove endpoint typing, adjacency at both concatenation points, simplicity,
interior disjointness, and the exact additive length. This is a blocking
S-Def/S-Comp obligation until formalized; an unoriented union is not yet a
Lean cycle certificate.

## Branch and invariant audit

- Positive account: a literal connector cycle, followed by an exact dyadic
  test and CT1 certificate execution.
- Negative witnesses: exact non-dyadic connector payload or exact pairwise-
  distinct owner-block chain.
- Measurability: one bounded return; proposed block and repeat scans are local.
- Cross-branch leakage: none found.
- Theorem weakened or assumption added: none.
- No cold, Boolean-realization, density, demand, capacity, or successor fact
  is imported.

The all-distinct payload promises opposite tokens at **every** block boundary,
whereas current node [171] supplies only the first boundary pair. The data are
derivable from the stored owner table, path adjacency, packing disjointness,
and slot positions, but a reusable `CrossWindowTokensAt` constructor for an
arbitrary distinct-owner consecutive edge is missing. `FirstCrossWindow.ofFirstHit`
cannot simply be reused for later boundaries because its input is a first-hit
record. This missing producer is blocking for the stated all-distinct payload.

## CT obligations

| Branch | Trigger | Missing obligation | Verdict |
|---|---|---|---|
| repeated, dyadic | explicit simple cycle with `PowerOfTwoLength` | oriented cycle constructor and exact CT1 adapter | blocking until Lean proof; route itself is standard |
| repeated, non-dyadic | exact cycle, rejected length, offset `1..12` | R1 route, R2 compatibility trigger, R3 total CT17 survivor consumers | blocking |
| all distinct | exact bounded block chain and boundary descriptors | D1 payload, D2 total class table, D3 CT10 trigger/locality, D4 transfer | blocking |

The proposed CT17 and CT10 handoffs have no admitted dependency cones yet, so
acyclicity and consumer totality cannot currently be certified. They must not
be queued merely because their payloads are bounded.

## Leaf totality

| Leaf | Certificate or consumer | Checker | Verdict |
|---|---|---|---|
| dyadic connector | CT1/C1 | one supplied cycle check | pending the exact cycle constructor |
| non-dyadic connector | proposed CT17 payload | bounded locally, but R1--R3 absent | fail |
| all-distinct chain | proposed CT10 payload | bounded locally, but D1--D4 absent | fail |

The repair is therefore not leaf-total. This alone forbids a PASS or manuscript
merge.

## Practicality and termination

- Largest intended universe: the owner-block list of one supplied return,
  of length at most `Q_base`.
- Work: one linear block pass and at most `K(K-1)/2` stored-owner comparisons.
- Memory: linear in the one return.
- Termination: finite list traversals; no re-entry.
- Hidden global computation: none proposed.

The eventual Lean runner must expose the actual maximal-block builder, least-
repeat selector, equality decider on stored owner identities, exact check
ledger, and reference-result theorem. Statements of `O(L^2)` alone are not an
executable contract.

## TeX--Lean--framework correspondence

- The source manuscript remains unchanged and still stops at the verified
  [169]--[171] scope boundary.
- The repair is a separate worksheet and correctly disclaims theorem status.
- Generic ownership is proposed correctly in Graph/Routes/CT layers, but no
  node-[172] Lean contract exists yet.
- No transfer example exists yet for either new residual route.
- No new `sorry`, `admit`, unsafe declaration, or axiom is introduced by this
  Markdown-only sketch.

## Findings

### Blocking

1. R1--R3 are open: the non-dyadic leaf has no admitted, total CT17 consumer.
2. D1--D4 are open: the all-distinct leaf has no admitted, total CT10 consumer.
3. The literal cycle needs an oriented concatenation theorem with endpoint,
   adjacency, simplicity, interior-disjointness, and length proofs.
4. The all-distinct payload lacks a producer for exact opposite tokens at
   every later owner-change boundary.
5. The exact node-[171] computed-run wrapper and executable block/repeat
   runner with a checked work ledger are not yet defined.

### Required cleanup

- Register producer/consumer payload signatures and audit dependency cones
  before queuing either residual.
- Add non-Erdős fixtures exercising repeated, all-distinct, dyadic, and
  non-dyadic outcomes of the exact reusable contracts.

### Advisory

- State `L` consistently as edge length, so support size is `L+1`.
- Name the reversed window subpath explicitly in the worksheet.

## FAIL disposition

- Exact obligation returned to the repair loop: first construct the oriented
  simple connector cycle and the arbitrary-boundary token producer; then
  implement and totalize R1--R3 and D1--D4.
- Negated residual: non-dyadic connector and all-distinct owner chain remain
  honest typed candidates, not closing certificates.
- Methodology re-entry: S-Def/S-Comp for the cycle, followed by S-Rout/S-Trig
  and leaf-totality for CT17 and CT10.
- Complete audit rerun after repair: no; this audit records the current FAIL.

