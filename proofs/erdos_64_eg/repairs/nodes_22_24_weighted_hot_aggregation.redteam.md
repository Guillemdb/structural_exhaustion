# Red-team audit: nodes [22]--[24] weighted-hot aggregation

## Baseline

- Repair sketch:
  `proofs/erdos_64_eg/repairs/nodes_22_24_weighted_hot_aggregation.repair.md`,
  SHA-256
  `1fc5aaf0d3159f58ec0d849b1fcc8cbba570179e063ce483d1eb2094cbd21050`.
- Lean interface:
  `examples/erdos_64_eg/Erdos64EG/P13WeightedHotColdInterface.lean`,
  SHA-256
  `0c9c8cc245d0225e59064b9b1970ba1c7ef49532df7c2df1ab0024d6f90daf2a`.
- Original manuscript baseline:
  `original_erdos_64_proof.tex`, SHA-256
  `215248521b7dbc6519076d506101b80a1c9a8425ee5c13b48a4ec52df21d2e10`.
- Failed block: the product of the exact weighted-hot state counts is
  presented as one independently target-testable family bounded by the
  labelled skeleton family.
- Methodology consulted: the both-sides test and repair protocol in
  `framework/branch_closure_methodology_extended.tex`, the full red-team
  checklist, the original `lem:p13-window-package`,
  `lem:hot-failure-cold-mass`, and `prop:p13-density`, and the current Core,
  Graph, and Erdos declarations named below.
- Current verdict: **FAIL**.  The one-window conditional-fibre theorem and
  the pure hot/cold arithmetic are sound.  The graph-owned aggregate
  producer, its negative routes, and the exact `118.108581006` rate are not
  proved.

The original manuscript was not edited during this audit.

## Provenance matrix

| Used fact | Producer | Earlier on this path? | Independent of defect? | Verdict |
|---|---|---:|---:|---|
| Exact duplicate-free selected packing | CT12 packing prefix | yes | yes | available |
| Exact hot/cold partition | `p13WeightedHotCount_add_coldCount` | yes | yes | available |
| Same selected window on either side | `classifyP13WeightedWindow_window` | yes | yes | available |
| Positive scale multiplicity and fixed scale loss | fields of `P13WeightedLiveWindowPackage` | yes | yes | available in a supplied package |
| Exact repeated safe and flat products | `UniformFiniteFibreProduct.mapped_prod_eq_finEnum_prod_pow`, then `safeProductExact`/`flatProductExact` | yes | yes | derived from the multiplicity ledger |
| One-window product inequality | `P13WeightedLiveWindowPackage.product_le` | yes | yes | proved |
| More than 118 bits per retained scale | `stateCount_gt_ratePower` | yes | yes | proved |
| More than `118.108581006` bits per retained scale | none | no | n/a | **missing** |
| Graph interpretation of every weighted state | none in the weighted package | no | n/a | **missing** |
| Full support of every interpreted state | none in the weighted package | no | n/a | **missing** |
| Cross-window glue and recover maps | node-[160] has a different conditional package | no for this route | n/a | **missing** |
| Aggregate target-response commutation | node-[160] has a conditional response theorem | no for this route | n/a | **missing** |
| Injection into the exact skeleton family used at node [24] | only conditional analogues at nodes [48]/[52] | no | n/a | **missing** |
| Hot failure payment once a hot bound is supplied | `p13WeightedHotBudget_total_le_budget_add_cold` | yes | yes | proved |
| Strict overflow forces a cold entry once a hot bound is supplied | `p13WeightedHotOverflow_forces_cold_nonempty` | yes | yes | proved |

## Audit of the exact local products

The product identities are constructible from the manuscript's barrier
multiplicity ledger; they need not be proof-injected package obligations.
During this audit the reusable theorem
`Core.UniformFiniteFibreProduct.mapped_prod_eq_finEnum_prod_pow` was added.  It
proves that, when every member of an exactly enumerated finite owner type
occurs exactly `m` times in a supplied coordinate list, multiplying an owner
weight over the coordinates equals the product of all owner weights raised to
`m`.  Its proof compares finite lists by exact counts and never constructs a
Cartesian state family.

Accordingly, `safeProductExact` and `flatProductExact` were removed from
`P13WeightedLiveWindowPackage` as fields and reintroduced as theorems derived
from `profileExact`, `barrierMultiplicity`, and the exhaustive 91-barrier
enumeration.  The barrier multiplicity field requires every barrier to occur
`scaleMultiplicity` times.  The key injectivity field separately prevents a
barrier/scale pair from being counted twice, and positivity rules out the old
empty-coordinate countermodel.

The theorem `stateCount_gt_ratePower` is also sound.  Explicitly, it proves

```text
2^(118 * scaleMultiplicity) < profile.states.values.length.
```

It uses the verified strict inequality

```text
2^118 * p13BarrierFlatProduct < p13BarrierSafeProduct,
```

raises it to the positive multiplicity, composes it with the complete-ledger
product inequality, and cancels the positive repeated flat product.  It does
not use Boolean realization or enumerate a product state space.

This theorem is nevertheless weaker than the rate consumed by nodes
[22]--[24].  The density predicate uses

```text
p13WindowDensityRateNumerator = 118108581006
```

at denominator `10^9`, whereas the current theorem exports only the integer
floor `118`.  No current theorem certifies an exact comparison equivalent to

```text
log2(p13BarrierSafeProduct / p13BarrierFlatProduct)
  >= 118108581006 / 10^9.
```

Consequently the local rate theorem cannot by itself prove the exact node-[24]
cap even after cross-window aggregation is supplied.  This is a separate
blocking numerical obligation, not part of the commutation proof.

### Exact numerical certificate design

Writing `A = p13BarrierSafeProduct` and
`B = p13BarrierFlatProduct`, the exact missing inequality is

```text
A^1000000000 > 2^118108581006 * B^1000000000.
```

Materializing either side is impractical: the result has tens of billions of
bits.  A practical kernel checker can instead use a fixed-point repeated-square
certificate for `A / (2^118 * B)`.  With denominator `D = 10^40`, set

```text
L0 = floor(A * D / (2^118 * B))
   = 10781672600910877398201228224441972344885.
```

For 34 steps, store one bit `q_i` and one bounded numerator `L_(i+1)` and
check only

```text
D * 2^q_i * L_(i+1) <= L_i^2.
```

The deterministic candidate shift word is

```text
0001101111001011111101101111111000
```

and its accumulated exponent under `K_(i+1) = 2*K_i + q_i` is
`K_34 = 1865407480`.  The final comparison has positive integer margin

```text
10^9 * K_34 - 108581006 * 2^34 = 1052880896.
```

Thus a generic rational repeated-square soundness theorem plus 35 bounded
integer checks would certify the exact printed rate without computing a giant
power or invoking real logarithms.  This audit did not add that generic
soundness theorem, so these candidate values are a checker design, not Lean
evidence and not permission to use the exact rate downstream.

## Quantifier attack

| Claim | Literal quantified form | Smallest countermodel or attack | Result |
|---|---|---|---|
| One complete weighted package has the stated integer state loss | for one supplied package, its stored state-list length exceeds `2^(118*m)` | checked algebraically against positive `m` and positive flat product | pass |
| Local state count is a count of target-complete graph states | every listed state has a graph completion, target semantics, and an injective graph code | take two abstract states with distinct connector functions but no graph interpretation field | **not implied** |
| Vertex-disjoint windows commute | arbitrary connector/support changes at one window preserve all responses owned by another | two disjoint window cores may use the same outside connector vertex or edge | **false without complete-support control** |
| Pairwise support compatibility gives one global state | every pair can be glued implies every finite owner family can be glued | three local assignments with pairwise-compatible but jointly inconsistent shared boundary data | **false in general** |
| Injective restriction realizes all local tuples | every aggregate state restricts injectively into local states, therefore every local tuple occurs | the diagonal family `{(0,0),(1,1)}` injects into `{0,1}^2` but omits `(0,1),(1,0)` | **false** |
| Recover after glue gives a product injection | a glue map is defined for every dependent local choice and every coordinate is recovered | direct equality argument | pass, but no such weighted glue exists |
| Distinct global graphs give distinct skeletons | the skeleton code retains the complete labelled edge set in the counted family | a code retaining only a fixed baseline subset can identify completions differing outside it | requires an exact edge-set code theorem |
| 118 integer bits proves the printed density constant | `118108581006 * p13 <= 1500000000*n` follows from a `118`-bit payment | `1.5/118 > 1.5/118.108581006` | **false** |

The repair sketch correctly avoids the injection-to-realization error in its
prose, but its proposed field `injective restriction map from aggregate states
to the tuple of local hot-window states` is insufficient for the product lower
bound.  The required direction is a total `glue` map defined on every exact
dependent local tuple, together with `restrict (glue choice) owner = choice
owner`.  Recoverability then proves injectivity of `glue`.  Merely injecting an
already chosen aggregate family into the local product gives an upper bound.

## Minimal graph-owned producer

The smallest adequate positive producer should not introduce a separately
enumerated Cartesian carrier.  It should store:

1. the exact duplicate-free hot list;
2. for every hot entry, an interpretation of every state in that entry's
   existing `package.profile.states.values` as a local graph completion;
3. the complete finite support of that interpretation, including the window,
   connector, response-test, and modified-edge supports;
4. a deterministic ownership rule for every overlap of two such supports;
5. a dependent `glue` function defined for every choice of one listed state
   per hot entry;
6. a `restrict` function and `recover` theorem for every owner;
7. preservation of the original graph outside the union of the selected
   supports and preservation of each owner's response under `glue`;
8. baseline and target semantics for every glued object;
9. an exact labelled-edge-set skeleton code for the glued object and
   injectivity of that code on glued choices; and
10. an exact finite capacity theorem for the code family actually used by
    node [24].

Items 5--6 prove product injectivity without scanning the product.  Items 3--4
are the genuine cross-window graph lemma.  Items 7--9 are the target and
skeleton semantic bridge.  Vertex-disjointness of the thirteen path vertices
discharges none of items 3--4 because the stored connectors may meet outside
the window.

### Existing declarations that can be reused

- `P13Node160LocalGraphCompletion` already gives a useful graph-owned local
  completion shape with a declared support and outside-support preservation.
  It is not indexed by a weighted package state and therefore does not
  discharge the new producer.
- `P13Node160RealizationPackage` already states `glue`, `restrict`, `recover`,
  support commutation, outside preservation, and response commutation.  It
  additionally assumes realization of every 91-bit assignment and is not a
  producer from the weighted hot list.  It is a model for the required field
  directions, not evidence that those fields exist here.
- `Graph.PackedBoundariedGluing` proves exact adjacency and target-preservation
  lemmas for one owned piece plus one compatible outside context.  The missing
  theorem is a finite many-piece owned-partition construction for the exact
  hot supports, including overlap classification.  The one-piece theorem
  cannot be iterated until disjointness or a canonical overlap invariant is
  proved.
- `Core.FiniteJointCapacity` proves a two-schedule product capacity from an
  injective code without materializing pairs.  It can be generalized or
  folded after the many-window glue/code theorem exists; it does not construct
  the code.
- `P13CurvatureProductCostRealization.states_length_le_baseline` shows the
  right pattern for turning a duplicate-free graph-owned skeleton code into a
  capacity bound.  Its context and state family are node-[48] data, not the
  weighted window product.
- `P13Node52JointAccountingRealization` packages a conditional two-family
  glue and injective skeleton code.  It explicitly leaves the analogous
  semantic producer open and therefore cannot discharge node [22].

No existing Core or Graph declaration proves `hotSupport_owner_or_overlap`,
`hotResponse_commutes`, or the weighted aggregate skeleton injection.

## Branch and invariant audit

- **Positive payment:** valid only after the many-window glue, recover,
  response, and skeleton-code producer is constructed and the exact decimal
  rate is certified.
- **Negative side:** the repair sketch names support ownership, response
  commutation, target soundness, and skeleton-code collision residuals.  It
  does not yet construct canonical first witnesses or prove the listed CT
  triggers.
- **Measurability:** a support-overlap scan is local and polynomial once every
  weighted state has one supplied finite complete support.  Such supports are
  not fields of the current weighted package.
- **Cross-branch leakage:** routing every support collision directly to the
  cold F1--F5 branch is unjustified.  A collision is not package absence and
  may involve two individually hot windows.  It requires its own typed
  overlap residual and a proved adapter to an F branch.
- **Theorem weakening:** no theorem is weakened, but treating an aggregate
  package or its hot bound as a caller assumption at a public node would move
  the missing conclusion into the hypotheses.

## CT and route obligations

| Residual | Available trigger | Missing contract | Verdict |
|---|---|---|---|
| Support ownership failure | none; no weighted support exists | first collided owner/state/support incidence and adapter to an exact F case | blocking |
| Response commutation failure | no aggregate response evaluator | concrete two-owner state change plus CT3/CT7 compatible context | blocking |
| Target soundness failure | no glued target semantics | exact target defect or target-cycle certificate | blocking |
| Skeleton-code collision | no weighted skeleton code | concrete two-choice collision and CT9/CT10 refinement trigger | blocking |
| Aggregate success | local state lower bounds only | total dependent glue, recovery, graph semantics, injective exact code | blocking |
| Hot budget plus overflow | exact natural-number inequalities | none after `hotBound` is proved | pass |

The CT names in the sketch are destinations, not yet verified handoffs.  In
particular, a skeleton collision does not automatically satisfy a CT9 label
overload or a CT10 promotion rule.

## Leaf totality

| Leaf | Exact current certificate | Practical local checker | Verdict |
|---|---|---|---|
| One hot window pays integer 118-bit rate | complete ledger and `stateCount_gt_ratePower` | local shrinking-fibre scan | pass |
| Exact-rate `118.108581006` payment | none | none | blocking |
| All weighted hot windows glue | none | none | blocking |
| First ownership failure | prose tag only | support scan cannot run without supports | blocking |
| First response failure | prose tag only | no aggregate evaluator | blocking |
| First skeleton collision | prose tag only | no aggregate code | blocking |
| Valid hot bound and strict total overflow | `p13WeightedHotOverflow_forces_cold_nonempty` | arithmetic only | pass |

## Practicality and termination

- Largest current enumeration: one supplied local state list times its
  supplied coordinate list.  The theorem scans only shrinking local fibres.
- Proposed acceptable scan: sum of local state/coordinate checks plus a
  polynomial pair scan over declared finite supports and owners.
- Forbidden scan: the dependent product of all hot state lists, all graph
  completions, all contexts, or all Boolean assignments.
- A code injectivity proof is a certificate and may be checked without
  materializing the product, as in `Core.FiniteJointCapacity`.
- No cycle or decreasing measure has yet been defined for overlap failures
  routed into F1--F5, so that proposed return edge is not yet admitted.

## TeX--Lean--framework correspondence

- The derived local product theorems match the repeated safe/flat products in
  `lem:p13-window-package` only conditionally on a supplied hot package.
- `stateCount_gt_ratePower` matches a strict integer 118-bit lower bound, not
  the manuscript's displayed `c13 = 118.108581006...` rate.
- The manuscript sentence “distinct packed windows are vertex-disjoint” does
  not match a Lean theorem about disjoint complete tester supports.
- The manuscript's product-of-target-complete-states sentence has no weighted
  Lean counterpart.
- Generic ownership is otherwise appropriate: conditional-fibre arithmetic
  is in Core, one-piece gluing is in Graph, and Erdős-specific constants and
  response meanings stay in the application.
- No scoped `sorry`, `admit`, `axiom`, or `unsafe` declaration was found.
- The only trust-sensitive finite facts used by the local theorem are the
  existing audited node-[21] table and Lean's kernel-checked arithmetic.

Focused build:

```text
lake build Erdos64EG.P13WeightedHotColdInterface \
  Erdos64EG.P13PartIWindowDensityTriage
```

passes, with only pre-existing unused-variable warnings.

## Findings

### Blocking

1. **Wrong injection direction in the proposed aggregate fields.**  An
   injection from aggregate states into local tuples does not yield the
   product lower bound.  A total dependent `glue` plus componentwise recovery
   is required.
2. **Weighted graph interpretation absent.**  The local weighted state type
   has connector semantics but no graph completion, complete support, or
   target semantics.
3. **Complete-support commutation absent.**  Disjoint window cores do not
   imply disjoint outside connector/test supports.
4. **Skeleton injection absent.**  Existing node-[48]/[52] code declarations
   are conditional and concern different state families.
5. **Exact rate absent.**  The implemented `118`-bit theorem does not prove
   the `118.108581006` density numerator.
6. **Negative routes are not typed consumers.**  None of the proposed first
   failures currently constructs the exact F, CT3, CT7, CT9, or CT10 trigger.

### Required cleanup

1. Replace “injective restriction map” in the repair sketch by total
   dependent glue plus componentwise recovery, and derive glue injectivity.
2. Split the numerical exact-rate obligation from the graph commutation
   obligation in the missing-lemma ledger.
3. Do not call an overlap of two individually live packages a cold window
   until a typed adapter proves the exact cold-corridor trigger.
4. State explicitly whether the skeleton family has exactly the baseline edge
   count or a near-cubic surplus allowance.  The code type must match the
   budget used in node [24].

### Advisory

- `Core.FiniteJointCapacity` is the right no-product-enumeration model for the
  final capacity proof, but the many-window graph code should be proved before
  choosing whether to generalize it or fold it.
- The current local theorem should remain: it is a useful and correct integer
  floor certificate even though it is not the final density rate.

## FAIL disposition

- Exact obligation returned to the repair loop: for the exact weighted hot
  list, define graph interpretations and complete supports; classify the first
  support overlap; on the no-overlap side construct total dependent gluing,
  prove component recovery and response preservation, and inject the glued
  objects into the exact node-[24] skeleton family.  Independently certify the
  rational lower bound corresponding to `118108581006 / 10^9` from the exact
  safe/flat products.
- Negated residual: the first exact owner/state/support collision, response
  change, target mismatch, or skeleton collision.  Package nonexistence and
  pairwise window-core disjointness are not substitutes for these witnesses.
- Methodology re-entry: level-2 graph-semantic producer repair, followed by
  level-3 route review for each negative leaf and a separate numerical
  certificate audit.
- New invariant attempted: complete declared support with canonical overlap
  ownership.  It is expressible and locally checkable, but no current producer
  supplies it.
- Dependency-ready proofs retained: the one-window integer rate theorem, the
  exact partition payment, and overflow-to-cold arithmetic.  No additional
  semantic Lean lemma was added because every missing semantic conclusion
  needs data absent from the current predecessor.  The dependency-ready
  generic finite-product identity was implemented, used to eliminate two
  proof-injected structure fields, and checked in the non-Erdős transfer
  `StructuralExhaustion.Examples.UniformFiniteFibreProduct`.
- Complete audit rerun after repair: no.

## Final verdict

**FAIL.**  The exact weighted local products and
`stateCount_gt_ratePower` are mathematically sound, and the final hot/cold
arithmetic is already implemented.  The proposed aggregate package needs its
glue/restriction direction corrected, then still needs graph-owned complete
supports, many-window commutation, target semantics, exact skeleton encoding,
typed negative consumers, and a sharper certified numerical rate.  No
existing Core or Graph declaration closes those obligations for the exact
weighted hot list.

## Post-audit repair iteration: exact numerical rate

The exact-rate finding above was returned to the repair loop and is now
discharged.  The invariant and rounding direction were frozen before coding:

```text
2^K * L/D <= x^(2^s),
L' = floor(L^2 / (D*2^q)),
K' = 2*K + q.
```

Because `D*2^q*L' <= L^2`, every rounding step is downward and preserves a
lower bound.  The reusable implementation is
`Core.FixedPointRepeatedSquareLower`.  Its inductive `Run.sound` theorem is
proved over `ℚ`; the checker evaluates only the current bounded numerator and
one shift at each row.  The public `ScaledDyadicRateLower` contract expresses
the rate through a dyadic power lower bound plus a scaled integer exponent
comparison, without real logarithms.

`Erdos64EG.P13ExactWeightedRate` instantiates this theorem with the exact
node-[21] products, `D=10^40`, the 34-bit shift word recorded above, and
initial exponent 118.  Kernel-checked bounded certificates prove:

```text
steps = 34,
finalExponent = 2029089971192,
D <= finalLower,
118108581006 * 2^34 <= 10^9 * finalExponent.
```

Together with the exact initial cross-product comparison, `Run.sound`
constructs `p13ExactWeightedRateCertificate` of type

```text
ScaledDyadicRateLower
  (p13BarrierSafeProduct / p13BarrierFlatProduct)
  118108581006 1000000000.
```

No term normalizes `A^10^9`, `2^118108581006`, or any comparable giant
integer.  All concrete rows are checked by `native_decide`; their semantic
composition is an ordinary Lean proof.

The independent transfer
`StructuralExhaustion.Examples.FixedPointRepeatedSquareLower` checks the same
generic theorem on `3/2`: one row with denominator 100 rounds 225 down to the
numerator 112 after one binary shift and proves
`2*112/100 <= (3/2)^2`.  This keeps the reusable checker independent of the
Erdős constants.

Focused verification after the repair:

```text
lake env lean StructuralExhaustion/Examples/FixedPointRepeatedSquareLower.lean
lake build
lake build Erdos64EG.P13ExactWeightedRate Erdos64EG.Tests
```

All pass; reported warnings are pre-existing linter warnings in replayed
modules.

### Updated exact-rate verdict

- Blocking finding 5 (“exact rate absent”) is **closed**.
- The repair sketch's `p13ExactWeightedRate` row now has a concrete producer.
- The full aggregation audit remains **FAIL** because graph-owned weighted
  state interpretation, complete-support ownership/commutation, total
  dependent gluing and recovery, exact skeleton injection, and typed negative
  consumers remain open.  None of those semantic findings is weakened by the
  numerical repair.
