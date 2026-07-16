# Red-team audit: node 176 canonical Type B support-family contract

## Baseline

- Repair sketch:
  `proofs/erdos_64_eg/repairs/node176_canonical_typeb_support_family_contract.md`.
- Source manuscript SHA-256 at audit start:
  `8910b6c91e7c1e9a83a8bec0ce232204f41274d9392df9e9de893f7a4801287f`.
- Repair-sketch SHA-256 at audit start:
  `9ad823050e88c7aca17956917f75fbdd6443e51db51f0728c1aa98a6e8cb2dd4`.
- Failed node and claim: white node `[176]`; the missing implication is from
  the local, universally quantified node-`[84]` theorem to one canonical
  finite ordinary/grouped support family, its two coefficient-208 bounds,
  within-role center incidence control, and finally the factor-416 global
  mass bound consumed by node `[85]`.
- Methodology consulted: branch-state provenance, quantifier normalization,
  both-sides admission, typed handoffs, CT14 S-Def/S-Rout/S-Trig/S-Comp,
  finite-local-universe rules, leaf totality, level-3 interface review, and
  the red-team checklist.
- Exact files inspected:
  `TypeBSupportScope.lean`, `CT14TypeBLocalFanMass.lean`,
  `CT14TypeBResidualCenterLedger.lean`, `TypeBEntryRouting.lean`,
  `Routes/NegativeSupportHandoff.lean`,
  `Graph/SupportIndexedFanMass.lean`, `Graph/TwoRoleFanMass.lean`, and the
  node-`[1]`--`[25]`, `[64]`--`[85]`, and Type B fan-mass manuscript
  sections.
- Current verdict: **FAIL**.

The sketch correctly refuses to enumerate vertex subsets and correctly
identifies a graph-owned schedule as the first missing producer. It does not,
however, construct that schedule from the exact incoming Lean branch, type
the grouped entries uniformly, prove reachability from node `[108]`, or fill
the semantic fields required by the existing CT14 profile.

## Independently reconstructed provenance

The formal ordinary prefix reaching node `[84]` is

```text
VerifiedTypeBLocalFanMassPrefix ctx
  -> VerifiedTypeBResidualCenterLedgerPrefix ctx
  -> VerifiedDegreeFourB2RoutingPrefix ctx
  -> ...
```

and ultimately retains the selected `MinimalCounterexampleContext`. Its
node-`[84]` field is literally

```lean
route : forall (scope : TypeBSupportScope ctx)
  (noHigher : scope.NoHigherCenter), scope.LocalFanMassRoute noHigher
```

This is a theorem for every *supplied* scope. It stores no scope, no list of
scopes, no `VerifiedNode65Residual`, and no exit-7 handoff.

The separate `TypeBEntryRouting` layer proves only local adapters:

- `node64` packages one supplied ordinary negative support and witness;
- `node66` transports one supplied decorated handoff;
- `VerifiedNode65Residual` is a tagged sum for one entry.

There is no producer theorem for node `[108]`, no finite list of all node-65
entries, and no theorem joining that local adapter to
`VerifiedTypeBLocalFanMassPrefix`. In particular, the proposed grouped input
is not an ancestor field of node `[84]`.

### Provenance matrix

| Used fact | Producer node/declaration | Earlier on this path? | Independent of node 176? | Verdict |
|---|---|---:|---:|---|
| Minimal selected graph, baseline, target avoidance | `MinimalCounterexampleContext`; node `[4]` prefix | yes | yes | available |
| Node-1 ambient graph ancestry | manuscript `[1]` and existential minimal-context selection | yes, through the verified prefix | yes | available only through an explicit retained prefix |
| Local node-84 route for a supplied scope | `VerifiedTypeBLocalFanMassPrefix.route` | yes | yes | available |
| One ordinary node-64 residual | `TypeBEntryRouting.node64` | only when its support and witness are supplied | yes | local constructor, not a global producer |
| One decorated node-66 residual | `TypeBEntryRouting.node66` | only after one `ExitHandoff` is supplied | yes | local adapter, not a node-108 producer |
| Finite list of all ordinary and decorated entries | none | no | n/a | blocking absence |
| Pairwise-disjoint Type A core family producing all exit-7 handoffs | manuscript assertion only; no Lean producer | no | n/a | blocking absence |
| Core--center incidence graph and its component partition | none | no | n/a | blocking absence |
| Canonical ordinary assignment across supports | manuscript `def:canonical-decomp`; no node-176 Lean object | not in node-84 prefix | unknown | blocking absence |
| Coefficient-200 processed-boundary theorem | manuscript open node `[176]` | no | n/a | blocking absence |
| Remaining coefficient-8 grouped/ordinary ledger theorem | manuscript open node `[176]` | no | n/a | blocking absence |
| Support-indexed CT14 arithmetic | `Graph.SupportIndexedFanMass` | reusable | yes | available after semantic profile construction |
| Bound by ambient `sigma(G)` | no current node-176 Lean theorem | no | n/a | blocking absence |

## Quantifier attack

### Schedule quantifier

The sketch needs a finite type `SourceEntry` and a graph-owned value

```text
source : ExactTypeBEntrySchedule ctx previous
```

whose completeness quantifies over that already defined finite source type.
Instead it proposes

```lean
structure ExactTypeBEntrySchedule (ctx) where
  entries : List (VerifiedNode65Residual ctx ...)
  complete : every surviving ordinary or exit-7 Type B entry occurs in entries
```

There are two failures.

First, “every surviving entry” has no declared finite domain. `complete` can
therefore hide the missing global branch theorem rather than check a supplied
source enumeration. Second, `VerifiedNode65Residual` depends on four
support predicates and one ternary fan predicate. The ellipsis cannot be
filled uniformly if different decorated handoffs carry different predicate
families. A single homogeneous `List` requires either fixed predicates proved
common to all handoffs or a dependent sigma package preserving each entry's
predicates. Neither is specified.

### Canonical-family quantifier

`entriesExact : entries = runCanonicalTypeBSupports source` proves ownership
only after `runCanonicalTypeBSupports` is an independently defined graph
function. With the current sketch, the function, its source enumeration, and
its coverage theorem are all names for the missing conclusion. Equality to an
undefined runner is not a producer.

The ordinary constructor similarly stores a freely supplied
`TypeBSupportScope` plus an equality to the undefined
`scopeOfOrdinaryEntry`. Until that function is constructed from the actual
entry, the equality field merely moves the missing scope producer into the
constructor.

### Incidence and simultaneous grouping quantifiers

The manuscript starts with one finite *pairwise vertex-disjoint* Type A core
family `Y`, includes all exit-7 handoffs from those cores, and forms connected
components of the resulting bipartite incidence graph. The current Lean route
supplies one handoff at a time. The sketch exchanges

```text
forall produced handoff, one local node66 residual exists
```

for

```text
exists one complete, deduplicated, pairwise-disjoint handoff family on which
all grouped components are computed.
```

The former does not imply the latter without the missing global producer and
ordering theorem.

### Quantifier table

| Claim | Literal quantified form | Smallest countermodel attempted | Result |
|---|---|---|---|
| Local node 84 supplies a global schedule | `forall scope, route(scope)` implies `exists finite scopes, complete(scopes)` | a nonempty abstract scope type with a theorem for every supplied scope but an empty proposed schedule | false; universal processing does not enumerate inputs |
| Local node66 adapters supply grouped reachability | `forall supplied handoff, residual(handoff)` implies `exists list containing every actual handoff` | two actual handoffs while the supplied list contains one | false; the adapter has no coverage theorem |
| One homogeneous node65 list stores all decorated entries | all entries inhabit one `VerifiedNode65Residual` type | two handoffs indexed by distinct predicate families | ill-typed without fixed predicates or a dependent sum |
| Equal grouped center implies component equality | occurrences share center, hence their cores lie in one component | valid only if both occurrences are edges of the same complete incidence graph | conditional; the complete graph and edge reflection are absent |
| Role-center injectivity follows by deduplication | deduplicate centers after supports are built | two distinct ordinary supports assigned the same center | false; per-support deduplication does not remove a cross-support collision without dropping or rerouting one support's deficit |
| CT14 global surplus is ambient `sigma(G)` | sum over derived `Center` equals or is bounded by ambient surplus | a `Center` type containing duplicate copies of one ambient vertex | false unless the embedding is injective and its surplus reflection is proved |

Injection-versus-surjection and Boolean-cube issues are not implicated here.
Representative existence and context coverage are implicated: scopes,
components, and retained-support representatives are assumed to exist before
their graph constructors are given.

## Branch and invariant audit

- **Positive payment/account:** the intended role-center injection would let
  `SupportIndexedFanMass` prove at most two uses of each center token. The
  payment is not established because neither the actual occurrences nor the
  cross-support injection is constructed.
- **Negative bounded witness/consumer:** first missing entry, collision, and
  failed coefficient support are finite only after the missing source and
  support lists exist. The stated “assignment correction,” “component merge,”
  and “local-ledger refinement” are not registered typed consumers and do not
  prove preservation of all deficit mass.
- **Measurability:** the proposed `m`, `t`, and `e` work bounds are local once
  the lists exist. Their graph-owned producers are absent, so the current
  sketch has no executable input universe.
- **Ladder legality:** role-center injection is a reasonable CT14 invariant
  only after exact support coverage and deficit preservation. Selecting it
  before those earlier invariants reverses the dependency order.
- **Cross-branch leakage:** the grouped path imports Type A exit-7 handoffs,
  pairwise-disjoint canonical Type A cores, route-8 extraction, saturated
  receiver absence, and post-ledger unsaturation. None is a field of
  `VerifiedTypeBLocalFanMassPrefix`. The sketch names nodes `[108]` and `[66]`
  but no compiled path collects their outputs into node `[176]`.
- **Theorem weakened or assumption added:** the source theorem is not
  explicitly weakened, but `ExactTypeBEntrySchedule.complete`,
  `CanonicalTypeBSupportFamily.coverage`, `localBound208`, and
  `usedSurplusLeGlobal` would be precisely the missing theorem if accepted as
  application data.

## Node-1 ancestry audit

Node `[1]` is the supplied finite simple graph. Nodes `[2]`--`[4]` select the
minimal counterexample, and the verified Lean prefix retains this through
`MinimalCounterexampleContext` and the chain beginning with
`VerifiedNoProperCorePrefix`.

The proposed `ExactTypeBEntrySchedule (ctx)` is indexed only by `ctx`; it does
not retain `VerifiedTypeBLocalFanMassPrefix ctx`, a node-65 source, the
original object/rank relation, or an exact decomposition output. Likewise
`CanonicalTypeBSupportFamily (ctx) source` does not state that `source` was
computed from the same verified prefix. Lean's shared `ctx` prevents changing
the selected graph, but it does not prove that the entries exhaust the branch
decomposition descended from node `[1]`. The schedule must be indexed by the
exact predecessor/decomposition payload and carry an equation to its runner.

Thus graph identity is preserved, but branch ancestry and coverage are not.
This is blocking provenance loss, not merely missing documentation.

## Grouped handoff reachability

The proposed path

```text
Type A exit 7 [108] -> node66 -> node65 -> grouped Type B ledger -> node176
```

is not currently realized in Lean. `TypeBEntryRouting.Exit7Handoff` is an
abbreviation for the expected producer type; no theorem constructs it at node
`[108]`. `node66` is identity-like transport of one already supplied handoff.
There is no finite handoff schedule, no proof that its cores are the canonical
pairwise-disjoint Type A cores, no completeness theorem for all handoffs, and
no route from grouped entries through the ordinary node-84 scope theorem.

The sketch's sentence that a grouped constructor appends “the actual node-66
decorated handoff” therefore assumes reachability. The first required grouped
unit is a data-preserving producer of an exact finite Type A exit-7 handoff
schedule, indexed by the same predecessor, with core disjointness, handoff
coverage, and predicate-family packaging.

## CT14 obligations

| CT14 field/step | Exact trigger | Current sketch | Verdict |
|---|---|---|---|
| `supports : FinEnum Support` | exact duplicate-free canonical support list | proposed runner and coverage, unimplemented | blocking |
| `centers : FinEnum Center` | duplicate-free ambient center image | described as derived image; embedding/injectivity theorem absent | blocking |
| `occurrences : FinEnum Occurrence` | exact dependent support-center incidences | described, no constructor/equality | blocking |
| `localBound` | `deficit X <= 208 * sum occurrence surplus` for each nonextracted support | `localBound208` uses undefined `support.centerMass`; no equality to profile sum | blocking |
| `withinRoleDisjoint` | injectivity of `(role (support o), center o)` on every occurrence | assigned as family field; repair branches unproved | blocking hidden assumption |
| extracted semantics | extracted support has zero retained CT14 deficit and its full mass is handed elsewhere | Boolean flag and proposed zero; no conservation/handoff theorem | blocking |
| coefficient | literal equality to 208 | proposed and compatible with current producer | ready only after semantic bound |
| CT14 terminal | complete profile and local bounds | generic theorem exists | reusable, not a producer |
| ambient surplus comparison | `profile.globalSurplus <= sigma ctx.G` | proposed family field, absent from current `TypeBGlobalFanMassProducer` and aggregate theorem | blocking |
| output to node 85 | exact node-85 input with context and mass meaning | `VerifiedTypeBGlobalFanMass` is named but no declaration exists | blocking payload mismatch |

The generic theorem currently proves only

```text
producer.profile.residualMass <= 416 * producer.profile.globalSurplus.
```

It does not identify `residualMass` with manuscript `M_B`, identify the
profile center sum with used ambient surplus, prove the latter at most
`sigma(G)`, obtain the near-cubic `O(sqrt n)` estimate, or construct a node-85
consumer. Those are separate S-Equiv/S-Comp/S-Trig obligations.

## Reused branches and handoffs

| Handoff | Exact trigger proved? | State transported? | Consumer dependency cone | Independent of node 176? | Measure | Verdict |
|---|---:|---:|---|---:|---|---|
| Target/dyadic exit to C1 | not from the proposed schedule | not recorded | existing target closure | likely | acyclic | unreachable from current producer |
| Target defect/compression to C2/C3 | not constructed per failed support | not recorded | CT3/minimality | likely | acyclic | named only |
| Saturated Type A receiver to node 89 | no exact receiver payload | no | Type A chain | not audited | none | blocking |
| Extracted route-8 core to node 109/Part IX | no exact route-8 payload or conservation identity | no | Type A route-8 ledger | may use global Type B bookkeeping | none | blocking/circularity unaudited |
| Ordinary collision to overlap repair | no registered payload/consumer | no | unspecified | unknown | none | blocking |
| Grouped collision to component merge | plausible graph operation after incidence graph exists | partial | same constructor | yes if implemented | number of unassigned/merged components | open |
| Verified global mass to node 85 | no node-85 typed input exists | context only | manuscript sublinear closure | depends on open node 176 arithmetic | acyclic intended | blocking |

The route-8 handoff needs special care: setting extracted CT14 mass to zero is
sound only with an exact conservation theorem transferring that same deficit
to the Type A ledger once. The sketch states the destination but supplies no
identity and no dependency audit excluding a return through node `[176]`.

## Leaf totality

| Leaf | Required endpoint | Exact proof/certificate in sketch | Practical checker | Verdict |
|---|---|---|---|---|
| Missing source entry | append at producer | no finite source enum or producer append theorem | none | blocking |
| Ordinary scope field missing | existing local producer | producer unnamed and trigger absent | none | blocking |
| First unvisited grouped handoff | component scan continuation | no handoff list | quadratic once supplied | producer blocking |
| Ordinary role-center collision | correction/overlap repair | no mass-preserving correction or typed route | local once supplied | blocking |
| Grouped role-center collision | merge components | no incidence edge reflection or merge theorem | local once supplied | blocking |
| Boundary coefficient-200 failure | charge to processed endpoint | no processed-endpoint ledger/consumer | local candidate | blocking |
| Remaining coefficient-8 failure | typed local deficit residual | residual type and consumer absent | none | blocking |
| Extracted route-8 support | Type A ledger | no conservation/coverage theorem | none | blocking |
| Valid retained supports | CT14 profile | semantic profile bridges absent | generic CT14 checker exists | blocking producer |
| Global CT14 bound | node 85 | no ambient-surplus/sublinearity/node-85 trigger | generic profile checker insufficient | blocking |

No leaf presently reaches C1--C5 or an already admitted typed consumer from
the proposed global runner. The leaf table in the sketch describes intended
destinations, not proved handoffs.

## Practicality and termination

- Largest proposed universe: the produced entry/support list, occurrence list,
  and actual handoff-incidence edge list.
- Controlling parameters: `m`, `t`, and `e`; these are appropriate local
  parameters after a producer exists.
- Claimed component work: `O((m+e+1)^2)` list work. This is plausible but not
  yet a theorem attached to a runner.
- Existing CT14 check count: exactly
  `2*m*t + 2*m + 1`, with proved quadratic bound
  `3*(m+1)*(t+1)`.
- Cycles: the proposed component scan removes one unassigned handoff; the
  collision “merge and rerun” path needs a separate strict measure, since a
  rerun may preserve the unassigned count. Number of components or first
  inconsistent labels could supply it, but neither is registered.
- Hidden global computation: “every surviving entry,” “all actual handoffs,”
  the canonical Type A core family, and the incidence components are global
  quantifiers with no enumerated source. The sketch does not enumerate all
  vertex subsets, but it has not yet replaced those quantifiers with a local
  produced schedule.

The intended execution model is acceptable in shape. Its inputs and
termination certificates are not implemented.

## TeX--Lean--framework correspondence

- **Exact statement match:** no. The manuscript family includes ordinary
  bridge residuals and grouped envelopes, exact route-8 extraction, a
  coefficient-208 semantic bound, at-most-two ambient center use, and
  `M_B <= 416 sigma(G)`. Lean currently exposes only a conditional abstract
  profile theorem.
- **Generic ownership:** `SupportIndexedFanMass` correctly owns the CT14
  arithmetic. Incidence-component construction, canonical support schedules,
  and support-to-profile semantic bridges belong in Graph/Routes before thin
  Erdős instantiation.
- **Problem-specific layer thin:** not yet; the proposed family record would
  store all hard Erdős conclusions as fields unless graph producers and
  reflection theorems are separated.
- **Transfer example:** the existing `Examples.SupportIndexedFanMass` tests
  the generic aggregate, not the new append-only schedule/component/collision
  route. A new route requires its own non-Erdős transfer example.
- **Trust search:** no `sorry`, `admit`, `axiom`, or `unsafe` occurs in the
  inspected exact files. `Classical.choose` appears in the local node-84
  unresolved-center extraction; it chooses from a proved finite existential
  and is not the global schedule gap.
- **Trust base:** current compiled support remains Lean/mathlib plus the
  registered HSS interface. The sketch introduces no external theorem.
- **Artifact status:** the manuscript and web correctly call node `[176]`
  open. No production synchronization is authorized on this FAIL verdict.

## Findings

### Blocking

1. **First exact failing obligation:** construct a finite, predecessor-indexed
   source schedule from the actual branch decomposition. The node-84 prefix
   contains no node-65 entry list, and the node-66 adapter constructs no
   node-108 handoff schedule.
2. Define a uniform entry type. Either prove all decorated handoffs share the
   same five semantic predicate families or use a dependent package that
   preserves them; `VerifiedNode65Residual ctx ...` cannot be a list element
   with an ellipsis.
3. Prove grouped reachability: exact finite Type A core list, pairwise core
   disjointness, complete exit-7 handoff list, and incidence-edge reflection.
4. Construct ordinary scopes from ordinary entries. Node 84 accepts arbitrary
   scopes and does not provide `scopeOfOrdinaryEntry`.
5. Prove support coverage and deficit conservation. Collision correction,
   component merging, and extracted route-8 transfer may not drop a support's
   negative mass.
6. Prove both coefficient-208 semantic bounds, including the equality between
   each support's center mass and the occurrence sum used by the CT14 profile.
7. Prove within-role injectivity from canonical assignment and complete
   incidence components; do not store it as an unconstructed family premise.
8. Prove `profile.globalSurplus <= sigma(ctx.G)` and identify profile residual
   mass with manuscript `M_B`. The current global theorem stops at the
   abstract center sum.
9. Construct the exact node-85 typed consumer and audit the route-8 handoff
   dependency cone for circularity.
10. Index the schedule by the exact verified predecessor/decomposition payload
    so that branch coverage, not merely graph identity, descends from node
    `[1]`.

### Required cleanup

1. Replace undefined prose types such as “exact ordinary schedule entry,”
   “Component producedHandoffIncidenceGraph,” and “exact grouped ledger
   outcome” with concrete proposed signatures before the next audit.
2. Separate graph-owned producer theorems from the final family record. A
   record containing `coverage`, `localBound208`, `withinRoleDisjoint`, and
   `usedSurplusLeGlobal` as raw application inputs would recreate the open
   node as a hypothesis.
3. Add a distinct transfer example for the schedule/component producer; the
   existing CT14 example covers only aggregate arithmetic.
4. Record a strict measure for collision-driven component reruns.

### Advisory

- Retain `Graph.SupportIndexedFanMass`; its role-tagged occurrence injection
  and exact work ledger match the intended aggregate once the semantic
  producer exists.
- The proposed `m,t,e` locality model is preferable to scanning vertex
  subsets and should be retained after the source schedule is made exact.
- Keeping ordinary and grouped constructors distinct is correct and prevents
  branch-specific predicates from leaking across the join.

## FAIL disposition

- Exact obligation returned to the repair loop: define and construct
  `ExactTypeBEntrySchedule` from an exact predecessor that actually emits both
  ordinary node-64 entries and all Type A exit-7 handoffs, with a concrete
  finite entry type and completeness theorem.
- Negated residual: the first predecessor decomposition entry absent from the
  schedule, or the first scheduled decorated entry whose predicate-indexed
  handoff cannot be represented in the declared entry type.
- Methodology re-entered: level-2 provenance reconstruction and invariant
  ordering, then level-3 interface design for a finite branch-output schedule.
- Finer split required:
  1. ordinary source schedule;
  2. Type A exit-7 handoff schedule;
  3. typed join preserving constructor-specific predicates;
  4. grouped incidence components;
  5. support-to-CT14 semantic reflection.
- Candidate first reusable contract: an append-only finite branch-output
  schedule indexed by the exact decomposition runner, with a dependent tagged
  entry type, coverage, noduplication, and list-local first-missing residual.
- Complete audit rerun after repair: **no**. This artifact audits the submitted
  sketch only; the blocking producer has not been implemented or added as an
  assumption.

## Verdict

**FAIL.** Node `[176]` remains white. The source manuscript, production Lean,
web companion, theorem index, and implementation log must not be changed from
this sketch.
