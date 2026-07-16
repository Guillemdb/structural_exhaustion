# Node 176 repair sketch: canonical Type B support-family producer

Status: design sketch only. This file changes no theorem statement and is not
evidence that node 176 is implemented.

## Defect freeze

- Defect ID: `EG-N176-CANONICAL-FAMILY`.
- Stable nodes: green local node 84, white aggregate node 176, consumer node
  85.
- Exact failed implication:

  ```text
  VerifiedTypeBLocalFanMassPrefix ctx
    does not imply
  exists Support Center Occurrence,
    TypeBGlobalFanMassProducer Support Center Occurrence.
  ```

  Node 84 proves a result for every *supplied* `TypeBSupportScope`; it does
  not produce a finite list of actual scopes or grouped envelopes.
- Classification: execution/interface defect E at level 3. The reusable CT14
  aggregate exists, but its graph-owned producer is absent.
- Smallest verified ancestor: `VerifiedTypeBLocalFanMassPrefix ctx`, whose
  `previous` field retains node 75 and nodes 81--83.
- Surviving ancestor state: the exact branch-tagged node-65 Type B entry and
  its later node-84 local outcome, on the same minimal-counterexample context.
- Blast radius: `lem:typeB-processed-boundary-bound`, both coefficient-208
  bounds, `prop:typeB-bridge-sublinear`, node 85, and the Type B input to
  `thm:branch-kill` at node 76.
- Exact residual: a local node-84 theorem with no graph-owned enumeration of
  the ordinary supports or grouped decorated handoff components to which it
  must be applied.
- Source manuscript remains unchanged during sketching: yes.

## Frozen directed branch state

Write the active state as

```text
B176 = (H0, order, exits, invariants, residual, vocabulary, queue, artifacts).
```

- `H0`: the selected minimal counterexample, target avoidance, the literal
  remainder, and the exact Type B branch data inherited by node 65.
- `order`: the existing minimal-counterexample rank; node 176 performs no
  replacement and introduces no new order.
- Incoming paths:
  - ordinary: `64 -> 65 -> 67--75 -> 81--84`;
  - grouped: Type A exit 7 `108 -> 66 -> 65`, followed by its Type B ledger.
- Certified absent exits for a retained coefficient-208 support: target hit,
  target-defective quotient, target-complete compression, proper/global
  delocalization, saturated Type A receiver, and extracted Type A route 8.
  These exclusions must be fields of the exact support record; they may not
  be inferred at node 176.
- Inherited invariants:
  - actual high centers and `degree >= 4`, from `TypeBSupportScope`;
  - exact node-75 assigned-surplus charging;
  - node-81 local entries, node-82 full-choice outcome, node-83 minimal
    overlap, and node-84 selected-center mass;
  - ordinary canonical assignment and grouped core--center incidence data,
    once produced upstream.
- Residual: `MissingCanonicalTypeBSupportSchedule`.
- Vocabulary: tagged support, ordinary/grouped role, actual center occurrence,
  extracted route-8 flag, literal deficit, processed envelope, incidence
  component.
- Queue: the completed `Graph.SupportIndexedFanMass` CT14 consumer.
- Artifacts affected after a future PASS: nodes 176, 85, and 76 only.
- Explicitly unavailable: a caller-supplied support family, all vertex
  subsets, all connected supports, all handoff subsets, and any grouped
  component not computed from an actual handoff list.

## Quantifier normalization

The missing conclusion is not

```text
forall supplied families, if their desired properties hold then CT14 closes.
```

That conditional theorem already exists. The required statement is

```text
for the one exact upstream Type B schedule on ctx,
compute a finite tagged support list and prove that its derived profile has
the required local bounds and role-center injectivity.
```

The family must be a deterministic function of an exact predecessor schedule.
`Support`, `Center`, and `Occurrence` are derived types, not producer fields.
Failure of construction has a canonical witness: the first predecessor entry
not represented in the list, the first role-center collision, or the first
retained support failing the coefficient-208 bound. All selectors use the
declared predecessor order.

## Proposed exact upstream schedule producer

The new upstream payload is:

```lean
structure ExactTypeBEntrySchedule (ctx) where
  entries : List (VerifiedNode65Residual ctx ...)
  entriesNodup : entries.Nodup
  exact : entries = runTypeBEntrySchedule ctx predecessor
  complete : every surviving ordinary or exit-7 Type B entry occurs in entries
```

`runTypeBEntrySchedule` is not allowed to scan possible supports. It must be
emitted by the existing branch decomposition as entries are created. The
ordinary constructor appends the actual node-64 residual. The grouped
constructor appends the actual node-66 decorated handoff. Thus schedule size
is the number of produced branch entries, not the number of vertex subsets.

The first implementable unit is this exact append-only schedule and its
provenance theorem. Until it exists, neither ordinary scopes nor grouped
components are graph-owned globally.

## Canonical support records

```lean
inductive CanonicalTypeBSupport (ctx)
  | ordinary
      (entry : exact ordinary schedule entry)
      (scope : TypeBSupportScope ctx)
      (scopeExact : scope = scopeOfOrdinaryEntry entry)
      (route : exact node84 route scope)
      (centers : exact singleton or overlap-center list)
  | grouped
      (component : Component producedHandoffIncidenceGraph)
      (componentExact : component = declared component from the BFS scan)
      (support : union of component handoff cores and fan envelopes)
      (centers : exact duplicate-free component-center list)
      (route : exact grouped Type B ledger outcome)
```

For ordinary entries, `scopeOfOrdinaryEntry` must derive `vertices`, reserved
carriers, and marked fans from the exact ledger; none is a free parameter.
For grouped entries, first build the finite bipartite incidence graph whose
vertices are actual handoff cores and actual handoff centers and whose edges
are literal recorded incidences. Compute its components in the declared list
order. No component family is supplied by the caller.

## Minimal family contract

```lean
structure CanonicalTypeBSupportFamily (ctx)
    (source : ExactTypeBEntrySchedule ctx) where
  entries : List (CanonicalTypeBSupport ctx)
  entriesNodup : entries.Nodup
  entriesExact : entries = runCanonicalTypeBSupports source
  coverage : every surviving source entry is represented exactly once
  withinRoleDisjoint : Function.Injective fun occurrence =>
    (occurrence.support.role, occurrence.center)
  localBound208 : forall support, not support.extracted ->
    support.deficit <= 208 * support.centerMass
  usedSurplusLeGlobal : usedCenterSurplus <= sigma ctx.G
```

Derived definitions:

- `Support` is the index type of `entries`.
- `Occurrence` is the dependent index of each support's exact center list.
- `Center` is the duplicate-free image of occurrence centers.
- `role`, `occurrenceSupport`, and `occurrenceCenter` are projections.
- `centerSurplus h = degree(h) - 3`.
- `deficit` is the literal negative net charge of the support.
- `extracted` is true exactly on the inherited route-8 constructor.

The `SupportIndexedFanMass.Profile` is derived from this structure. It is not
stored as arbitrary application data.

## Resource inventory

| Resource | Producer | Pays for | Capacity |
|---|---|---|---|
| Local center list and degree lower bound | `TypeBSupportScope` | positive center surplus | once per role-center token |
| Singleton/overlap selected list | nodes 75, 83, 84 | ordinary center occurrences | literal list length |
| Full-choice/route-8 split | nodes 81--84 | retained versus extracted support | one exact outcome per ordinary scope |
| Decorated handoff | nodes 108, 66 | grouped core-center incidence | once in the exact handoff schedule |
| Processed-envelope degree bound | `lem:typeB-processed-boundary-bound` | 200 of the coefficient 208 | actual processed vertices only |
| Local fan/core accounting | ordinary and grouped deficit lemmas | remaining 8 | actual support only |
| CT14 two-role injection | family contract | factor two | at most ordinary plus grouped use |

## Both-sides test

| Predicate | Positive side | Negative residual | Measurable from | Consumer |
|---|---|---|---|---|
| Entry is ordinary | construct exact scope and ordinary support | entry is grouped | schedule constructor tag | grouped constructor |
| Grouped handoff belongs to current incidence component | add its core/envelope to the component union | first incidence crossing components | finite incidence edge list | merge components and rerun component scan |
| Support is route-8 extracted | contribute zero retained deficit and hand core to Type A | support is retained | exact node-84/grouped route | coefficient-208 local bound |
| Role-center tags are injective | CT14 multiplicity at most two | first equal tag from distinct occurrences | declared occurrence order | canonical-assignment correction for ordinary; component merge for grouped |
| Retained support satisfies coefficient 208 | supply CT14 local capacity | first failing retained support | support order and literal charge | processed-boundary/local-ledger refinement |

Each negative side is bounded by an actual list and refines construction; none
is converted into an assumption.

Selected invariant: injectivity of `(role, center)` on actual occurrences,
after exact role-specific canonicalization. This is the earliest invariant
that converts local coefficient bounds into the global factor two.

## CT14 worksheet

- Instance: node 176, `Graph.SupportIndexedFanMass`.
- Input: `CanonicalTypeBSupportFamily ctx exactSchedule`.
- S-Def: members are exact support indices; labels are ordinary/grouped;
  lower mass is retained deficit; capacity is `208 * centerMass`.
- S-Dich: extracted supports have zero retained mass; every other support uses
  `localBound208`.
- S-Equiv/Pers: support identity, role, center occurrences, and extracted flag
  are preserved definitionally from the canonical list.
- S-Det: schedule order, incidence-component BFS order, and support order are
  fixed by predecessor lists.
- S-Rout: construct `SupportIndexedFanMass.Profile` from derived types.
- S-Trig: `withinRoleDisjoint` is exactly the profile's injection trigger.
- S-Comp: `coefficient = 208`; CT14 yields
  `M_B <= 208*S_B <= 416*usedCenterSurplus <= 416*sigma(G)`.
- S-Rest/S-Meas: no loop after component construction. The component scan
  removes at least one unassigned handoff per pass.
- Output: typed `VerifiedTypeBGlobalFanMass` consumed by node 85.

## Autonomous derivation ledger

| Required statement | Exact inputs | Canonical failure | Refined route |
|---|---|---|---|
| Exact global entry schedule | branch-produced ordinary/decorated entries | first unrecorded entry | append at its producer |
| Ordinary scope construction | ordinary entry plus exact ledger | first missing scope field | route to the field's existing local producer |
| Grouped component partition | actual handoff incidence list | first unvisited handoff | declared-order finite component scan |
| Ordinary role disjointness | canonical ordinary assignment | first duplicated center | keep only the unique assigned support and route the other entry to overlap repair |
| Grouped role disjointness | incidence components | same center in two components | literal incidence joins them; merge components |
| Boundary coefficient 200 | processed vertex and incidence lists | first boundary edge not charged | charge it to its literal processed endpoint |
| Remaining coefficient 8 | exact local fan/core ledger | first unpaid local term | typed local deficit residual, consumed before CT14 |
| Used surplus at most global surplus | duplicate-free used-center list | duplicated center | deduplicate occurrences after role tagging and use one global center capacity |

No row permits adding its conclusion as a hypothesis.

## Leaf-totality and exit tests

| Branch | Exact output | Consumer |
|---|---|---|
| target or dyadic exit | C1 | existing target consumer |
| target defect/compression | C2/C3 | existing quotient/compression consumer |
| proper/global delocalization | typed existing exit | existing delocalization consumer |
| saturated Type A receiver | typed Type A handoff | node 89 chain |
| route-8 extracted core | zero CT14 mass plus exact core | node 109/Part IX |
| retained ordinary support | coefficient-208 support record | node-176 CT14 |
| retained grouped support | coefficient-208 support record | node-176 CT14 |
| role-center collision | first collision payload | assignment correction or component merge |
| all retained supports valid | verified global fan-mass payload | node 85 |

Exit tests required before admission:

1. every schedule entry has exactly one ordinary/grouped constructor;
2. every grouped handoff occurs in exactly one computed component;
3. every retained support has all target-algebra exits explicitly absent;
4. every extracted support contributes zero retained CT14 mass;
5. every occurrence belongs to its support's literal center list;
6. equal role-center tags imply equal occurrences;
7. each coefficient-208 proof uses only its support's processed lists;
8. the global factor two uses only the two roles;
9. node 85 receives the same context and exact global mass bound;
10. no support subset, family, graph, path, context, or Boolean-function
    universe is materialized.

## Practicality

Let `m` be the produced support count, `t` the actual center-occurrence count,
and `e` the produced handoff-incidence count. Schedule construction is linear
in produced entries. A declared-order component scan can be checked in
`O((m+e+1)^2)` list work. The existing CT14 profile uses exactly

```text
2*m*t + 2*m + 1
```

primitive checks and satisfies its proved quadratic bound
`3*(m+1)*(t+1)`. Certificates contain the exact entry list, component labels,
occurrence list, first-failure evidence when present, and local coefficient
proofs. No ambient family is enumerated.

## Synchronization gate

This sketch must receive an independent red-team PASS before any source
manuscript or production Lean edit. A later merge must synchronize the node
176 diagram, dependency and invariant tables, payload registry, Graph/CT14
producer, thin Erdős instantiation, non-Erdős transfer example, web status,
and implementation log from compiled provenance.
