# Node [84] support-indexed fan-mass repair worksheet

This is an isolated repair sketch.  It does not amend the source manuscript,
diagram, theorem index, web status, or implementation log.  The source TeX
baseline inspected during sketching has SHA-256
`6cea87715450176e2b3e611a347c7147764730866c7174122e5be0445235c671`.

## Defect freeze

- Defect ID: `EG64-node84-support-index-interface`.
- Stable node: `[84]` (`fanmass`).
- Exact failed implication, with quantifiers: the current green generic
  `Role × Center` surrogate would require every Type B residual support to be
  represented by one center.  The manuscript instead claims that for every
  finite canonical family `X_B` of actual ordinary and grouped Type B supports,
  if each `X` has a finite center-token set `H_X` and
  `No_-(X) ≤ 208 ∑_{h∈H_X} s_X(h)`, and if no center occurs more than once
  within either role, then
  `∑_X No_-(X) ≤ 416 σ(G)`.  The surrogate does not imply this statement.
- Classification and repair level: level-2 structural interface mismatch.
- Smallest verified ancestor: the typed node-`[108]` to node-`[66]` handoff is
  only a single routing payload; it is not yet the required family producer.
- Immutable blast radius at discovery: node `[84]` and all consumers of its
  sublinear Type B mass claim.
- Source manuscript remains unchanged during sketching: yes.

## Directed branch state

- Baseline hypotheses `H0`: the frozen near-cubic-spine branch, target
  avoidance, and all earlier certified Type B routing exclusions.
- Minimality order: inherited graph rank; unused by this aggregate CT14 step.
- Incoming paths: ordinary Type B bridge supports and grouped decorated Type B
  envelope supports surviving their earlier exits.
- Certified absent exits: only those carried by each support producer; the
  generic aggregate layer does not manufacture them.
- Inherited invariants and producers: actual finite support enumeration,
  actual finite center-token incidences, role of each support, center surplus,
  support deficit, extracted-support decision, per-support local bound, and
  within-role incidence disjointness.
- Exact residual formula: `M_B = ∑_X retainedDeficit(X)` with
  `retainedDeficit(X)=0` for an extracted support and `No_-(X)` otherwise.
- Finite vocabulary: `Support`, `Center`, `Occurrence`, and the two roles
  `ordinary | grouped`.
- Queued payload and consumer: a CT14 capacity residual carrying the proved
  bound `(2 * coefficient) * globalSurplus`; coefficient `208` would give
  `416σ(G)` after a valid thin instantiation.
- Artifact rows affected: node `[84]`, its TeX--Lean index row, and downstream
  global pressure consumers.  None are changed by this sketch.
- Explicitly unavailable: the actual grouped-envelope support family from
  node `[108]`, the incidence-partition proof for that family, and both exact
  coefficient-208 per-support theorems.

### Frozen-predecessor type audit

The missing data above are not merely absent convenience lemmas.  They cannot
be derived from the current predecessor types.

| Green predecessor | Exact Lean payload relevant to `[84]` | What it does not contain |
|---|---|---|
| `[75]` | for one `TypeBSupportScope`, every explicitly chosen `Finset scope.Center` has cardinality at most that scope's assigned surplus | a finite family of scopes/supports; canonical assignment across that family; disjointness of centers belonging to distinct scopes; a support deficit |
| `[81]` | one unresolved actual center, or a full local-entry resolution | a family producer or a deficit bound |
| `[82]` | a full CT12 choice followed by nonnegative charge or one literal negative remaining core | a coefficient-208 theorem on the unresolved/overlap branches |
| `[83]` | one inclusion-minimal overlap obstruction and its selected center list | a canonical family of bridge supports or a grouped-envelope incidence partition |
| `[108] -> [66]` | one `Exit7Handoff`, definitionally preserved as one decorated residual | a finite handoff family; incidence components; a grouped envelope charge; disjointness of grouped center occurrences |

There are two direct countermodels to any attempted construction from these
types alone.

1. Take a finite schedule with two copies of the same valid
   `TypeBSupportScope`.  All `[75]` theorems still hold separately, but the
   same center occurs twice in the ordinary role.  Therefore tagged-incidence
   injectivity is false.  The predecessor API contains no canonical-family
   field capable of excluding this schedule.
2. An `Exit7Handoff` requires a negative connected source with no internal
   high center and one external high center.  Its fields impose no numerical
   relation between the negative charge of the source and the surplus of the
   external center.  Replicating or enlarging a cubic negative source while
   retaining the same external center is not excluded by this type.  Thus the
   grouped coefficient-208 estimate is not a consequence of the handoff
   contract.

The currently proved quantitative theorems do not fill this gap.  The
choice-free ordinary theorem has an additional receiver-overload term,
`-netQuarterCharge <= 21 * assignedSurplus + receiverOverload`.  The
full-choice unsaturated theorem bounds the quarter-unit ledger by
`800 * assignedSurplus`.  Neither theorem is the manuscript statement
`No_-(X) <= 208 * sum_h (degree h - 3)` for all three residual sources, and
neither constructs grouped envelopes.

## Quantifier normalization

- Domain and codomain: every enumerated `Occurrence` maps to one actual
  `Support` and one actual `Center`; every support maps to one of two roles.
- Well-definedness: supplied as total finite maps over exact `FinEnum`s.
- Injection statement: the map
  `o ↦ (role (support o), center o)` is injective.
- Surjection/realization statement: no surjection onto all role--center pairs
  is asserted.  Only produced incidences are counted.
- Exact negation: two distinct occurrences have the same role and center.
  Such a witness invalidates the factor-two capacity conclusion and must be
  returned to an earlier overlap/refinement consumer, not erased by CT14.
- Canonical witness: the first duplicate tagged incidence in the supplied
  occurrence order.
- Selector determinism and measurability: finite equality scans on supplied
  support/incidence data; no ambient graph search.

## Resource inventory

| Resource | Producer | Price list | Remaining capacity |
|---|---|---|---|
| Actual ordinary support | ordinary Type B producer | its center-token sum | coefficient times that sum |
| Actual grouped envelope support | missing node `[108]` family producer | its incidence-component token sum | coefficient times that sum |
| Center surplus | near-cubic surplus ledger | at most once per role | at most twice globally |

## Both-sides candidates

| Predicate | Positive payment/account | Negative bounded residual | Measurable from | Consumer | Admit? |
|---|---|---|---|---|---|
| Tagged incidence is injective | total token mass `≤ 2σ` | first same-role duplicate | finite occurrence list | earlier overlap/refinement route | yes only after both producer and consumer are typed |
| Every retained support has its coefficient bound | CT14 capacity | first support missing/failing the bound | finite support and incidence lists | its ordinary/grouped semantic producer | yes only as proved predecessor evidence |

Selected invariant: actual support-indexed incidences, at repair level 2.  The
generic prototype takes the two positive-side proofs as semantic inputs.  A
future Erdős producer must route their negations before invoking the profile.

## CT worksheet

- Instance and node: support-indexed CT14 prototype for proposed node `[84]`.
- Input payload and producer: exact finite supports and incidences plus proved
  local-bound and tagged-injectivity evidence; Erdős producer still missing.
- Parameters: support/center/occurrence enumerations, two-role map, incidence
  projections, surplus, deficit, extracted flag, coefficient.
- S-Def: CT14 members are actual supports, not `Role × Center` surrogates.
- S-Dich: extracted supports contribute zero; retained supports use their
  semantic local bound.
- S-Equiv/S-Pers: aggregation changes no support or branch state.
- S-Det: all folds follow the supplied exact enumeration orders.
- S-Rout/S-Trig: complete bounded/labeled members terminate at CT14 capacity;
  missing semantic prerequisites remain predecessor residuals.
- S-Comp: summing local bounds gives `M ≤ coefficient * carriedTokenMass`;
  tagged incidence injectivity embeds occurrences into `Role × Center`, giving
  `carriedTokenMass ≤ 2 * globalSurplus`.
- S-Rest/S-Meas: no loop or restoration; all checks use supplied local lists.
- Certificate: CT14 capacity terminal, valid trace, total execution, aggregate
  mass theorem, and an honest local quadratic work bound.

## Autonomous lemma-derivation ledger

| Required statement | Exact available inputs | First proof attempt | False subimplication/countermodel | Refined residual | Next invariant/CT route | Discharged by |
|---|---|---|---|---|---|---|
| aggregate actual supports | local bound per support | sum inequalities | `Role × Center` loses multi-center supports | explicit occurrences | CT14 | `Graph.SupportIndexedFanMass` |
| at-most-two center use | within-role disjointness | inject into `Role × Center` | allowing duplicate same-role incidence gives multiplicity three | duplicate tagged incidence | overlap/refinement producer | generic injection theorem; Erdős producer open |
| practical checker bound | nested support/incidence fold | initially claimed linear | uncached token mass scans all incidences per support | exact quadratic local work | optional future cached profile | corrected prototype |

- Methodology level revisited: level 2 after the surrogate and initial runtime
  claims failed audit.
- Granularity change: CT14 members changed from role--center pairs to actual
  supports; center tokens became explicit incidences.
- New reusable contract: `Graph.SupportIndexedFanMass.Profile`.
- Transfer example: `Examples.SupportIndexedFanMass`, with one center reused
  across the two roles but no reuse within a role.
- No missing lemma is carried as an Erdős assumption: the prototype fields are
  an interface contract only; no Erdős profile is constructed.

## Leaf-totality table

| Branch | Exact residual | Local object | CT route | Progress | C1--C5 or typed consumer |
|---|---|---|---|---|---|
| all local bounds and injectivity proved | support-indexed residual mass | finite supports/incidences | CT14 | capacity theorem | C4 |
| extracted support | zero retained contribution | support | predecessor extraction | removed from CT14 mass | typed earlier consumer required |
| failed local coefficient bound | first failing support | actual support and its incidences | semantic repair | not in generic CT14 | producer residual, open for Erdős |
| same-role duplicate center | first duplicate tagged incidence | two actual supports/incidences | overlap/refinement | not in generic CT14 | typed consumer open for Erdős |
| missing grouped family | node `[108]` has no exact family payload | grouped envelope components | producer repair | blocking | no consumer invocation permitted |

## Reused closed-branch routes

No closed Erdős branch is reused in this isolated prototype.  In particular,
the node-`[108]` single handoff is not promoted to a family theorem.

## Practicality

- Local input size: `s = |Support|`, `i = |Occurrence|`, `c = |Center|`.
- Finite alphabet/table size: two roles and the supplied local lists.
- Runtime: the uncached CT14 execution performs
  `2*s*i + 2*s + 1` primitive checks, bounded by
  `3*(s+1)*(i+1)`.  This is polynomial and local, but not linear.
- Certificate: exact enumerations, incidence maps, local inequalities,
  injectivity proof, CT14 trace, and aggregate inequalities.
- Recursion: none.
- No ambient graph universe is materialized: neither graphs, vertex subsets,
  nor all possible supports are enumerated; only the producer-supplied support
  and incidence records are scanned.

## Synchronization after PASS

- Original TeX: not changed; independent red-team and an actual node-`[108]`
  producer are prerequisites.
- Chapter 1 diagram/dependencies: not changed.
- Registers and defect records: not changed.
- Generic Lean: `StructuralExhaustion/Graph/SupportIndexedFanMass.lean`.
- Problem instantiation: deliberately absent.
- Non-target transfer: `StructuralExhaustion/Examples/SupportIndexedFanMass.lean`.
- Web/log: not changed.
- Required commands: build the generic module, transfer module, and umbrella
  framework import.  Record their results in the independent audit.

## Current disposition

The support-indexed global aggregate contract and non-Erdős transfer are ready
for independent red-team review, but they are not the repaired meaning of node
`[84]`: the exact grouped family/incidence producer and the ordinary/grouped
coefficient-208 semantic bounds have not been instantiated from the frozen
Erdős branch.

An Erdős instantiation of `Profile` at this point would therefore be circular:
its `localBound` field would assume the two coefficient-208 lemmas and its
`withinRoleDisjoint` field would assume the missing canonical-family and
incidence-component conclusions.  CT14 would correctly aggregate those
assumptions, but it would not prove node `[84]`.

## Superseding honest contract split

The repair loop therefore narrows node `[84]` to the strongest exact statement
proved by its green incoming edges and moves the unavailable global statement
to a new downstream aggregate frontier.

### Repaired local node `[84]`

For one literal `TypeBSupportScope` and the exact exhaustive route from nodes
`[81]`--`[83]`, node `[84]` now returns exactly one of:

1. an unresolved actual center together with a CT14 singleton-mass stage;
2. the existing nonnegative B2 result;
3. the existing literal negative remaining-core route-8 result; or
4. the exact minimal-overlap result together with a CT14 stage on precisely
   the obstruction's selected center set.

The reusable `Graph.SelectedSurplusMass` profile assigns lower mass one to a
selected center and capacity `degree(center)-3` to that same center.  The
capacity is positive because membership in `scope.Center` proves degree at
least four.  Hence CT14 proves

```text
number of selected actual centers
  <= selected assigned surplus
  <= complete assigned surplus of this exact scope.
```

For a minimal overlap, `selected` is a sublist of the duplicate-free full
center schedule, so conversion to a finite set loses nothing; Lean proves its
cardinality equals the obstruction-list length.  The runner makes exactly
`4 * |highCenters| + 1` profile-operator calls.  Since selected-set membership
is list-backed, the thin instance also records the honest comparison ledger
`4 * |highCenters| * (|selected| + 1) + 1`, bounded by
`5 * (|highCenters| + 1)^2`.  It enumerates no support, subgraph, path, or
graph universe.

### New downstream global frontier

`TypeBGlobalFanMassProducer` is a separate, uninstantiated producer contract.
It must provide the actual support-indexed ordinary/grouped family, exact
center occurrences, coefficient `208`, both semantic per-support bounds, and
tagged within-role injectivity.  Only from such a genuine producer does the
generic theorem yield `residualMass <= 416 * globalSurplus`.

No constructor derives this producer from the repaired local node.  Thus the
local node is green without weakening or silently proving the global
manuscript claim; the global claim remains an explicit downstream mathematical
frontier.

### Lean artifacts for the split

- `StructuralExhaustion.Graph.SelectedSurplusMass`
- `StructuralExhaustion.Examples.SelectedSurplusMass`
- `Erdos64EG.CT14TypeBLocalFanMass`

The source manuscript, diagram, web export, and implementation log remain
unchanged in this isolated repair phase.
