# Part I hot/cold repair: local producer ledger

## Frozen defect

- Manuscript baseline:
  `8910b6c91e7c1e9a83a8bec0ce232204f41274d9392df9e9de893f7a4801287f`.
- Smallest verified predecessor: the same-context
  `VerifiedP13MultiScaleCurvaturePrefix` at node `[21]`.
- Failed implication: the 91 safe/flat row counts do not construct a
  simultaneous completion response or commuting cross-window gluing.
- The original TeX remains unchanged during this repair iteration.

## Paper-faithful structural route

The repair keeps the manuscript's cold-skeleton order:

1. retain the actual selected CT12 window schedule;
2. classify non-cubic windows by a literal strict-surplus position;
3. for every ambient-cubic window, enumerate its fifteen actual external
   incidences in the inherited order;
4. remove exactly the first two transit stubs;
5. split each remaining incidence according to whether its endpoint survives
   deletion of the ambient-cubic selected windows;
6. on the surviving side, construct the complete outside-component boundary
   schedule, choose its true cyclic successor, and compute the declared-order
   shortest component path;
7. retain the other side as an exact cross-window residual;
8. only after the component corridor has its F1--F5 initial-prefix classifier
   and fixed cut-state may bounded overlap and G1/G2/G3 consume it.

`StructuralExhaustion.Graph.InducedPathColdBranchExcess` proves the exact
length-thirteen incidence schedule, no duplication, and unchanged window
ownership. `P13FixedSkeletonBranchExcessCorridors` instantiates that schedule,
but its deleted-edge-return F1/F4/F5 run is only a provisional diagnostic: it
returns to the source window, makes F2 and F3 empty, and uses high degree
rather than the paper's declared-handoff F4. It is not the manuscript corridor
and is not a node-24 input.

The graph-generic correction is
`StructuralExhaustion.Graph.InducedPathBranchExcessComponentEntry`. For one
literal source it returns either the exact
`InducedPathComponentBoundarySchedule.Input` or the retained cross-window
incidence. `P13FixedSkeletonComponentEntries` maps this dichotomy over the
complete thirteen-per-window schedule and proves the exact two-ledger
partition. On the component side, the existing graph layer supplies the
complete incident schedule, true cyclic successor, same-component proof, and
one computed shortest component path. No outcome list or cold family is a
caller field.

## Exact residual after this iteration

The component path is now correct, but its initial-prefix F1--F5 semantics are
not implemented. The provisional `ColdStructuralGerm` remains an ambient-size
deleted-edge-return object and is not the manuscript's constant-size
`ColdBoundedGerm`; bounded overlap is unavailable.

`P13FixedSkeletonComponentD1D3` now maps the exact component-entry ledger to
the existing graph-owned D1--D3 projection.  Every observed constructor keeps
the literal source token, exact component input and state, and a typed
`MissingD4D7Reconstruction`; cross-window constructors pass unchanged.

`StructuralExhaustion.Graph.InducedPathComponentD4` now constructs D4 as the
literal finite family of internal length-two wedges in the stored active
support, with a boundary-window role and the exact `omegaTwo` value of the
three graph-derived attachment labels. `P13FixedSkeletonComponentD4` maps this
producer over every observed entry and retains exact D1--D3 provenance.

The next admitted producer must add D5--D7 on initial prefixes of that explicit
component path. It must return F1 target, F2 distinction, F3
compression, F4 declared handoff, or a terminal/repeated constant-size F5
germ. Only stored corridor positions and declared local clauses may be
inspected; contexts, graphs, states, subgraphs, and Boolean cubes may not be
enumerated.

## Locality

- Branch-excess selection scans the fifteen literal incidences of each cubic
  window once.
- Component entry performs one endpoint-membership decision per retained
  incidence. Only the component constructor invokes the existing local
  schedule/BFS producers.
- The entry schedule has a formal linear bound from
  `13 * cubicWindows <= 13 * p13 <= n`.
- D1--D3 projection over all entries has a formal quadratic envelope; each
  component entry reads two degree rows and thirteen fixed target offsets.
- D4 scans only active-support triples and has a proved `2*n^3` envelope; no
  context family participates in its evaluation.
- The provisional F5 length split is not consumed as a manuscript F5
  certificate.
- `StructuralExhaustion.Examples.InducedPathColdBranchExcess` and
  `StructuralExhaustion.Examples.InducedPathBranchExcessComponentEntry`
  provide non-Erdős transfer coverage.
- `StructuralExhaustion.Examples.InducedPathComponentD4` exercises the exact
  new graph-owned D4 family outside the Erdős application.

## Follow-up local consumers

The cross-window leaf is no longer merely a deleted-endpoint tag.
`Routes.InducedPathCrossWindowIncidencePair` uses the retained membership proof
to recover the endpoint's unique ambient-cubic packed-window slot. Packing
disjointness proves that this owner differs from the source owner, after which
the route constructs the reverse incidence token and proves that the two
distinct cross-window tokens are opposite orientations of one literal edge.
It does not invent an owner-change path, table, or first-hit cursor.

The first aggregate cross-window step is now exact. For each selected window,
the local component/cross-window split proves `A+X=13` and hence `7≤A` or
`7≤X`. On the cross-heavy side, `P13FixedSkeletonCrossHeavyLedger` aggregates
only the actual retained cross-window entries. Their oriented source tokens
are injective locally by duplicate-freeness of the branch-excess schedule and
globally by distinct stored window owners, giving
`7 * card(cross-heavy windows) ≤ card(oriented incidences)` without an ambient
search. The next local scan now classifies every actual oriented token by
whether its incidence-pair reverse occurs in that same selected subschedule.
It either proves full reverse closure or retains the first missing reverse with
its exact clean prefix. On the proof-carrying closed subledger, unordered pairs
have fibre size at most two, yielding the exact factor-two bound over only the
pair labels that actually occur. The missing-reverse branch still needs a
local-interference consumer. Its first exact consumer now locates the reverse
in the destination owner's fifteen-token order: the first two positions are
typed transit, a non-cross-heavy owner routes to the component-heavy
`7`-of-`13` branch, and a cross-heavy owner retains the exact branch-excess
selection mismatch. That mismatch is now discharged locally: reconstructing
the canonical destination-owner corridor shows that its reverse endpoint lies
in the deleted selected-window support, forcing the `crossWindow` constructor,
and the exact nested list memberships place the token in the selected ledger.
Consequently a missing reverse has only the transit or non-cross-heavy/
component-heavy outcomes. The closed branch still needs response-preserving
cross-window gluing; no outcome is silently dropped.

The missing branch is also aggregated without changing its universe. The
exact filtered missing-token list is partitioned by its resolved local
outcome. For each destination owner, opposite-orientation injectivity embeds
the transit fibre into that owner's literal first two tokens, proving fibre
capacity at most two. Every non-transit missing token retains its exact
non-cross-heavy destination owner and the corresponding component-heavy
`7`-of-`13` certificate. No commuting response or Boolean realization is used.

The transit fibres cover and disjointly partition the exact transit-missing
list by the actual destination-owner coordinate. Summing their local capacity
two over the literal ambient-cubic owner order yields
`card(transit missing) ≤ 2 * card(ambient-cubic windows)`. The complementary
non-transit list remains explicit and every one of its members carries the
same exact component-heavy owner route.

D4 now projects to an actual normalized two-boundary state. Available D7 data
is advanced separately: the verified sparse-pair stage is recomputed on the
same minimal context, and only pair supports contained in the current active
interface are retained. Its response profile is context-indexed, so this
support schedule is not mislabelled as a Boolean D7 evaluator.

Independent ownership audits show that full D5 and D6 remain upstream-data
obligations. D5 requires a proved Type A support and canonical receiver-trace
family; D6 requires a proved Type B assigned support plus fan, certificate,
candidate, overlap, and handoff data. Neither follows from the component BFS
path. The repair still fails its full-closure gate.

The first D5 prerequisite has nevertheless been discharged generically:
`Graph.TypeACanonicalReceiverTrace` takes an exact Type A support profile and
constructs one declared-order BFS trace from every internal cubic vertex to
the first internal-degree-at-most-two receiver. The endpoint, shortestness,
path property, and degree-three strict-prefix property are all proved. The
remaining application obligation is to derive that support profile from the
correct branch and then add the completion-port, channel, basin, theta, and
carrier subcoordinates.

The ancestry boundary is now explicit. The component corridor above is not a
Type A support. The first legal Type A source is the manuscript node-`[61]`
negative remainder support followed by the node-`[62]` no-high-center result.
Lean now retains remainder inclusion at node `[61]`, performs node `[62]` as an
exhaustive scan of the actual support, and derives the node-`[63]` Type A
profile without importing data from the later Type B ledger or exit-(7)
handoff. The opposite node-`[62]` result routes the identical support to node
`[64]`.

`P13NegativeSupportLocalization` also installs the CT11 selection step: from
the graph-owned first-occurrence connected-component decomposition, Lean proves
the exact local internal-degree identity and additive point-charge ledger. The
integer charge is at most the upstream natural net numerator even when natural
subtraction truncates. Hence a genuine strict-quarter node-`[24]` handoff gives
CT11 a negative total, CT11 selects node `[61]`, and node `[62]` routes the
identical support to `[63]` or `[64]`. This closes the local implementation of
nodes `[61]`--`[64]` but does not recolor them while their required node-`[24]`
predecessor is white.
