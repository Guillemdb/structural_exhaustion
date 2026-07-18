# Nodes [153]–[154]: cold first-failure and bounded-overlap contract

Status: implementation sketch.  This file freezes the exact local contract
before any change to the live manuscript.  It does not claim the G1–G3
consumers or the node-[24] density conclusion.

## 1. Verified incoming object

For a fixed minimal-counterexample context `ctx`, node [152] supplies the
graph-owned list

```text
p13WeightedColdBranchExcessSchedule ctx node21
```

of thirteen selected post-transit stubs for every retained weighted-cold
ambient-cubic window.  An entry `e` retains:

* its exact `P13WeightedColdCubicWindow` and hence the original weighted-cold
  certificate and selected packing member;
* its exact `CubicStub`, membership in the thirteen-stub tail, and the theorem
  that the stub belongs to the same window; and
* the canonical graph producer
  `P13WeightedColdBranchExcessStub.corridor e`.

The last object currently runs the older deleted-edge-return classifier.  It
is useful for the literal F1 and high-degree tests, but it is not the paper's
component corridor: the paper deletes all retained cold-window interiors,
selects the true cyclic successor boundary stub in the same outside
component, and uses the canonical shortest component path.  The already
implemented `InducedPathBranchExcessComponentEntry.route` is the correct
graph-level producer for that geometry.  The first bridge still owed is
therefore a same-source adapter from each weighted-cold stub to that component
entry; no fresh stub or path may be supplied by a caller.

## 2. Exact branch state

For one source incidence `e`, let `C(e)` be its graph-owned component route.
There are two initial constructors.

1. `crossWindow`: the outside endpoint is in another deleted cold window.
   This is a typed cross-window residual and must enter its existing
   owner-change/reverse-incidence analysis.  It cannot be relabelled F5.
2. `component`: the route carries the complete incident boundary schedule,
   the true cyclic successor, and one canonical shortest path in the shared
   outside component.  Only this constructor enters F1–F5.

For the component constructor, the stage list is the ordered list of initial
segments of the stored component path, including the two boundary stubs and
the bounded window-interface data.  Every stage retains the same source
incidence, successor, component and path; this is the provenance invariant
used by all five outcomes.

## 3. The five prioritized outcomes

At each stage, in order, inspect:

* **F1 (target hit).** A displayed completion at one of the thirteen offsets
  is a literal simple cycle in `ctx.G.object.graph` and its length satisfies
  `PowerOfTwoLength`.  Output the cycle, offset, source incidence and stage.
* **F2 (response distinction).** Two prefixes with identical displayed
  two-boundary data admit one *literal compatible context* in which their
  target responses differ.  Output both prefixes, the shared boundary data,
  that context, its compatibility proof and the Boolean/Propositional
  response discrepancy.  The context is a proof-selected witness; no ambient
  context universe is enumerated.
* **F3 (silent proper exchange).** The same prefix pair has equal target
  response for every compatible context, equal boundary-degree profile and a
  strictly smaller proper representative satisfying the internal baseline and
  internal target-free conditions.  Output the full CT3/replacement payload,
  not merely equality of the coarse state code.
* **F4 (named handoff).** The stage first meets a previously declared Type-B
  envelope or route-8 carrier.  Output the exact pre-existing ledger key and
  its membership proof.  A high-degree vertex alone is only a surplus
  payment; it is not automatically a Type-B handoff.
* **F5 (bounded germ).** All earlier stages are negative for F1–F4 and either
  the successor is reached within the fixed state bound or the first repeated
  exact cut-state is found.  Output the support between the certified
  endpoints, its two interfaces, its two same-interface representatives, all
  inherited labels, a bound by `M_cold`, and the exact response/reflection data
  needed by the G1–G3 classifier.

Priority is part of the output: an Fk constructor carries negative evidence
for every earlier Fi at the same stage, and the canonical first-hit record
carries absence of every event on every earlier stage.

## 4. Totality and ledger disjointness

The implementation must prove, for every component entry:

```text
F1 source ⊕ F2 source ⊕ F3 source ⊕ F4 source ⊕ F5 source
```

as the output of one `FiniteFirstFailure.Profile.run`, not as caller-supplied
case data.  F5 is constructed from the exhaustive negative scan.  Mapping
this runner over the exact node-[152] schedule must prove:

* length preservation;
* a five-way exact partition of the schedule;
* each output's source is the identical input entry;
* no source occurs twice (inherited from the duplicate-free weighted-cold
  window schedule and the thirteen distinct tail stubs); and
* the total local work is the sum of the stored stage-list lengths.

Cross-window component-route outputs remain a sixth, earlier typed ledger and
are not counted in the five-way component partition.

## 5. Bounded-overlap contract

Let `Candidate` be the finite subtype of F5 outputs in the exact executed
ledger and let `support : Candidate -> Finset ctx.G.Vertex` be the stored germ
support.  The paper needs two independently proved bounds:

```text
support item |<= M_cold
card { item | vertex in support item } |<= B_cold
```

The second bound is the only graph-geometric counting obligation.  It must be
proved locally from:

* subcubicity of every surviving F5 support;
* containment of any source whose support contains `v` in the radius
  `M_cold + 2` ball about `v`;
* the subcubic ball bound `1 + 3 * (2^(M_cold+2) - 1)`; and
* at most fifteen external source stubs per ambient-cubic window.

No graph, path, support or context family is globally enumerated.  Once these
two bounds are available, a reusable finite lemma proves that every fixed
support meets at most `M_cold * B_cold` supplied supports.  Maximal disjoint
packing then gives

```text
Candidate.card / (M_cold * B_cold + 1) <= selected.card.
```

The `+1` is necessary because the overlap fibre includes the selected support
itself.  This is the exact finite version of node [154]'s `D_cold` payment.

## 6. Typed handoff to G1–G3

Each selected disjoint F5 item must construct
`P13ColdGermLedger.ColdBoundedGerm`, including:

* the literal proper atom and replacement;
* equal boundary-degree profiles;
* internal target-freeness and baseline;
* strict local decrease;
* an optional literal F1 hit;
* a finite *germ-local* response-code table; and
* a reflection theorem covering every compatible literal outside context.

The final field is not implied by coordinatewise activity or equality of the
coarse cut-state.  It must come from the F2/F3 pair comparison: a witnessed
failure is F2; exhaustive equality is the F3/G3-side semantic certificate.
This handoff feeds the existing G1–G3 classifier but does not itself close any
G branch.

## 7. Missing-lemma ledger

| ID | Owner | Required lemma | Inputs | Output / consumer |
|---|---|---|---|---|
| C153.1a | Graph + Erdős thin adapter | weighted stub to exact cold-family endpoint decision | one entry of node-[152] schedule | cold-deleted or cold-outside result with same-source equality; discharged |
| C153.1b | Graph | restricted-family component schedule | exact cold-family outside boundary | cyclic successor and canonical BFS component path in that same restricted outside graph |
| C153.2 | Graph | component-path prefix filtration | stored component input/path | ordered, duplicate-free prefix stages and support monotonicity |
| C153.3 | Graph/Erdős | F1 completion soundness | one prefix and offset | literal simple dyadic cycle |
| C153.4 | Routes | F2 target-defect route | exact compatible-context distinction | sparse-exit or exit-(4) payload with context retained |
| C153.5 | Routes | F3 compression route | target-complete proper exchange | exact CT3/replacement input and strict decrease |
| C153.6 | Erdős adapter | F4 ledger recognition | prefix plus inherited Type-B/route-8 ledgers | exact existing ledger key |
| C153.7 | Core | five-way executed-ledger partition | finite first-failure runner over exact sources | totality, disjoint tags, provenance and local work |
| C153.8 | Core | support-size × point-multiplicity overlap | finite nonempty supports, bounds `M`,`B` | overlap fibre at most `M*B` |
| C154.1 | Graph | subcubic ball cardinality | local radius and degree-at-most-three proof | `1+3(2^r-1)` vertex bound |
| C154.2 | Graph/Erdős | F5 point multiplicity | exact source schedule and C154.1 | at most `B_cold` candidates through one vertex |
| C154.3 | Core | disjoint extraction | C153.8 with self-overlap | division bound with `D_cold=M*B+1` |
| C154.4 | Erdős thin adapter | F5 to `ColdBoundedGerm` | exact F5 exchange/reflection payload | typed G1–G3 input |

The dependency-ready work is C153.7, C153.8 and C154.3.  They are generic
finite bookkeeping and belong in `StructuralExhaustion.Core`.  C153.2–C153.6
and C154.1–C154.4 are mathematical producer obligations; none may be replaced
by author contracts when nodes [153]–[154] are eventually marked green.
C153.1 is discharged by the same-source adapter in Section 9; C153.2–C153.6
and C154.1–C154.4 remain open.

## 8. Local computation and termination

The first-failure runner scans only the stored prefix list of one supplied
component path.  F2 uses a proof-selected distinguishing context and F3 uses
universal response equivalence as a proposition; neither enumerates ambient
contexts.  The aggregate runner traverses the exact selected-stub ledger once.
The overlap extractor uses the finite subtype of already produced F5 items
and proof-level maximal packing.  Termination is list recursion; the visible
work measure is the sum of prefix-list lengths plus the finite candidate and
overlap ledgers.

## 9. C153.1 correction: the deletion family is weighted-cold, not ambient-cubic

The first C153.1 prototype called
`InducedPathBranchExcessComponentEntry.route` on the correct source stub, but
that graph producer deletes the supports of **all** ambient-cubic selected
windows.  The paper defines `X_cold` using only
`p13WeightedColdCubicWindows`.  These are not equivalent: a hot
ambient-cubic window is removed by the old producer but survives the paper's
deletion.  Hence the old `P13WeightedColdComponentEntries` module is only an
auxiliary all-ambient-cubic classifier and does not discharge C153.1.

The corrected graph contract is
`InducedPathRestrictedColdSkeleton.CubicWindowFamily`.  It takes an explicit
finite set of selected window indices and proves every member ambient-cubic.
It defines the deletion union, outside induced graph, boundary stub and
endpoint dichotomy relative to exactly that family.

For Erdős, `p13WeightedColdWindowFamily` is built from the literal
`p13WeightedColdCubicWindows` list.  Every entry of the exact node-[152]
schedule carries a membership proof showing that its source window belongs to
this family.  `p13WeightedColdRestrictedEntries` then returns exactly:

* `componentBoundary`: the identical source token and proof that its endpoint
  survives deletion of weighted-cold cubic windows only; or
* `crossWindow`: the identical source stub and proof that its endpoint lies in
  the weighted-cold deletion union.

The output gives an exact two-way partition, performs one cold-union membership
test per source and has total visible work at most the ambient vertex count.
No paths or components are accepted from a caller.

This discharges the **endpoint-deletion half** C153.1a.

## 10. C153.1b: restricted component schedule and canonical path

`InducedPathRestrictedComponentBoundarySchedule` carries the same explicit
`CubicWindowFamily` through every structural object.  From a C153.1a
`componentBoundary` it:

1. uses the all-darts non-bridge theorem to scan one deleted-edge return;
2. finds the first edge leaving the anchor component in the restricted outside
   graph;
3. identifies the other endpoint in a window belonging to the same explicit
   family;
4. enumerates only literal boundary tokens whose windows belong to that
   family and whose endpoints survive that family's deletion;
5. filters this schedule by the one computed outside component and chooses the
   true cyclic successor in its stored order; and
6. runs declared-order BFS inside that same component to obtain a certified
   simple shortest path.

`P13WeightedColdRestrictedComponentSchedule` consumes every exact C153.1a
entry.  Its component constructor stores the restricted input derived from the
same source token; its cross-window constructor remains unchanged.  The
component payload proves token identity, successor distinctness, component
identity, path simplicity and shortestness.  The stored path support is
bounded by the explicit component carrier cardinality.

The scans are local: one supplied return, `WindowIndex × Fin 13` for its first
family slot, the literal selected-incidence token order, and two BFS runs on
the restricted outside/component graphs.  No path family, graph family or
ambient completion family is enumerated.  This discharges C153.1b.  C153.2 may
now construct its ordered prefix stages from this exact `componentPath`; the
cross-window constructor must not enter that filtration.

## 11. C153.2: exact ordered prefix geometry

`WalkPrefixFiltration.Profile` consumes one already produced simple path.  Its
stage type is exactly

```text
Fin componentPath.support.length
```

and the stage at index `i` retains
`componentPath.support.take (i+1)`.  Consequently the stage order is the
stored path-position order, the stage list is duplicate-free, every prefix is
nonempty and duplicate-free, and prefix supports are nested monotonically.
The runner does not enumerate walks or accept a prefix list.

`P13WeightedColdRestrictedPrefixPackage` can be constructed only from a
C153.1b component payload.  It retains the identical source entry, boundary,
restricted input and route equalities; its path is not a caller field.  The
source token remains the original node-[152] stub, and every prefix is a
literal subset of the canonical restricted component path.  Visible work is
one descriptor per path-support vertex and is bounded by the explicit
component-carrier cardinality.

This discharges C153.2's geometry only.  It intentionally defines no F1--F4
predicate, response context, cut-state, replacement, handoff, or bounded F5
germ.  Those begin at C153.3.

## 12. C153.3: literal local F1 completion, and the residual it exposes

`InducedPathRestrictedPrefixCompletion` maps each stored restricted-component
prefix through the two canonical induced-subgraph inclusions into the original
graph.  At a pair `(stage, offset)` it recognizes F1 only if:

1. the prefix has positive length;
2. its actual endpoint is adjacent in the original graph to the displayed
   vertex of the anchor `P13`; and
3. the exact length
   `prefix.length + 2 + positionDistance anchor.offset offset` is accepted.

The prefix is simple and lies outside the entire weighted-cold deletion, hence
is disjoint from the anchor window.  The anchor token supplies the first
attachment edge, and condition 2 supplies the second.  The existing reusable
`InducedPathConnectorCycle.connectorCycle` therefore constructs a literal
Mathlib simple cycle in the original graph.  The Erdős adapter specializes the
accepted predicate to `PowerOfTwoLength`.  Its production continuation is
stage-major: in stored prefix order, it first scans the canonical
`List.finRange 13` offset order and retains the first literal F1 hit, then
checks F2, F3 and F4 at that same prefix.  The older global stage-product F1
scan remains only an auxiliary audit, because using it as a prepass could let
a later F1 outrank an earlier F2.  Visible F1 work is at most thirteen local
tests per stored prefix descriptor.

This discharges the soundness and ordered-search part of C153.3.  It also
isolates a manuscript premise which must not be silently assumed: a numerical
fact `PowerOfTwoLength (ell + offset)` does not supply the endpoint-to-window
edge at that offset.  A fixed self-return has its two actual attachment
positions and therefore one actual window-segment distance; it does not, from
that fact alone, realize every distance from zero through twelve.  Arithmetic-
only target bits with no displayed return edge are a typed non-F1 residual.
Closing the manuscript's stronger short-self-return "whole interval" claim
requires a separate structural lemma producing the corresponding thirteen
actual completions; it is not part of the literal F1 constructor.  The
stage-major `FiniteFirstFailure` profile and its exhaustive F5 construction
are implemented as a parameterized continuation contract.  Node [153] remains
open until the graph/route-owned F2--F5 semantic producer constructs the exact
response distinctions, replacement data, ledger keys and terminal/repeated
germ; quantifying over that contract is not an unconditional node proof.
