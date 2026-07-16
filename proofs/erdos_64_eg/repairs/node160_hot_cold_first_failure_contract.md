# Node [160] repair sketch: symbolic hot realization or graph-owned first failure

Status: separate repair worksheet only. This file does not change the source
manuscript, Lean implementation, web companion, theorem index, or node color.
Node `[160]` remains white until every exit test at the end of this document
passes.

## Defect freeze

- **Defect ID:** EG-P13-160-HOT-COLD-FIRST-FAILURE.
- **Stable node:** `[160]`, between the verified node-`[21]` multi-scale
  curvature prefix and the still-open nodes `[22]`--`[24]`.
- **Smallest verified ancestor:**
  `VerifiedP13MultiScaleCurvaturePrefix ctx` on the bounded-surplus
  constructor of the node-`[19]` route.
- **Classification:** design defect D. The application repair is level 2; a
  reusable symbolic extension/first-obstruction interface is a candidate
  level-3 addition.
- **Immutable blast radius:** nodes `[22]`, `[23]`, and `[24]` may not use a
  window entropy payment, commuting product, `U13`, or density ceiling from
  this branch. Nodes `[158]` and `[159]` are a parallel thirteen-coordinate
  actual-attachment continuation and do not repair `[160]`.
- **Source manuscript frozen:** yes.

### The false quantifier

Let `I` be the exact 91-element type `P13BarrierIndex`. Node `[21]` supplies
finite safe and flat relation counts `W_i` and `F_i`, their audited semantics,
and

```text
2^118 * product_i F_i < product_i W_i.
```

The invalid inference was

```text
(for every i, the row W_i/F_i is defined and audited)
  implies
(there exist one finite completion family S and rho : S -> (I -> Bool)
 such that for every epsilon : I -> Bool there exists s : S with
 rho(s) = epsilon).
```

The right-hand side is a simultaneous surjectivity statement. It is not an
injection statement, a rank statement, coordinatewise two-valuedness, or a
consequence of 91 independent count identities. The response set
`{00, 11}` is the two-coordinate counterexample: both coordinate projections
contain both bits, while `01` and `10` are absent.

The exact negation, once a genuine graph-owned system exists, is

```text
exists epsilon : I -> Bool, forall s : S, rho(s) != epsilon.
```

This repair does **not** find `epsilon` by enumerating `I -> Bool`. Instead it
requires either a symbolic extension theorem, quantified over a supplied
assignment but executed along only its 91 coordinates, or a graph-produced
first extension obstruction. The failed bit is part of the obstruction
output; it is never a caller-authored branch flag.

## Surviving directed branch state

Write the active state as

```text
B160 = (H0, order, exits, invariants, residual, vocabulary, queue, artifacts).
```

- `H0`: `ctx` is the inherited lexicographically minimal packed finite
  counterexample, has minimum degree at least three, and avoids every
  power-of-two cycle.
- `order`: the inherited packed-graph lexicographic rank. The proposed local
  construction adds a separate finite measure, the number of unprocessed
  barrier coordinates; it does not replace the graph order.
- incoming path: target avoidance, the verified minimality prefix, induced
  `P13` realization, CT12 maximum induced-`P13` packing, the 399-label CT10
  algebra, the node-`[19]` squared-scale split, its bounded-surplus
  constructor, and node `[21]`.
- certified absent exits: literal target hits and certified smaller
  target-complete replacements remain excluded exactly where the ancestor
  excludes them. No new exclusion is inferred from node `[160]`.
- inherited invariants: the exact selected CT12 packing, its `P13`-free
  remainder, the 399 legal labels, the exact 91 barrier indices, the safe and
  flat row semantics and counts, the strict product rate floor, and the
  bounded-surplus ledger.
- exact residual: a node-`[21]` bounded-surplus target-avoiding graph and one
  exact selected packed window, before any 91-coordinate completion system,
  Boolean realization, or cross-window gluing has been constructed.
- finite vocabulary: `SelectedP13Window ctx`, `P13BarrierIndex`, its declared
  `FinEnum` order, `Fin 13` window positions, 399 labels, finite supports,
  finite boundary profiles, partial completion certificates, Boolean
  prefixes, and first local extension obstructions.
- queue: a verified hot window may enter the hot gluing layer; a verified
  first obstruction may enter only the new completion-obstruction consumer
  described below.
- artifacts: the node-`[21]` Lean certificate and audits,
  `P13MultiScaleBitSemantic`, `P13SequentialEntropyFiltration`,
  `P13MultiScaleConnectorState`, and the generic Boolean entropy theorem.

Facts explicitly unavailable on this path are a completion-state producer,
a two-valued graph toggle, a simultaneous 91-response reflection theorem, a
cross-window commuting gluing theorem, terminal-fibre nonemptiness, and a CT
trigger derived merely from a cardinality inequality. The thirteen-bit actual
attachment fork belongs to the parallel `[158]`--`[159]` route and is not an
input here.

## Resource inventory

| Resource | Producer | What it may pay for | What it does not pay for |
|---|---|---|---|
| Exact barrier order and cardinality 91 | node `[21]` / CT10 | bounded coordinate schedule | Boolean assignments or completion states |
| Safe/flat relation rows and counts | node `[21]` | response-reflection target and arithmetic checks | state existence or surjectivity |
| Strict product rate floor | node `[21]` | a later nonvacuous hot entropy comparison | terminal nonemptiness or gluing |
| Selected windows | CT12 | exact window provenance and packed supports | disjointness of completion supports not yet defined |
| Target avoidance | `ctx` | rejection of a literal constructed target | arbitrary missing-bit promotion |
| Minimality | verified prefix | a certified strictly smaller target-complete replacement | existence of such a replacement |
| Fixed relation evaluator | `P13MultiScaleBitSemantic` | one-coordinate semantic reflection | simultaneous modification of 91 coordinates |
| Literal two-piece gluing | `Graph.PackedBoundariedGluing` | exact normalized edge ownership after its hypotheses are proved | multi-window commutation |

The bookkeeping-versus-theorem test rejects “the 91 counts realize the
cube”: that is the missing graph theorem restated globally. The admissible
bookkeeping step is only the traversal of an already certified local
extension interface.

## Three-layer producer contract

The notation below is a proposed Lean-facing contract. Names are provisional;
the quantifier order and ownership fields are not.

### Layer 1: graph-owned completion system and reflection

For `previous : VerifiedP13MultiScaleCurvaturePrefix ctx` and one exact
`window : SelectedP13Window ctx`, define:

```text
structure P13CompletionSystem (ctx) (previous) (window) where
  State : Type u
  states : FinEnum State
  completion : State -> P13CompletionDatum ctx window
  admissible : forall s,
    P13CompletionAdmissible ctx window (completion s)
  response : State -> P13BarrierIndex -> Bool
  response_reflect : forall s i,
    response s i = true iff
      P13CompletionFlatResponse ctx previous window (completion s) i
  predecessorExact : the response rows are the exact node-[21] rows
  windowExact : every completion has the declared selected-window boundary
  checks : Nat
  checks_bound : checks <=
    91 * states.card * P13CompletionDatum.localCheckCost
```

`P13CompletionDatum` must be one simultaneous, bounded, graph-owned
completion with its exact finite support, boundary profile, owned edges, and
local admissibility certificate. It may not be:

- an arbitrary `FinEnum State` supplied at the Erdős theorem;
- a function choosing an unrelated connector for every barrier;
- a list of all graphs, subgraphs, outside contexts, or colorings; or
- `P13ConnectorSequence`, whose current enumeration has an `n^15` envelope
  and whose accepted flat bit is always true by target avoidance.

The system may use a proof-carrying explicit state list. Its checker scans
that list and the 91 fixed relations. It does not construct a universe of
ambient graphs.

#### Prefix and extension objects

Let `schedule := p13BarrierClassification.classes.orderedValues`. A partial
state at depth `k` carries:

```text
structure P13PartialCompletion (k : Nat) where
  prefix : List Bool
  prefix_length : prefix.length = k
  datum : P13PartialCompletionDatum ctx window
  supportOwned : ...
  admissible : ...
  reflectsPrior : forall j < k,
    responseAt datum schedule[j] = prefix[j]
```

A graph-owned local extension certificate has exactly two positive moves or
one negative move:

```text
inductive P13ExtensionDecision (p : P13PartialCompletion k) (i : I)
  | both
      (zero : P13PartialCompletion (k+1))
      (one  : P13PartialCompletion (k+1))
      (zeroExtends : Extends p zero false)
      (oneExtends  : Extends p one true)
  | obstructed
      (failedBit : Bool)
      (noExtension : forall q,
        Extends p q failedBit -> False)
      (semanticFailure : P13LocalCompletionObstruction ctx previous window i)
```

The crucial producer theorem must be graph-owned. It cannot be a generic
decision over all Boolean prefixes:

```text
P13SymbolicExtensionCertificate ctx previous window
```

contains either

```text
extend : forall k < 91, forall p : P13PartialCompletion k,
  forall bit : Bool, exists q, Extends p q bit
```

or a concrete least obstruction containing `k`, `p`, `schedule[k]`, and the
failed bit. In the hot constructor, `bit` is a bound variable of the theorem;
in the cold constructor it is output data derived from the failed graph move.
There is no Boolean “hot/cold” argument.

An arbitrary black-box response table cannot produce this dichotomy without
examining exponentially many prefixes. Therefore the certificate must be
derived from a uniform local graph lemma or accompanied by a locally checked
proof certificate. Merely defining the inductive type does not make node
`[160]` green.

### Layer 2: hot-only realization and commuting gluing

From the uniform extension constructor, recurse on the 91-element schedule
for a *supplied symbolic assignment*:

```text
structure P13HotWindow (system : P13CompletionSystem ...) : Prop where
  realizes : forall assignment : P13BarrierIndex -> Bool,
    exists state, system.response state = assignment
```

Evaluation of `realizes assignment` follows one path of length 91. The theorem
quantifies over assignments but does not enumerate them. A verified
`P13HotWindow` converts directly to
`Core.BooleanStateEntropy.Profile`; it must not invoke
`Core.LocalBooleanRealization.System.classify`, whose assignment universe has
cardinality `2^91`.

Hot windows do not yet give a product. The cross-window layer is separate:

```text
structure P13CommutingWindowGluing
    (system : forall w : SelectedP13Window ctx,
      P13CompletionSystem ctx previous w)
    (hot : forall w, P13HotWindow (system w)) where
  GlobalState : Type u
  globalStates : FinEnum GlobalState
  glue : (forall w, (system w).State) -> GlobalState
  admissible : forall choice, GlobalAdmissible (glue choice)
  responsePreserved : forall choice w i,
    globalResponse (glue choice) w i = (system w).response (choice w) i
  recover : forall choice w, restrict (glue choice) w = choice w
```

`recover` proves injectivity of `glue`; `responsePreserved` proves that local
realizations commute. These fields require exact support/boundary ownership,
not just vertex-disjoint selected path supports. Only this layer may feed the
window-product entropy account used downstream of `[160]`.

### Layer 3: cold first-failure residual

The cold payload is the least failed local extension, not a bare omitted
assignment and not an arithmetic ratio failure:

```text
structure P13ColdFirstFailure (ctx) (previous) (window) where
  prior : List P13BarrierIndex
  index : P13BarrierIndex
  suffix : List P13BarrierIndex
  scheduleExact : schedule = prior ++ index :: suffix
  prefix : List Bool
  prefixLength : prefix.length = prior.length
  partial : P13PartialCompletion prefix.length
  partialReflects : ...
  failedBit : Bool
  noExtension : forall q,
    Extends partial q failedBit -> False
  first : every earlier scheduled extension in this construction succeeded
  semanticFailure : P13LocalCompletionObstruction
    ctx previous window index
```

Define `omitted : P13BarrierIndex -> Bool` by the proved prefix, followed by
`failedBit`, followed by `false` on the canonical remaining schedule. Then
prove

```text
forall state : system.State, system.response state != omitted.
```

This proof uses `noExtension` at `index`; it does not scan the Boolean cube.
The selected bit is part of the graph-produced obstruction. The canonical
false tail is used only to totalize the already obstructed prefix and is not a
caller decision.

`semanticFailure` must be a data-carrying sum whose constructors expose the
first exact failed graph clause:

```text
MissingLocalMove
BoundaryProfileMismatch
OwnedSupportOverlap
CrossEdgeInterference
EarlierResponseChanged
AdmissibilityFailure
```

Each constructor stores the relevant completion pieces, boundary labels,
support vertex or edge, before/after response, and proof of failure. An enum
tag with none of those witnesses is insufficient.

## Both-sides test

| Predicate | Positive payment/account | Negative bounded residual | Measured from | Typed consumer | Admit? |
|---|---|---|---|---|---|
| Uniform two-bit extension at every partial prefix | symbolic 91-bit hot realization | least graph-owned extension obstruction | proof-carrying extension certificate and 91-stage order | hot layer / completion-obstruction consumer | selected contract; producer theorem open |
| Complete response surjectivity of an arbitrary finite state table | Boolean entropy | first missing vector | would require the assignment cube | CT10 was proposed | rejected: `2^91` and CT10 cannot invent graph semantics |
| Every sequential ratio pays | telescoping product inequality | first arithmetic failing fibre | supplied state list | CT6/CT10 was proposed | rejected here: neither side supplies completion semantics or nonvacuity |
| Completion supports commute | cross-window injection and response preservation | first witnessed ownership/interference clause | explicit completion supports and boundaries | completion-interference consumer | selected only after layer 1 exists |
| A fixed relation row reflects one response | node-[21] semantic alignment | explicit reflection mismatch | 399-label local bit relations | layer-1 producer repair | selected supporting invariant |

The selected invariant sits before cube realization on the invariant ladder:
first certify the local graph move and its persistence, then construct the
symbolic realization theorem, and only then perform entropy bookkeeping.

## Typed outputs and declared consumers

### Hot output

Payload:

```text
(ctx, previous, window, system, hotCertificate)
```

- S-Rout: `hotCertificate.realizes` constructs the exact
  `BooleanStateEntropy.Profile` for that window.
- S-Trig: the global entropy consumer additionally requires
  `P13CommutingWindowGluing`; without it the payload stops at the hot-window
  ledger and makes no product claim.
- Consumer: the repaired node-`[22]` hot-window entropy account, only after
  its gluing and scale-multiplicity fields are implemented.

### Cold output

Payload:

```text
(ctx, previous, window, prior, index, prefix, partial, failedBit,
 noExtension, semanticFailure)
```

- S-Rout: preserve the exact constructor of `semanticFailure`; do not erase it
  to `Prop` or replace it by `exists omitted`.
- S-Trig: a consumer may run only on the matching constructor and must receive
  the two comparison pieces/context/refinement datum required by its CT.
- Consumer: a new reusable `Graph.LocalCompletionObstruction` classifier,
  whose outputs are typed target hit, certified smaller replacement,
  distinguishing-context pair, or a strictly refined finite obstruction.
  Bare overlap, boundary mismatch, or response change is not by itself a CT3,
  CT7, or CT10 trigger.

The cold consumer is therefore a level-3 interface obligation, not an already
closed route. It must provide S-Rout/S-Trig lemmas and a non-Erdős transfer
example before `[160]` can be green.

## CT / interface worksheet

- **Instance:** node `[160]`, one selected window, one first failed
  91-coordinate completion extension.
- **Input:** exact `VerifiedP13MultiScaleCurvaturePrefix ctx`, exact selected
  window, graph-owned partial completion, and the node-`[21]` barrier order.
- **Parameters:** coordinate order is fixed by
  `p13BarrierClassification.classes.orderedValues`; no synthesized assignment
  order and no caller branch flag.
- **S-Def:** `P13CompletionDatum`, `P13PartialCompletion`, `Extends`, response,
  and the six graph failure constructors.
- **S-Dich:** uniform extension of either bit at every next coordinate, or the
  least certified failed extension.
- **S-Equiv:** `response_reflect` identifies each completion response with the
  exact fixed node-`[21]` relation predicate.
- **S-Pers:** an extension preserves the selected window, boundary ownership,
  admissibility, and all earlier response coordinates.
- **S-Det:** the coordinate is the first failed member of the fixed 91-entry
  order; the failure-clause order is fixed as move, boundary, overlap,
  cross-edge, response, admissibility.
- **S-Rout:** hot to symbolic realization; cold to the data-preserving
  completion-obstruction classifier.
- **S-Trig:** hot entropy needs commuting gluing; each cold constructor must
  prove the full target consumer trigger rather than a resemblance lemma.
- **S-Comp:** 91 successful symbolic extensions compose to one completion
  realizing the supplied assignment.
- **S-Rest:** each extension leaves all inherited ancestor fields and earlier
  responses unchanged.
- **S-Meas:** `91 - k`; every successful extension increases `k` by one.
- **Certificate:** uniform extension proof or concrete first obstruction,
  together with local support, boundary, adjacency, response, and
  admissibility checks.

No existing CT consumes the raw six-way obstruction sum. The proposed
interface must be reviewed at level 3. CT3, CT7, or CT10 becomes a downstream
consumer only after a constructor-specific theorem builds its exact trigger.

## Autonomous lemma-derivation ledger

| Required statement | Exact inputs | Rejected attempt | Refined residual | Required discharge |
|---|---|---|---|---|
| Graph-owned finite completion family | node `[21]`, selected window, fixed graph | use 13-bit actual attachments or `n^15` connector sequences | simultaneous bounded completion datum | construct and locally verify `P13CompletionDatum` |
| Uniform extension for both bits | one valid partial completion and next barrier | infer from safe/flat counts | first missing local move | graph toggle lemma or typed obstruction |
| Complete 91-bit realization | uniform extension | run `LocalBooleanRealization.classify` | symbolic assignment recursion | theorem recursing for 91 steps only |
| Cross-window product | hot local systems and CT12 path supports | assume selected supports imply completion supports commute | first explicit interference clause | owned multi-window gluing or alternate global charge |
| Cold CT route | missing assignment or arithmetic fibre | relabel as CT10/CT7 | graph-semantic first failure | constructor-specific trigger theorem |
| Nonvacuous entropy payment | hot system and rate floor | use a complete filtration with empty terminal fibre | actual realized completion | derive from hot realization, then prove scale/gluing account |

No rejected statement is retained as a hypothesis. The contract exposes the
next finite obstruction and changes granularity from complete Boolean vectors
to one graph extension step.

## Local computation and termination

- Coordinate input size: exactly 91 barriers, represented by the already
  verified node-`[21]` `FinEnum`.
- Relation alphabet: 399 labels and fixed sparse compatibility rows.
- One response check uses the fixed local relation evaluator; it does not
  inspect all graphs or all outside contexts.
- A supplied completion-certificate table is checked in
  `O(91 * numberOfStates * localResponseCost)`.
- Realizing one symbolic assignment performs exactly 91 extension
  applications, plus local certificate checks.
- Checking one cold certificate scans its prefix of length at most 90 and one
  failed local clause.
- Cross-window checking, once pieces exist, scans the selected windows and
  their explicit finite supports/owned incidences. Its bound must be stated in
  those support sizes, not in a graph-universe cardinality.
- The recursion measure is the number of unprocessed coordinates and strictly
  decreases from 91 to 0.

There is no executable scan over `P13BarrierIndex -> Bool`; in particular
there is no factor `2^91`. There is no enumeration of `SimpleGraph`, subgraph,
coloring, completion, or context universes. If the only available method to
produce the uniform extension certificate enumerates all Boolean prefixes,
the method fails the practicality gate and node `[160]` remains white.

## First implementable framework unit

The first dependency-ready reusable subunit is now the proof-level
`Core.FinitePrefixExtension` contract with:

1. a finite ordered coordinate list;
2. prefix-indexed symbolic states representing all admitted prefixes at that
   depth rather than a list of assignments;
3. an application-owned extension step returning either the next symbolic
   family or a graph-derived obstruction;
4. a complete extension ledger;
5. a first-obstruction record with the exact clean coordinate prefix; and
6. a reference runner with one visible call per supplied coordinate.

This subunit and its non-Erdős hot/cold fixture are implemented in
`StructuralExhaustion.Core.FinitePrefixExtension` and
`StructuralExhaustion.Examples.FinitePrefixExtension`.  It intentionally does
not manufacture a realization function or an omitted assignment: those require
the application to prove that its symbolic state really represents both bit
extensions and that its obstruction has the claimed graph semantics.

The transfer example uses a four-coordinate non-Erdős prefix system and pins
both the complete and first-obstruction outcomes.  The framework unit makes no
claim that an arbitrary finite response table admits a polynomial hot/cold
classifier.

The first application unit is the thin `P13CompletionSystem` specification
and exact response-reflection statement. It is not a green node until the
selected graph constructs its `State`, completion data, local extension
certificate, and obstruction semantics.

## Leaf-totality table

| Branch | Exact output | Progress | Endpoint |
|---|---|---|---|
| Uniform extensions through all 91 coordinates | `P13HotWindow` | one realized completion per symbolic assignment | typed hot handoff; requires commuting gluing before entropy product |
| First local extension failure | `P13ColdFirstFailure` with graph constructor | shorter processed schedule and explicit obstruction | typed level-3 obstruction consumer; not yet C1--C5 |
| Cross-window gluing succeeds | injective global response-preserving state map | product account | node-`[22]` hot consumer after scale account |
| Cross-window gluing first fails | explicit support/boundary/edge/response interference | named local witness | typed interference consumer; not yet C1--C5 |

This table is intentionally not yet closed. It records the exact remaining
producer and consumer obligations instead of coloring `[160]` green.

## Exit tests before any merge

All tests below are mandatory.

1. **Provenance:** every completion, prefix, response, and obstruction is
   constructed from `ctx`, `previous`, and the exact selected window; no raw
   Erdős theorem argument supplies `State`, `response`, `Bool`, or an outcome.
2. **Quantifiers:** Lean states `forall assignment, exists state` on the hot
   branch. No injection, rank, pairwise distinction, or coordinatewise choice
   is substituted for it.
3. **No cube enumeration:** focused code inspection shows no `FinEnum
   (P13BarrierIndex -> Bool)`, `LocalBooleanRealization.classify`, Boolean
   prefix tree traversal, or `2^91` work term.
4. **Locality:** all executable searches range only over the 91 rows, 399
   labels, explicit proof-supplied completion certificates, and their finite
   supports.
5. **Reflection:** every response bit has a proved iff theorem to the exact
   node-`[21]` safe/flat graph predicate.
6. **Persistence:** extending or gluing a completion preserves all earlier
   responses, boundary ownership, admissibility, target avoidance, and exact
   selected-window provenance.
7. **Hot payment:** realization is nonvacuous; the commuting gluing theorem,
   scale multiplicity, and exact downstream cardinality account compile before
   any window-density claim is restored.
8. **Cold route:** every failure constructor preserves its witness as data and
   proves the full trigger of one registered consumer. Bare arithmetic,
   overlap, or a missing vector is not accepted as CT3/CT7/CT10 input.
9. **Framework placement:** generic symbolic recursion and obstruction logic
   live in Core/Graph, with a non-Erdős transfer example; Erdős code contains
   only concrete graph data and thin instantiation.
10. **Trust and practicality:** focused searches find no `sorry`, `admit`, new
    axiom, `unsafe`, ambient-universe enumeration, or hidden exponential
    classifier. Local work bounds are compiled theorems.
11. **Synchronization:** only after a red-team PASS are the main TeX diagram,
    dependency table, TeX--Lean index, web theorem companion, implementation
    log, and node color updated together.
12. **Red-team:** `$red-team-structural-exhaustion-manuscript-repair` returns
    PASS on this sketch after all producer, consumer, persistence, and transfer
    obligations are implemented.

Until these tests pass, the correct status is: **contract sketched, node
`[160]` white, nodes `[22]`--`[24]` unavailable**.

## Implemented family-runner follow-up

The red-team's pointwise-to-family runner blocker is now isolated and
implemented in `Core.FinitePrefixExtensionFamily`, with an independent
non-Erdős execution. `P13SelectedWindowPrefixFamily` lifts it to the exact
CT12-selected window subtype and order, retains the unchanged node-`[21]`
prefix in the family type, runs the fixed 91-coordinate schedule on every
window, and returns either the first obstructed window with complete earlier
ledgers or complete ledgers for the entire selected family. Its visible-work
envelope is exactly `91 * p13 ctx`.

This resolves only the family traversal part of red-team blocker 4. The
pointwise machine is still an explicit producer interface awaiting a
graph-owned constructor. In particular, complete symbolic ledgers still do
not imply all-assignment realization, an obstruction does not yet imply a
globally omitted vector, and no commuting gluing or terminal consumer has been
proved. Node `[160]` therefore remains white.
