# Mandatory Erdős Node Authoring Contract

Use this contract before editing, reviewing, or marking green any node in the
Chapter 1 diagrams. It is deliberately low-freedom. A node that does not fit
this contract remains yellow even if isolated declarations compile.

## 1. Freeze the paper identity

`original_erdos_64_proof.tex` is the sole mathematical specification for this
card.  The live manuscript is a derived synchronization artifact and cannot
change a responsibility, supply an excuse for an omitted proof, or override
the original proof strategy.  Never edit the original.

Fill this card from `original_erdos_64_proof.tex` and the corresponding prose
in `proofs/erdos_64_eg/erdos_64_proof.tex` before reading application code:

| Field | Required value |
|---|---|
| Node ID | One existing diagram node |
| Incoming edges | Every exact source node and branch label |
| Outgoing edges | Every exact target node/terminal and branch label |
| Local responsibility | Only the mathematical move stated at this node |
| Retained branch facts | Facts already carried by each incoming branch |
| New output | The single new fact, datum, decision, or terminal proved here |
| CT chain | One existing CT, or the smallest existing CT chain implementing the move |
| Immediate consumers | Only consumers already present in the diagram |

Reject the edit if this card adds, removes, renames, splits, or merges a node,
edge, branch, case, join, or exit. Never edit `original_erdos_64_proof.tex`.

## 2. Enumerate the exact local obligations

Create one row for every assertion made by the paper *at this node*:

| Task ID | Paper assertion | Incoming ledger producer | Local Lean declaration/CT run | Outgoing edge | Status |
|---|---|---|---|---|---|

Include locally defined objects, branch predicates, semantic bridges, exact
equalities and inequalities, CT execution/trace/totality facts, terminal
implications, and work bounds. Do not assign a successor's closure theorem or
a sibling branch's fact to this node. Do not omit a local obligation because a
later node will consume it.

## 3. Enforce the only permitted state flow

Every non-root node has exactly this shape:

```text
exact incoming branch stage
  + its one full accumulated framework ledger
  -> retrieve all inherited inputs from that ledger
  -> execute the node's existing framework CT/combinator
  -> prove only the node's new paper-local mathematics
  -> framework automatically extends that same ledger
  -> exact outgoing branch stage(s)
```

Only the genuine theorem root may use `ResidualStage.exact`. Every later node
must consume the literal stage returned by its predecessor's framework
executor. Never seed, checkpoint, clone, restage, replace, or manually rebuild
the ledger. There is one accumulated ledger, not event-specific, branch-local,
or application-owned parallel ledgers. A decision may return several typed
branch stages, but each contains the same incoming accumulated ledger extended
with its own exact branch certificate.

Dashboard completion metadata is never part of this state flow. It may not
occur in a Lean declaration name, input type, proposition, branch carrier, or
certificate. A partially implemented obligation has no callable proof API;
the legal node input is still only the literal predecessor stage and its one
accumulated ledger.

## 4. Retrieve; never rederive or copy

### Incoming residual only; never create a family

A node may quantify only over carriers, collections, schedules, fibres, and
families already contained in its literal incoming residual and exposed by
the single accumulated ledger. It must never define a new application-owned
family of graphs, states, completions, contexts, supports, witnesses, or
realizations, even as an image, subtype, sigma type, chosen representative,
or extensionally equal replacement. If the needed view is not exposed, add a
generic Core projection/query for the existing residual; do not manufacture a
new carrier in the node. Every output fact must refine the same incoming
residual, and Core alone appends it to the common ledger.

For every required inherited value, record its original producer. Retrieve all
inputs from the current ledger with one compositional
`Core.ResidualRefinement.State.LedgerQuery`, using `fact`, `stage`,
`andFact`, `andStage`, `entailedStage`, `andEntailedStage`, and `map` as
needed. Resolve the query with `State.StageNode.derive` or the matching
dependent-decision continuation.

Register each reusable proposition once, beside its producer, with
`State.StageEntails`. Later nodes query the proposition; they do not reopen a
certificate structure, copy the theorem into intermediate outputs, or prove
it again. A temporary named query view is allowed only as an input view and
must not become a field of the node output.

If retrieval fails, repair the earliest producer's ledger attachment. Never
add the missing fact as a new consumer assumption, recompute it from the graph,
or reach around the ledger through a stable residual.

## 5. Keep the application output thin

An Erdős node output contains only mathematics first established by that node.
It must not contain:

- the predecessor, ledger, context, or execution again;
- `previous`, `previousExact`, `exactPrevious`, or an equivalent equality;
- inherited facts or certificates;
- a caller-supplied conclusion, branch outcome, accounting callback, or
  feasibility contract;
- a custom handoff, route, checkpoint, event ledger, or compatibility wrapper;
- a copied nested predecessor inside a decision result.

Do not define an application-owned structure merely to express transport. Use
the existing framework CT output, `StageNode`, decision, query, and accumulated
transition carriers. A manuscript-facing name may be a thin alias or wrapper
around genuinely new local mathematical payload only.

## 6. Use the mandatory successor patterns

For an ordinary data-bearing successor, use the framework's stage mapping
over the literal predecessor and construct the new payload from that retrieved
value:

```lean
def nodeN : State.StageNode … NewPayload :=
  State.StageNode.mapStage predecessorStage fun previous =>
    -- prove only node N's local assertion from `previous` and ledger queries
```

When several inherited values are needed, use one query and `derive`; never
add arity-specific helpers such as `usingThreeStages`:

```lean
def nodeN : State.StageNode … NewPayload :=
  State.StageNode.derive currentStage nodeNInputs fun inputs =>
    -- one local proof
```

For a reusable proposition produced here, add its `StageEntails` instance at
this producer. Do not change all later output types to carry the proposition.

For a CT transition, Erdős code declares only the existing source CT, target
CT/profile, exact incoming stage, and node-local mathematical instantiation.
The framework-owned node executor resolves the route, retrieves any current
residual projection, executes the target CT, appends its facts, preserves the
complete ledger, and returns the exact successor stage.

Erdős application code must not invoke or mention routing internals such as
`advance`, `advanceCurrent`, `onLedger`, `OutputLedger`,
`ProjectedOutputLedger`, `EnabledStage`, `.ledgerStage`, source projections,
or `ResidualStage.exact` after the root. If the framework cannot perform a
required paper edge through one public node/CT execution, repair the generic
framework API first; never implement the missing route in the example.

## 7. Use only existing diagram decisions

A paper yes/no question is implemented by a framework decision over the exact
incoming stage. Both outcomes exist by the decision; neither branch must prove
the other. Continue them with the existing `StageNode` dependent-decision
combinators, including `DependentDecisionAt`,
`continueDependentDecisionYesAgain`,
`continueDependentDecisionYesAgainDerived`,
`continueDependentDecisionNoAfterYes`, and nested-leaf combinators where their
types apply.

Never introduce an Erdős-specific sum, route, exceptional case, or residual
subtype to represent a branch. Never demand a global contradiction at a node
whose paper responsibility is only to refine and route a residual. A terminal
node proves only its own branch-local closing implication.

## 8. Keep CT and graph ownership strict

Use only framework CTs for node execution. If a repeated mechanism is absent,
implement it once at its general owner and add a non-Erdős fixture before the
thin Erdős instantiation:

| Content | Owner |
|---|---|
| Ledger, query, stage, decision, generic finite/accounting plumbing | `Core` |
| One CT's runner, result, trace, semantics, totality | That CT |
| CT-to-CT accumulated transition and provenance | `Routes` |
| Parameterized graph mathematics | `Graph` |
| Fixed Problem 64 data and paper-specific arithmetic | Erdős example |

Do not generalize a paper-local theorem into a claim about all graphs. Do not
put Erdős constants or names in the framework. The parameterization test
decides ownership; difficulty proving one application lemma does not.

## 9. Keep computation local

Inspect only the finite local carrier specified by the paper. Use supplied
proof-carrying witnesses, symbolic encodings, and framework cardinality/work
lemmas. Never enumerate all graphs, subgraphs, universes, colorings, contexts,
or powersets; never perform monolithic Boolean-table expansion; never raise
heartbeats, recursion depth, timeout, or memory limits. Run one focused,
single-process build for the touched module before wider validation.

## 10. Hard-reject these patterns before compilation

Search the touched Erdős dependency cone and reject any newly introduced use
of:

```text
extends Core.ExactHandoff
previousExact
exactPrevious
TacticInterface
RouteRule
GeneratedRoute
onLedger
advance / advanceCurrent
OutputLedger / ProjectedOutputLedger
usingTwoStages / usingThreeStages / usingNStages
caller-supplied account, outcome, terminal, closure, or survival hypotheses
ResidualStage.exact after the root
manual checkpoint or replacement ledger
node-local graph/state/completion/context/support/witness/realization family
```

Also reject a `usingStage` body that ignores the retrieved stage, a consumer
that reaches directly into an old residual for an accumulated fact, and an
output that nests earlier node payloads solely for transport.

## 11. Green-node certificate

Mark the node green only when all answers are yes:

1. Does its identity and every edge exactly match the immutable diagram?
2. Are all immediate predecessors green on this exact incoming path?
3. Does it consume the literal predecessor stage and one full ledger?
4. Are all inherited inputs retrieved from that same ledger?
5. Does it execute an existing framework CT/combinator?
6. Does Erdős code prove only the new local paper responsibility?
7. Does the framework append every new fact and preserve all old facts?
8. Are all original-paper obligations for this node kernel-checked?
9. Are every outgoing branch and terminal represented without extra cases?
10. Is the computation local, symbolic where large, and practically bounded?
11. Do focused builds and trust checks pass without resource-limit changes?
12. Do Lean, live TeX, the Lean-owned web obligations, and generated status
    report the same local result?

Any `no` keeps the node yellow. Record each unmet item as a specific obligation
with its intended producer; do not advance the frontier.
