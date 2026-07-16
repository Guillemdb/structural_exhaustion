# Red-team audit: node [160] hot/cold first-failure contract

## Baseline and verdict

- Audited repair sketch: `node160_hot_cold_first_failure_contract.md`.
- Exact manuscript obligation: `[21] -> [160] -> [22]`, the white
  91-coordinate completion-state and commuting-realization edge in
  `rem:p13-91-realization-obligation`.
- Exact implemented generic units:
  `Core.FinitePrefixExtension` and its non-Erdős transfer example.
- Relevant exact predecessor: `VerifiedP13MultiScaleCurvaturePrefix ctx`.
- Verdict: **FAIL**. The sketch correctly leaves node [160] white, but its
  proposed contract still has blocking quantifier, reflection, provenance,
  gluing, and leaf-totality gaps.

The sketch makes the essential first correction: the 91 separate audited
counts do not imply

```text
forall assignment : I -> Bool, exists state, response state = assignment.
```

Its `{00,11}` countermodel is valid. It also correctly refuses to substitute
the unrelated 13-bit actual-attachment classifier for this obligation.

## Provenance and node-[1] ancestry

| Required datum | Exact available producer | Audit |
|---|---|---|
| minimal-counterexample graph | `ctx : MinimalCounterexampleContext ...` | exact node-[1] graph identity is retained |
| node-[21] result | `VerifiedP13MultiScaleCurvaturePrefix ctx` | exact predecessor is retained through `previous` |
| 91 barrier relations and audits | fields of `VerifiedP13MultiScaleCurvaturePrefix` | available, but only as counts/rows/rates |
| selected packing | `p13Windows ctx` from the earlier CT12 packing on the same `ctx` | available independently of node [21] |
| one selected window | subtype `{w // w in p13Windows ctx}` | exact if this subtype is used; not a raw caller window |
| completion states and response | no producer | blocking |
| cross-window completion gluing | no producer | blocking |

The predecessor chain itself does not store a selected window. This is not a
license to accept one with no provenance: the application signature must use
the exact membership subtype derived from `p13Windows ctx`, as the current
`P13HotColdInterface.SelectedP13Window` does. The sketch names that subtype,
but it has not yet defined a node-[160] producer whose input equality and
membership are visible in Lean.

The nearby `P13HotColdInterface` is not a repair of node [160]. It explicitly
leaves `P13LocalBooleanData.system` application-owned, works with a generic
Boolean realization table, and disclaims the 91-coordinate graph-owned state
system and cross-window product. It must not be imported as ancestry for a
node-[160] proof.

## Quantifier attacks

### Coordinatewise versus simultaneous

The sketch passes this attack: it rejects the invalid promotion from 91
coordinatewise facts to simultaneous surjectivity and demands a uniform
extension theorem instead.

### One symbolic run versus all assignments

The implemented `Core.FinitePrefixExtension.Machine` has

```text
extend : State k -> Coord -> Step State Failure k
```

and follows exactly one successor at each visited coordinate. `Complete`
therefore proves only that this one symbolic state traversed the coordinate
list. It does not prove that both Boolean successors exist at every prefix,
and it has no theorem extracting a concrete completion for an externally
supplied assignment.

The prose-level `P13ExtensionDecision`, by contrast, is indexed by a partial
completion and a requested bit. These are not yet the same contract. To make
the symbolic interpretation sound, the Erdős layer needs at least:

1. a predicate saying that `State k` represents every admitted length-`k`
   Boolean prefix;
2. an empty-prefix proof for `root`;
3. a step theorem preserving both bit fibres without enumerating them; and
4. a terminal extraction theorem producing a concrete admissible completion
   for a supplied assignment and proving response equality.

Without this refinement, a machine that always returns `.extended` is a
countermodel to the claimed hot conclusion: it completes the scan even when
its application state represents only one response vector.

### Local first failure versus a globally omitted vector

The proposed cold theorem is not justified by the stated `noExtension` field.
Failure to extend one particular partial completion by `failedBit` does not
imply that no complete state realizes the prefix-plus-bit-plus-false-suffix
vector. Another partial completion with the same response prefix could extend
that bit and realize the alleged omitted vector.

A two-partial-state countermodel suffices: `p` and `p'` have the same visible
prefix; `p` has no `1` extension, while `p'` has one. The recorded failure of
`p` is genuine, yet the total state through `p'` realizes the proposed
omitted vector. The application must prove canonical-prefix uniqueness or a
factorization theorem saying that every total state with the prior response
prefix extends the exact failed partial. Until then the cold residual is a
local obstruction, not a missing 91-bit assignment.

### One window versus the packed-window family

The manuscript first asks for the local theorem for one selected window and
then separately requires a product over several packed windows. The sketch's
Layer 1 is pointwise in one `window`, while its hot consumer expects local
systems and hot certificates for every selected window. A node-level runner
must therefore expose an exhaustive family result:

```text
first graph-owned cold obstruction in the finite selected-window order
or
a hot realization certificate for every selected window.
```

No such finite family scan, first-cold selector, exact check ledger, or theorem
linking its all-hot result to the dependent family consumed by gluing is
defined. Merely proving a dichotomy for an arbitrary single window does not
construct the all-window hot branch.

## Hot/cold separation and forbidden shortcuts

- No leakage from nodes [158]--[159] into the proposed 91-bit proof was found.
- The sketch explicitly rejects `LocalBooleanRealization.classify`, Boolean
  prefix-tree traversal, and a `2^91` work term for node [160].
- The implemented Core machine and transfer example scan only the supplied
  coordinate list. They do not enumerate `I -> Bool`, graphs, subgraphs,
  contexts, states, or ambient universes.
- No caller-provided `hot`, `cold`, `realizes`, or Boolean cube is present in
  the Core contract.
- The application-owned `extend` function can still manufacture arbitrary
  success or failure. Graph ownership therefore remains entirely in the
  missing Erdős producer and semantic reflection theorem.

The transfer example checks four literal coordinates, an exact obstruction at
coordinate two, an always-extending run, and a four-check budget. This is a
valid transfer for ordered first failure only. It is not transfer evidence for
two-bit extension, graph admissibility, omitted-vector reflection, or
commuting gluing.

## Graph ownership and semantic reflection

`P13CompletionDatum`, `P13CompletionAdmissible`, the flat-response evaluator,
prefix restriction, and `P13LocalCompletionObstruction` are only proposed
names. The sketch has not supplied Lean definitions that make the following
facts graph-owned:

- every state is built from the fixed `ctx.G` and exact selected window;
- restriction and extension preserve the same boundary and selected-window
  embedding;
- the 91 responses are the manuscript's actual barrier relations;
- a failed extension produces one of the six advertised graph clauses;
- `semanticFailure` rules out the requested extension rather than merely
  recording a tag;
- a completed symbolic state yields a concrete admissible graph completion.

This is an S-Def/S-Trig blocker. CT10 cannot supply any of these semantics and
must not be used to classify invented completion data.

## Cross-window gluing attack

`P13CommutingWindowGluing` is presently a desired theorem, not a producer. In
particular, vertex-disjoint selected `P13` supports do not show that their
completion supports are disjoint or that independent local choices preserve
all responses. The proposed `glue : (forall w, State w) -> GlobalState` also
requires proofs of:

- finite, graph-owned support and boundary ownership for each local state;
- a deterministic order of gluing the selected windows;
- preservation of admissibility at every intermediate step;
- pairwise commutation or an equivalent sequential noninterference theorem;
- response preservation for every local coordinate;
- injectivity/recovery needed by the entropy count; and
- a local first-interference witness when a step fails.

None of these follows from path vertex-disjointness. The gluing-failure branch
is especially incomplete: it has no Lean residual type with a proved exact
first witness and no admitted C1--C5 or typed downstream consumer.

## Both-sides and leaf-totality audit

| Leaf | Positive account | Negative witness | Consumer | Verdict |
|---|---|---|---|---|
| all 91 symbolic steps extend | one completed symbolic ledger | none | terminal extraction plus local hot entropy | **fail**: extraction/reflection absent |
| first local extension fails | least index and proposed semantic payload | local no-extension | graph obstruction consumer | **fail**: omitted-vector factorization and consumers absent |
| every selected window is hot and gluing succeeds | response-preserving global state | none | node [22] product entropy | **fail**: family runner and gluing absent |
| cross-window gluing first fails | proposed interference clause | exact local interference | named typed route | **fail**: no residual producer or terminal consumer |

The six advertised cold constructors are only a classification target. No
total theorem shows that every failed extension yields exactly one of them,
and their C1--C5 consumers are not implemented. Consequently the repair is not
leaf-total even before the cross-window branch is considered.

## Practicality, termination, and trust

- Focused build passed:
  `lake build StructuralExhaustion.Core.FinitePrefixExtension
  StructuralExhaustion.Examples.FinitePrefixExtension`.
- Focused searches found no `sorry`, `admit`, new `axiom`, or `unsafe` in the
  two implemented files.
- `visibleChecks = coordinates.length`; the transfer example verifies four
  checks. Thus the generic runner terminates by finite list recursion and has
  no hidden exponential term.
- The proposed application work bounds are not yet executable. There is no
  exact 91-coordinate list theorem, completion-construction check ledger,
  selected-window family ledger, or gluing check ledger.
- Sole-HSS trust is preserved by the implemented generic unit, but no
  `#print axioms` result can validate the unimplemented graph theorems.

## TeX--Lean--web synchronization

The manuscript correctly keeps [160] white and says that node [21] supplies
only relations/counts, not completion states, response realization, or
commuting gluing. The repair sketch also says it is not merge-ready. That is
the honest synchronized status. Promoting [160], [22], [23], or [24] to green
from `FinitePrefixExtension` alone would contradict the manuscript's exact
scope.

## Findings

### Blocking

1. `FinitePrefixExtension.Complete` has no sound bridge from one symbolic run
   to realization of every externally supplied Boolean assignment.
2. The cold omitted-vector theorem lacks canonical-prefix uniqueness or a
   factorization theorem for all total states with the failed prefix.
3. No graph-owned completion datum, admissibility/reflection layer, or total
   six-clause obstruction classifier exists in Lean.
4. No exact finite family runner turns the pointwise window dichotomy into
   either the first cold selected window or hot certificates for all selected
   windows.
5. The cross-window commuting gluing theorem, first-interference residual, and
   recovery/injectivity proof are absent.
6. Cold obstruction and gluing-interference leaves have no total typed C1--C5
   consumers. The leaf table is therefore open.

### Required cleanup

- Make selected-window provenance an exact subtype from `p13Windows ctx` in
  every node-[160] input and retain the node-[21] predecessor unchanged.
- Add representation, two-fibre preservation, terminal extraction, and
  response-reflection interfaces around the generic prefix runner.
- State and prove the prefix factorization theorem before naming any global
  omitted assignment.
- Add non-Erdős transfer examples for the representation/extraction theorem,
  a true semantic obstruction, family first-cold selection, successful
  commuting gluing, and first gluing interference.
- Record exact local check budgets for completion construction, the 91-step
  pass, the selected-window pass, and sequential gluing.

### Advisory

- Keep the current refusal to use the 13-bit classifier or enumerate the
  91-bit cube.
- Keep node [160] white until both the local and cross-window producers have
  passed independent review.

## FAIL disposition

Return the obligation to S-Def/S-Dich/S-Trig at the local layer: first define
the graph-owned partial/completion semantics and prove the symbolic-family
representation, terminal extraction, and cold factorization theorems. Then
construct the selected-window family runner and re-enter S-Comp/S-Rout for
commuting gluing and every interference consumer. A full red-team rerun is
required before node [160] or its node-[22] consumer can be green.
