---
name: review-erdos-64-eg-expansion
description: "Audit and repair an Erdős--Gyárfás Problem 64 expansion and discharge every partially formalized diagram node before further expansion. Use after implement-next-erdos-64-eg-ct, when any web node is yellow, or when a claimed frontier must be checked for local unconditional Lean provenance, one full accumulated residual ledger, framework-owned routing, agreement with proofs/erdos_64_eg/erdos_64_proof.tex, TeX--Lean--web synchronization, practical local computation, sole-HSS trust, and maximal framework reuse."
---

# Review Erdős 64 Expansion and Clear Partial Nodes

Review and repair the current verified frontier. Do not implement the next CT.
Stop before the next white node. A clean review has no yellow node in the
already-touched dependency cone.

## Read the mandatory contract

Read completely:

- [`../implement-next-erdos-64-eg-ct/references/mandatory-node-template.md`](../implement-next-erdos-64-eg-ct/references/mandatory-node-template.md);
- `.agents/skills/implement-next-erdos-64-eg-ct/SKILL.md`;
- `.agents/skills/design-structural-exhaustion-proof/SKILL.md`; and
- the selected `implement-structural-exhaustion-ctN/SKILL.md`.

Treat the template as the review gate. No legacy paragraph may authorize
application-owned routing, handoffs, checkpoints, predecessor copies, manual
ledgers, caller-supplied results, or obligations outside the paper node.

## Freeze topology and scope

Treat `original_erdos_64_proof.tex` as the immutable mathematical and topology
authority and never edit that file.  The live manuscript is only a derived
synchronization view; its status prose or missing implementation notes are
never evidence that an original-paper obligation may be skipped, weakened, or
declared unavailable. Compare the complete live Chapter 1 diagram against it. Never add,
rename, split, merge, or remove a node, edge, branch label, join, or exit. Any
difference fails the review.

Every public outcome corresponds to one existing directed edge with its source
node, target node, branch label, producer, and consumer. An internal helper may
prove mathematics on that edge but cannot create a new consumer or case.

Preserve useful Lean code when demoting a node. Track it as conditional support
and correct its provenance/status. Never delete proof code merely to make the
dashboard match.

## Establish authority

Work from the repository root, inspect the dirty worktree, and preserve
unrelated edits. Read:

- all Chapter 1 proof-flow diagrams, the detailed dependency row, and every
  cited definition/proof in `original_erdos_64_proof.tex`, followed by the
  corresponding live material solely for synchronization;
- `OfficialStatement.lean`, `InternalProblem.lean`, the exact predecessor and
  reviewed Erdős modules, `Erdos64EG.lean`, `Tests.lean`, `WebExport.lean`,
  `README.md`, and `IMPLEMENTATION_LOG.md`;
- every changed or consumed declaration in `Core`, the selected CT, `Routes`,
  and `Graph`, plus its non-Erdős transfer example;
- `generated/lean-machines.json`; and
- `generated/examples/erdos-64.json`.

The paper specifies the mathematics, Lean determines what is proved, and
generated files are checked projections only.

## Enforce the no-yellow gate

Compute yellow nodes from the compiled manuscript descriptor. A node is yellow
when an implemented proof step cites it but it is absent from
`formalizedNodeIds`. Iterate over touched nodes in dependency order until the
set is empty; do not advance the frontier.

Judge completeness locally. A node is green exactly when it:

1. consumes the exact preceding execution output, branch condition, and full
   accumulated ledger from green predecessors;
2. defines every object and finite datum asserted at that node;
3. executes the public framework runner and retains the terminal-indexed
   outcome, typed path and trace, semantic soundness, totality, and work bound;
4. proves every local conclusion and outgoing payload; and
5. accepts no caller assumption restating its responsibility.

A terminal node proves only its branch-local closing implication. A handoff
node only refines and routes its residual. Neither needs the global theorem or
the opposite branch.

## Audit the obligation ledger

For every touched node, reconstruct the complete obligation ledger with a
stable task ID for every asserted object and every unfinished task:

| Task ID | Original-paper property | Exact predecessor | Lean evidence/run | Outgoing edge | Status | Missing producer |
|---|---|---|---|---|---|---|

Statuses are `proved`, `partial`, or `missing`. Green requires every row proved
from green exact predecessors. Removing a node from `formalizedNodeIds` alone
is never a valid demotion. Publish preserved and missing tasks to the Lean-owned
web obligation ledger immediately.

Reject obligations assigned outside the node's paper scope. Never require a
successor closure at a classification node or import a sibling branch fact.
Before reporting a missing theorem, reconstruct every incoming diagram path
and query the actual accumulated ledger.

## Audit the one-ledger API

Every non-root node consumes the literal predecessor stage and one full
accumulated ledger. All inherited facts are retrieved through one
`State.LedgerQuery`; reusable propositions are declared once with
`State.StageEntails`. Reject copied fields, repeated derivations, old-residual
reach-through, nested transport payloads, and arity-specific retrieval helpers.

Routing is entirely framework-owned. Reject every routing primitive in Erdős
code: route executors, `advance`, `advanceCurrent`, `onLedger`, output-ledger
aliases, enabled-stage types, `.ledgerStage`, source projections, manual
extension, restaging, custom handoffs, and predecessor/equality bundles.
Require one framework-owned node executor that resolves the edge, preserves
and extends the ledger, executes the CT, and returns the successor stage.

Existing decisions must use framework dependent-stage combinators so each
branch retains the literal predecessor and ledger. Reject application-owned
sum types, repeated decisions, invented residual cases, or a branch that must
prove its complement before proceeding.

Reject any Lean declaration whose name, input, proposition, or carrier
encodes dashboard completion or migration status. Missing proof evidence has
no callable interface and cannot be supplied by a consumer; it must be proved
at its paper producer or omitted from the accepted proof path.

Treat framework automation and residual refinement, routing, provenance,
support recognition, execution, traces, and work accounting as binding
implementation specification. If automation is missing, implement it once in
Core, the CT, Routes, or Graph with a transfer fixture. A mathematically correct
Erdős node remains yellow while application plumbing exists.

## Audit unconditional Lean provenance

The public endpoint must begin from the official problem and earlier verified
outputs. It must not accept a capability, result, terminal equality,
survival/closure hypothesis, response theorem, or other author contract that
the stage should derive.

Require the exact problem predicates, deciders, finite local data, semantic
equivalences, CT execution, trace, semantics, totality, and local work bound.
Interfaces, structures, wrappers, and fixtures without execution are not proof.

If the paper states a dichotomy, require the exhaustive framework decision.
Do not assume the premise excluding another terminal. Check every existing
outgoing edge and every node covered by the CT block.

Search the dependency cone for `sorry`, `admit`, unsafe declarations, new
axioms, and proof surrogates. Run `#print axioms` on the public endpoint and new
semantic theorems. The sole permitted external theorem is the declared
Hegde--Sandeep--Shashank theorem, only along its genuine dependency cone.

## Compare paper mathematics with Lean

Compare every cited definition, lemma, identity, constant, range, strictness,
subtraction, semantic predicate, and branch in both directions. Verify that
each dependency comes from an earlier ledger producer and that Lean proves the
same scope as the paper.

When Lean exposes a paper error, repair the paper only with mathematics already
kernel-verified in this round. Never weaken or rewrite the paper merely to
conceal an unproved Lean obligation. Preserve the original topology. If the
paper claim cannot be recovered, keep the previous unconditional frontier and
report the exact missing implication.

## Audit locality and ownership

Require an explicit finite local universe, observable order where relevant,
exact primitive-check accounting, and `Core.PolynomialCheckBudget`. Reject all
`SimpleGraph V`, all subgraphs, all colorings, all ambient contexts, powerset
enumeration, or a recursively expanding frontier. Reject raised resource
limits and elaboration-time global finite-state expansion.

Require framework symbolic encodings, q-column bundles, occurrence-native
support scans, enumeration/cardinality lemmas, and CT work combinators. A
timeout or material RSS increase is a yellow-node defect.

Apply the parameterization test declaration by declaration:

| Dependency | Owner |
|---|---|
| Generic finite, ledger, query, decision, or arithmetic machinery | `Core` |
| One CT's runner/result/trace/semantics | That CT namespace |
| CT transition and accumulated-ledger executor | `Routes` |
| Parameterized graph mathematics | `Graph` |
| Fixed Problem 64 data and arithmetic | Erdős example |

Never put Erdős names in Core. Confirm that a named textbook example consumes
the exact new graph/core/CT/route profile through the same framework node
executor and proves execution, trace, semantics, totality, and work.

## Reconcile TeX, Lean, web, and status

Treat `Erdos64EG/WebExport.lean` and `erdosManuscript` as authoritative. For
each implemented proof step and stage, require the exact
`ExampleDeclarationGroup` coverage, including framework interface evidence.

Keep `ExampleManuscriptDescriptor.nodeObligations` synchronized with the
compiled yellow set. The web may render this ledger but cannot invent tasks or
colors. Require both navigation directions:

- TeX label or diagram node -> proof step -> workflow stage -> declarations;
- Lean declaration -> declaration group and role -> exact TeX label and node.

Require every label/node to exist uniquely, every stage to map to one proof
step, and `explainedDeclarations == displayedDeclarations`. Regenerate with
`make export`; never hand-edit generated JSON. Reconcile the whole
`IMPLEMENTATION_LOG.md`, README, imports, and generated status with the same
kernel-checked frontier.

## Repair and validate

Fix the owning layer first, then the thin Erdős instantiation, live TeX, and
Lean-owned web descriptor. Run focused single-process checks before broader
commands:

```bash
make lint
make framework-build
make erdos-example-build
make example-build
make export
python3 tools/validate_repository.py --root .
python3 -m pytest -q tests/test_repository.py tests/test_example_catalog.py tests/test_web_api.py tests/test_skills.py
make web-frontend-test
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build/erdos proofs/erdos_64_eg/erdos_64_proof.tex
git diff --check
```

Do not report a clean review if a required check fails. Report the reviewed
nodes/CT, exact unconditional endpoint, provenance chain, paper correction,
framework abstractions, transfer, local work bound, TeX--Lean--web coverage,
trust result, and commands. If blocked, identify the previous unconditional
frontier and one precise missing implication; never call the failed node green.

## Reject node-local families

Fail the review whenever an Erdős node defines a new family, carrier,
collection, subtype, image, sigma type, chosen representative set, or
enumeration of graphs, states, completions, contexts, supports, witnesses, or
realizations. Every such object must already be part of the literal incoming
residual and retrieved from the one accumulated ledger through Core. An
extensional equality to an incoming object does not excuse replacement. If a
consumer lacks a view, require a generic Core projection/query of the existing
residual; never permit application-owned reconstruction.
