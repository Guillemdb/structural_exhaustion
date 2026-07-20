---
name: implement-next-erdos-64-eg-ct
description: "Advance the repository's Erdős--Gyárfás Problem 64 Lean formalization by exactly one structural-exhaustion CT selected from the manuscript's directed residual flow. Use when continuing proofs/erdos_64_eg/erdos_64_proof.tex: reconstruct every branch, consume the single full accumulated residual ledger, require framework-owned CT routing, implement only the first dependency-ready paper-local responsibility, synchronize TeX--Lean--web evidence, validate locally, and update the implementation log."
---

# Implement the Next Erdős 64 CT

Advance exactly one CT per invocation. Select the first dependency-ready manuscript stage that fails the audit, complete it, then stop. Do not start a second CT.

## Read the mandatory contract

Before inspecting or editing an Erdős node, read
[`references/mandatory-node-template.md`](references/mandatory-node-template.md)
completely. Fill its paper-identity card and complete obligation ledger. Its
single-ledger, framework-routing, thin-output, immutable-topology, locality,
and green-node rules are binding implementation specification.

Do not edit Lean until the card identifies the exact incoming stage, every
ledger query, the CT/profile, the one new local mathematical payload, and every
existing outgoing edge.

Give every obligation a stable task ID. The complete obligation ledger must
contain every asserted object and every unfinished task, not only the node's
headline theorem.

## Establish authority

Work from the repository root, inspect `git status --short`, and preserve
unrelated changes. Read completely:

- the architecture and every Chapter 1 `Proof-dependency diagram` panel in
  `proofs/erdos_64_eg/erdos_64_proof.tex`;
- the selected row of the `Detailed dependency table` and every definition or
  proof it cites;
- `original_erdos_64_proof.tex` for immutable diagram topology only;
- `Erdos64EG/OfficialStatement.lean`, `Erdos64EG/InternalProblem.lean`, the
  exact predecessor modules, `Erdos64EG/WebExport.lean`, `Erdos64EG.lean`,
  `Tests.lean`, `README.md`, and
  `examples/erdos_64_eg/IMPLEMENTATION_LOG.md`;
- `generated/lean-machines.json` and `generated/examples/erdos-64.json`;
- `.agents/skills/design-structural-exhaustion-proof/SKILL.md`; and
- the selected `implement-structural-exhaustion-ctN/SKILL.md`.

Inspect the compiled CT and transition catalogs only to verify that the
framework owns the selected CT and every edge. Erdős code never implements or
consumes routing.

## Preserve the original directed proof

Treat `original_erdos_64_proof.tex` as closed; never edit that file. Never add,
rename, split, merge, or remove a node, edge, case, join, branch label, or exit.
Every public outcome must correspond to an existing directed edge and record
its source node, target node, branch label, producer, and consumer.

An internal helper may prove mathematics on an existing edge, but it cannot
create a new consumer or outcome. Keep working and partial Lean code when a
node is demoted; correct its provenance and status instead of deleting it.

Read the proof as a directed graph, not a linear node-number sequence. Trace
every incoming path and branch condition. Use a fact only when it is present
in the exact incoming ledger on that path. Never borrow from a sibling branch,
later node, or similarly named object in another residual.

Terminal nodes close only their own branch. A handoff node produces its named
residual; it need not close the whole proof. Never demand a successor's closure
theorem from a local classification node.

## Select the verified frontier

Use the compiled node-status map and actual diagram arrows. Every immediate
predecessor on the selected path must be green. Yellow, white, and
declared-frontier predecessors block the node.

Count a stage as unconditional only when:

1. it consumes the exact preceding execution result and full accumulated
   ledger from the same graph and branch;
2. it defines every paper-local object and semantic bridge;
3. the public framework runner executes the selected CT;
4. Lean retains the terminal-indexed outcome, typed trace, semantic soundness,
   totality, exact local result, and `Core.PolynomialCheckBudget`; and
5. its endpoint accepts no caller-supplied contract, outcome, terminal,
   closure, feasibility, or conclusion that it is meant to prove.

A wrapper, structure, capability, fixture, or conditional theorem is not an
implemented stage.

## Enforce the single-ledger framework API

Every non-root node consumes the literal incoming framework stage. There is
one full accumulated ledger. The framework automatically retrieves the
current residual, executes the CT, preserves all previous facts, appends every
new fact, handles every branch, and returns the successor stage.

Erdős code supplies only concrete manuscript mathematics and a thin CT
instantiation. It must not contain routing, route executors, source
projections, output-ledger aliases, manual extension, restaging, checkpoints,
custom handoffs, predecessor/equality fields, or application-owned result
types.

Retrieve any number of inherited facts with one compositional
`State.LedgerQuery` and `State.StageNode.derive`. Declare each reusable
proposition once with `State.StageEntails` beside its producer. Never rederive,
copy, reopen, or recompute an accumulated fact. If retrieval fails, repair the
earliest producer's ledger attachment.

Use framework residual refinement, provenance, support recognition, decision,
pointwise execution, enumeration, symbolic encoding, and work accounting.
If reusable plumbing is missing, that is an API design error: implement it once
in `lean/StructuralExhaustion/Core`, the CT, Routes, or
`lean/StructuralExhaustion/Graph` with a non-Erdős fixture, then keep the
`examples/erdos_64_eg` application thin. Never put Erdős names or constants in
`Core`.

## Implement the paper-local CT

Use `design-structural-exhaustion-proof` to select the CT by mathematical role.
Then:

1. Define only the concrete types, predicates, deciders, graph objects, fixed
   constants, and reflection facts first introduced at this node.
2. Prove executable predicates equivalent to the paper predicates.
3. Instantiate the existing CT with those values; do not accept the
   instantiation, result, or conclusion from the caller.
4. Execute the public framework runner from the incoming stage.
5. Prove every local obligation, all existing outgoing branches, trace,
   semantics, totality, and practical work bound.
6. Register every new reusable fact in the same accumulated ledger.
7. Add small fixtures only to exercise branches, never as a substitute for the
   theorem.

Do not add `sorry`, `admit`, unsafe declarations, new axioms, opaque Boolean
surrogates, empty universes, or placeholder `True`/`False` semantics.

## Keep computation local

Use only the finite local data and proof-carrying witnesses specified by the
paper. Never enumerate all `SimpleGraph V`, all subgraphs, all colorings, all
ambient contexts, powersets, or a recursively expanding universe. Never raise
heartbeats, recursion depth, timeout, or memory limits.

Use framework symbolic finite encodings, q-column bundles, cardinality lemmas,
local support schedules, CT-native scans, and work combinators. Run a focused,
single-process build first. A timeout or material RSS increase keeps the node
yellow and requires a framework-level efficiency repair.

## Maintain the bidirectional TeX--Lean--web index

Update only `proofs/erdos_64_eg/erdos_64_proof.tex`; never modify the original.
Preserve all diagram nodes, endpoints, directions, and labels exactly. Use
stable mathematical `\label`s and never put Lean declaration names or
implementation status in a LaTeX label.

Update `Erdos64EG/WebExport.lean` from kernel-checked evidence. For every
implemented proof step `p` and workflow stage `s`: The union of `p`'s
declaration groups must equal `D(s)`. Use `ExampleProofStepDescriptor`,
`ExampleDeclarationGroup`, and `erdosManuscript.nodeObligations`. Every task
has a stable ID, paper property, exact evidence, and proved/partial/missing
status. Removing a node from `formalizedNodeIds` alone is invalid.

Require both navigation directions:

- TeX label or diagram node -> proof step -> workflow stage -> declarations;
- selected Lean declaration -> declaration group and role -> exact paper node.

Every displayed stage must map to exactly one proof step. Require
`explainedDeclarations == displayedDeclarations`. Regenerate with `make
export` instead of hand-editing generated JSON. The stage is complete only
when it is recorded in TeX, Lean, and the generated web projection.

## Require transfer and validate

Any new reusable profile needs a non-Erdős problem instantiation of the same
API: a named standard textbook graph theorem that executes the same runner,
proves trace/semantics/totality/work, and builds as an external example
package. `CTNAutomationFirst.lean` does not alone satisfy this
problem-transfer requirement. Reuse the generalized graph/core material.

Run focused checks, then the affected subset of:

```bash
make lint
make framework-build
make erdos-example-build
make export
python3 tools/validate_repository.py --root .
python3 -m pytest -q tests/test_repository.py tests/test_example_catalog.py tests/test_web_api.py tests/test_skills.py
make web-frontend-test
git diff --check
```

Compile the live paper when it changes. Inspect generated artifacts rather
than hand-editing them. Use `#print axioms` on new endpoints; only the declared
Hegde--Sandeep--Shashank theorem may introduce external trust, and only along
its actual dependency cone.

Finally: Reconcile the whole ledger against the compiled Lean declarations in
`examples/erdos_64_eg/IMPLEMENTATION_LOG.md`. Record the manuscript section,
theorem labels, and diagram nodes; the provenance chain from the official
problem through prior CT outputs; the runner, terminal or residual, typed
trace, semantic theorem, totality, and work bound; transfer evidence; passed
commands; and the next dependency-ready manuscript section.

If validation fails, leave the verified frontier unchanged. Report the exact
last unconditional node and blocker. Stop after the one selected CT is proved,
tested, synchronized, and recorded.

## Absolute residual-carrier rule

Never define a node-local family or replacement carrier. Work only on the
literal incoming residual and retrieve every collection through the single
Core-owned accumulated ledger. If a view is missing, extend Core with a
projection/query of that same residual; do not create an application family.
