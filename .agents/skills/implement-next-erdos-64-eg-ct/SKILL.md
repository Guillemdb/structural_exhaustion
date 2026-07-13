---
name: implement-next-erdos-64-eg-ct
description: "Advance the repository's Erdős--Gyárfás Problem 64 Lean formalization by exactly one structural-exhaustion CT selected from the manuscript proof flow. Use when continuing proofs/erdos_64_eg/erdos_64_proof.tex: identify the first dependency-ready stage, perform a mandatory framework-first ownership audit, place all reusable logic in Core, CT, Routes, or Graph, keep Erdős code to concrete problem data and thin instantiations, execute the CT from earlier verified outputs, prove transfer in a non-Erdős example, maintain the bidirectional TeX--Lean index and synchronized web theorem companion, build the affected packages, and update the implementation log."
---

# Implement the Next Erdős 64 CT

Advance exactly one CT per invocation. Complete the earliest unfinished CT at
the verified proof frontier and stop; do not scaffold or partially implement a
later CT.

## Establish the authorities

1. Work from `git rev-parse --show-toplevel` and inspect `git status --short`.
   Preserve unrelated worktree changes.
2. Read completely:

   - the preliminary architecture and Chapter 1 proof-flow material in
     `proofs/erdos_64_eg/erdos_64_proof.tex`, followed by every full
     definition and proof cited by the selected dependency row;
   - `examples/erdos_64_eg/Erdos64EG/OfficialStatement.lean`;
   - `examples/erdos_64_eg/Erdos64EG/InternalProblem.lean`;
   - every existing `examples/erdos_64_eg/Erdos64EG/CT*.lean`;
   - `examples/erdos_64_eg/Erdos64EG.lean`, `Tests.lean`, `README.md`, and
     `IMPLEMENTATION_LOG.md`;
   - `examples/erdos_64_eg/Erdos64EG/WebExport.lean`,
     `generated/examples/erdos-64.json`, and the example catalog schemas;
   - `README.md`, `docs/architecture.md`, and the relevant framework
     specification; and
   - `.agents/skills/design-structural-exhaustion-proof/SKILL.md`.

3. Inspect the compiled CT and route catalogs before selecting an API:

   ```bash
   jq '.tactics[] | {tacticId, capability, capabilityProfiles, terminals, residualKinds}' generated/lean-machines.json
   jq '.routes' generated/lean-machines.json
   ```

Treat the manuscript as the mathematical specification, the official Lean
statement as the problem boundary, and compiled Lean declarations as the
implementation authority. Do not infer completion from documentation alone.

## Find the verified frontier

Use Chapter 1's proof flow, not CT numbering, to choose the next work item.
Read the architecture load path, the eleven parts under
`Proof-dependency diagram`, and the `Detailed dependency table`. Follow diagram
arrows and table prerequisites; node numbers alone are not a topological order
across branch continuations. Then read the full manuscript definitions and
proofs cited by the first candidate row.

Audit each existing Erdős stage against its Lean declarations. Count a stage
as unconditionally verified only when all of the following hold:

- the Erdős-specific input is constructed from `OfficialStatement`,
  `Internal.problem`, and already proved earlier-stage outputs;
- all manuscript data and semantic bridges required by the CT are defined and
  proved in Lean;
- the public framework runner is actually executed;
- its terminal or residual, typed trace, semantic soundness, totality, and
  practical work bound are proved; and
- an exported theorem states the corresponding manuscript claim without
  accepting that claim, a CT outcome, or an uninstantiated author contract as
  a premise.

A file, import, abbreviation, generic wrapper, parameterized capability, or
caller-supplied contract is not by itself a completed Erdős stage. If an
earlier stage fails this audit, that stage remains the frontier even when a
later-numbered CT file exists.

Select the first dependency-ready manuscript stage that fails the audit. Write
an execution-map row before editing:

| Manuscript labels and nodes | Web proof-step/stage IDs | Prior Lean output | CT/profile | Concrete local input | Expected output | Next consumer | Work bound |
|---|---|---|---|---|---|---|---|

Map its mathematical operation to one CT using
`design-structural-exhaustion-proof`. Read the selected
`.agents/skills/implement-structural-exhaustion-ctN/SKILL.md` completely. If
the exact compiled flow is a registered route, also read
`.agents/skills/implement-structural-exhaustion-route/SKILL.md`; otherwise
compose proved outputs directly.

## Pass the framework-ownership gate before editing Erdős code

Classify every planned declaration in the execution-map row before choosing a
file. Use the most general valid owner:

| Declaration depends on | Required owner |
|---|---|
| Only `Core.Problem`, branch/minimal contexts, finite collections, ranks, or generic predicates | `lean/StructuralExhaustion/Core` |
| One CT's specification, capability, runner, result, trace, or semantic theorem | That CT namespace |
| A residual-to-consumer transformation, context transport, trigger construction, or route provenance | `lean/StructuralExhaustion/Routes` |
| Mathlib graph objects and parameters such as a degree threshold, length predicate, boundary type, or graph-local certificate | `lean/StructuralExhaustion/Graph` |
| Power-of-two/Mersenne arithmetic, the pinned official statement, fixed Erdős constants, or concrete manuscript data | `examples/erdos_64_eg` |

Parameterization is the decisive test. If a definition or theorem remains
meaningful after replacing the power-of-two predicate, degree three, or the
Erdős target by parameters, it does not belong in the Erdős package. Move it
to the appropriate framework layer before instantiating it. This includes:

- target encodings and positive/avoiding runner wrappers;
- transport through `TargetBridge` or `MinimalityKernel`;
- CT-to-CT composition, residual extraction, route construction, and
  provenance;
- graph deletion, boundary, response, criticality, independence, and
  rank-minimal-prefix theorems; and
- structures bundling generic CT terminals, traces, route results, and
  structural consequences.

Search `lean/StructuralExhaustion` and every non-Erdős example for an existing
constructor before adding a declaration. If two examples contain the same
proof shape with only predicates or constants changed, stop and extract that
shape into the framework. Do not use an application-local namespace as a
staging area for generic code.

An Erdős CT module may contain concrete manuscript types, finite data,
deciders, arithmetic/reflection proofs, public-statement bridges, and named
thin instantiations of framework APIs. A named wrapper around a generic
method must be an `abbrev`, direct definition, or one-line theorem delegation;
it must not reconstruct the generic proof. Keep concrete smoke fixtures and
export metadata in the example.

Write the reusable API and its framework fixture first. Then make the Erdős
module consume it. Do not count the stage complete while reusable logic
remains in `examples/erdos_64_eg`.

## Preserve provenance through the CT chain

Import the preceding Erdős CT module. Construct the new CT input from the
preceding execution result, terminal-indexed outcome, trace, or theorem. Add a
named provenance theorem when definitional reduction does not make this
connection explicit.

Never replace an earlier output with a fresh assumption that restates it. In
particular, do not make the final slice theorem accept a capability,
`TargetCompressionContract`, response-correctness theorem, terminal, residual,
or manuscript conclusion that the selected stage is supposed to construct.
The theorem may quantify only over the official problem inputs and genuinely
proved outputs of preceding stages.

Use a registered route only when the catalog contains that exact residual
flow. For other CT sequences, use ordinary theorem composition and retain the
framework's output types. Do not erase an outcome into an application-defined
Boolean or rebuild a branch context independently.

## Translate the complete selected stage

Translate every definition, case split, local lemma, finite datum, and
numerical bound used by the selected manuscript stage. Do not invent a
replacement argument or weaken the manuscript statement to fit an API.

1. Define the problem-specific finite types, local graph objects, inspection
   orders, predicates, and deciders.
2. Prove each executable predicate equivalent to its manuscript proposition.
3. Instantiate an existing reusable profile or the CT capability with concrete
   Erdős data. Define this instantiation; do not leave it as a caller argument.
4. Invoke the public CT runner and preserve its execution result, expected
   terminal or residual, terminal-indexed outcome, and typed trace.
5. Prove the runner's semantic theorem, totality, exact trace or terminal when
   required, and native polynomial work certificate.
6. Derive the manuscript theorem for this stage from prior outputs and the CT
   result.
7. Add small executable fixtures that exercise every intended branch without
   substituting for the general theorem.
8. Export the new stage from `Erdos64EG.lean` and update package tests and
   current-state documentation.

Do not add `sorry`, `admit`, new axioms, unsafe proof escape hatches, opaque
proof surrogates, or declarations reserved for later stages.

## Maintain the bidirectional TeX--Lean--web index

Treat manuscript indexing and the web theorem companion as part of the proof,
not post-processing. A CT stage is incomplete until the TeX source, compiled
Lean descriptor, and generated web artifact describe the same verified
frontier.

Before implementing the stage:

1. Identify the narrowest existing semantic `\label` for every definition,
   lemma, theorem, section, and proof-diagram node used by the stage.
2. Add missing labels directly to
   `proofs/erdos_64_eg/erdos_64_proof.tex`. Use stable mathematical names such
   as `def:...`, `lem:...`, `prop:...`, `thm:...`, or `sec:...`; never put Lean
   declaration names or implementation status in a LaTeX label.
3. If the formalization exposes a genuine ambiguity, missing hypothesis, or
   mathematical error, correct the manuscript statement and its dependents in
   the same invocation. Do not weaken or silently reinterpret the paper to fit
   a Lean API. If the correction is not mathematically justified, leave the
   stage unimplemented and report the discrepancy.
4. Preserve proof-diagram node numbers. Add a new node only when the
   manuscript gains a genuinely new proof step; update the detailed dependency
   table and every affected arrow or prerequisite at the same time.

After the Lean stage is proved, update
`examples/erdos_64_eg/Erdos64EG/WebExport.lean` in the same change:

- Add or extend exactly one workflow stage for the selected manuscript step,
  with its primary declaration, all reader-relevant evidence declarations,
  inbound link evidence, and problem-to-framework interface bindings.
- Add or extend the corresponding `ExampleProofStepDescriptor` in
  `erdosManuscript`. Record the stable TeX labels and diagram node IDs, a plain
  explanation, a genuine TeX mathematical statement rather than Lean pretty
  printing, the precise correspondence kind, scope limitations, and the
  practical work bound.
- Classify declarations into `ExampleDeclarationGroup`s by their actual role:
  mathematical definition, semantic theorem, encoding bridge, execution,
  trace audit, soundness/totality, work bound, provenance, framework
  interface, external theorem, or fixture. Explain what every group contributes
  to the manuscript argument.
- Expose every new public Erdős declaration that a reader needs to reconstruct
  the selected stage. If a declaration is intentionally omitted, make it
  private/local or record a concrete justification in the implementation log;
  do not leave unexplained public proof steps hidden from the web index.
- Mark the step `implemented` only after the unconditional stage audit passes.
  Keep the first future step as `next`, with no `stageId` or declaration groups;
  never attach verified declarations to an unimplemented manuscript claim.

Preserve these two-way invariants. For each implemented proof step `p` mapped
to workflow stage `s`, let `D(s)` be the union of the stage primary/evidence
declarations, matching interface-binding declarations, and evidence on links
entering `s`. The union of `p`'s declaration groups must equal `D(s)`: no
missing explanations and no unrelated declarations. Every displayed stage
must map to exactly one proof step. Reuse of one declaration by multiple stages
is allowed only when each stage explains its role independently.

The resulting navigation must work in both directions:

- TeX label or diagram node -> proof step -> workflow stage -> grouped Lean
  declarations; and
- selected Lean declaration -> declaration group and role -> plain/formal
  explanation -> exact TeX label and diagram nodes.

Do not duplicate this correspondence in an ad hoc Markdown table or encode
Lean identifiers into the paper. The Lean-owned `erdosManuscript` descriptor
is the authoritative crosswalk; the semantic labels in the TeX file are its
stable mathematical anchors, and the generated web artifact is its checked
projection.

## Keep computation local and practical

Use only the finite local data specified by the manuscript. Supply explicit
`FinEnum` values, local decision procedures, check counts, and a
`Core.PolynomialCheckBudget` or the CT-native polynomial certificate. Prefer
certificates and finite response coordinates over search.

Do not materialize all `SimpleGraph V`, all subgraphs, all colorings, all
ambient contexts, or any recursively expanding graph universe. Permit
recursion only with a visible structurally decreasing measure. If the current
contract would require global enumeration, fix the reusable local contract
instead of hiding the computation in Erdős application code.

For manuscript packing stages, distinguish maximum cardinality from maximal
saturation. Use `Core.FiniteDisjointPacking`,
`CT12.DisjointPacking`, and `Graph.InducedPathPacking` when applicable. Their
maximum is proof-selected; the executable CT12 loop receives only the
selected list, its iteration count is exactly that list's length, and it is
bounded by the host vertex count. Carry the exact covered/remainder partition
forward. When the manuscript excludes arbitrary finite subgraphs rather than
only induced supports, use `Graph.FiniteObject.InternalSubgraph` and its
generic minimum-degree monotonicity bridge. Do not mark a later
density-dependent claim such as “the remainder is large” complete merely
because its packing-derived freeness clause is already verified.

For finite induced-path attachment algebras, reuse
`Graph.InducedPathAttachment` and
`CT10.ExhaustiveClassification.Profile`. The graph layer owns compact
bit-code/finite-set equivalence, symbolic positive-gap semantics, actual
attachment labels, cycle construction, `Legal`, `Compatible`, `C`, and
`omegaTwo`. The CT10 profile owns accepted-subtype enumeration, exhaustive
execution, typed trace, semantic validity, totality, and the quadratic work
ledger. Count candidate classification itself in the ledger. Put only the
fixed path order, forbidden target predicate, concrete gap kernel, and exact
manuscript constants in the Erdős module. Connect the stage through
`EdgeRootedBoundariedInducedPathPackingAttachmentPrefix` so the CT10 branch
context and actual-label theorem come from the exact preceding packing
prefix. Use symbolic code-to-mathematics lemmas for parametric semantics;
reserve bounded reflection for the fixed finite counts.

## Place reusable changes correctly

- Keep only theorem-specific data, arithmetic, official-statement bridges,
  thin instantiations, fixtures, and export names in `examples/erdos_64_eg`.
- Put reusable graph definitions and theorems in
  `lean/StructuralExhaustion/Graph`.
- Put target-independent execution and finite machinery in `Core` or the
  owning CT, and put every reusable residual-to-trigger composition in
  `Routes`.
- Change a CT or `Core` contract only after demonstrating an API design error:
  the manuscript's local operation cannot be expressed without proof
  injection, global enumeration, or loss of a required invariant.
- Make any framework repair problem-independent, preserve automation-first
  ownership of execution, and add regression coverage. Never put Erdős names
  or constants in `Core` or a generic CT.

Difficulty proving an Erdős lemma is not evidence of a core design error.
After a framework change, rebuild every existing user of the changed API.

Before leaving this section, audit the Erdős diff declaration by declaration.
For every new non-fixture definition or theorem, state which fixed Erdős datum
prevents it from being generalized. If there is no such datum, extract it.

## Require a non-Erdős transfer instantiation

Before finishing, locate a non-Erdős problem instantiation of the selected CT.
It qualifies only if it:

- lives outside `examples/erdos_64_eg` and formalizes a named, standard
  textbook graph theorem;
- supplies concrete problem data to the same public CT/profile used here;
- executes the runner and proves its semantic result, typed trace, and
  practical work bound; and
- builds as an external example package.

When this invocation adds or extends a reusable graph/core/route profile, the
non-Erdős package must consume that exact new profile or method. Merely using
the same CT through a separately implemented adapter does not establish
transfer. Remove duplicated application proofs and make both examples thin
instantiations of the shared declaration.

The generic `lean/StructuralExhaustion/Examples/CTNAutomationFirst.lean`
fixture is useful regression coverage but does not alone satisfy this
problem-transfer requirement. If no qualifying example exists, implement the
simplest natural textbook example. Prefer extending an existing external
example when mathematically appropriate; otherwise add a small package and
wire it into the repository build and example catalog. Reuse the generalized
graph/core material instead of copying the Erdős adapter. Never introduce a
large graph universe or exponential search merely to obtain redundancy.

## Validate and record the completed frontier

Run checks proportional to every touched layer, including:

```bash
make lint
make framework-build
make erdos-example-build
make export
python3 tools/validate_repository.py --root .
python3 -m pytest -q tests/test_repository.py tests/test_example_catalog.py tests/test_web_api.py
make web-frontend-test
git diff --check
```

Also build the qualifying transfer example and run focused tests for every
changed graph, core, CT, route, or catalog surface. Regenerate tracked catalog
artifacts only when their Lean export changed, and inspect the resulting diff.

Compile `proofs/erdos_64_eg/erdos_64_proof.tex` after changing labels or
mathematics. Inspect `generated/examples/erdos-64.json` and require:

- every manuscript label and diagram node referenced by `erdosManuscript`
  exists uniquely in the TeX source;
- `explainedDeclarations == displayedDeclarations`;
- no displayed declaration is absent from the proof-step groups and no group
  names a declaration outside its mapped stage; and
- the new stage, plain explanation, formal statement, scope note, work bound,
  and implementation status appear in the generated web detail.

Do not bypass renderer, schema, source-freshness, or coverage failures. Fix the
Lean descriptor, TeX anchor, or export instead of hand-editing generated JSON.

As a final ownership check, inspect the complete Erdős Lean diff alongside
the transfer example. Reject any generic structure, runner wrapper, bridge
transport, route proof, or graph theorem that appears only in the Erdős
namespace. Confirm that the framework fixture and the external transfer
package compile before compiling the thin Erdős instantiation.

Only after all required checks pass, update
`examples/erdos_64_eg/IMPLEMENTATION_LOG.md`. Keep it a direct current-state
ledger of unconditional verification. Reconcile the whole ledger against the
compiled Lean declarations on every invocation; do not merely append the new
stage. Record:

- the verified manuscript section, theorem labels, and diagram nodes;
- the web proof-step ID, workflow stage ID, correspondence kind, and exact
  displayed-declaration coverage;
- the CT/profile and exact Erdős Lean declarations;
- the provenance chain from the official problem through prior CT outputs;
- the runner, terminal or residual, typed trace, semantic theorem, totality,
  and work-bound declarations;
- the qualifying non-Erdős instantiation and its shared reusable API; and
- the validation commands that passed and the next dependency-ready
  manuscript section, clearly marked as not yet implemented.

Do not list a conditional author interface as an unconditionally verified
stage. Do not write comparisons with older versions or claims about future
proof completion. If validation fails, leave the verified frontier unchanged.

Stop after this one CT is fully implemented, tested, built, exported, and
recorded in TeX, Lean, and the generated web projection. Do not start a second CT.
Report the exact manuscript-to-CT mapping, both directions of the
TeX--Lean index, and the declarations that connect its input to the preceding
verified output.
