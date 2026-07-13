---
name: implement-next-erdos-64-eg-ct
description: "Advance the repository's Erdős--Gyárfás Problem 64 Lean formalization by exactly one structural-exhaustion CT selected from the manuscript proof flow. Use when continuing proofs/erdos_64_eg/erdos_64_proof.tex: identify the first dependency-ready stage not yet unconditionally verified, map its prose to CT1--CT17, construct its problem-specific inputs from the official graph and earlier CT outputs, execute the framework rigorously, add a simple non-Erdős transfer example when needed, build the affected packages, and update the implementation log."
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

| Manuscript section and nodes | Prior Lean output | CT/profile | Concrete local input | Expected output | Next consumer | Work bound |
|---|---|---|---|---|---|---|

Map its mathematical operation to one CT using
`design-structural-exhaustion-proof`. Read the selected
`.agents/skills/implement-structural-exhaustion-ctN/SKILL.md` completely. If
the exact compiled flow is a registered route, also read
`.agents/skills/implement-structural-exhaustion-route/SKILL.md`; otherwise
compose proved outputs directly.

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

## Place reusable changes correctly

- Keep theorem-specific data and adapters in `examples/erdos_64_eg`.
- Put reusable graph definitions and theorems in
  `lean/StructuralExhaustion/Graph`.
- Change a CT or `Core` contract only after demonstrating an API design error:
  the manuscript's local operation cannot be expressed without proof
  injection, global enumeration, or loss of a required invariant.
- Make any framework repair problem-independent, preserve automation-first
  ownership of execution, and add regression coverage. Never put Erdős names
  or constants in `Core` or a generic CT.

Difficulty proving an Erdős lemma is not evidence of a core design error.
After a framework change, rebuild every existing user of the changed API.

## Require a non-Erdős transfer instantiation

Before finishing, locate a non-Erdős problem instantiation of the selected CT.
It qualifies only if it:

- lives outside `examples/erdos_64_eg` and formalizes a named, standard
  textbook graph theorem;
- supplies concrete problem data to the same public CT/profile used here;
- executes the runner and proves its semantic result, typed trace, and
  practical work bound; and
- builds as an external example package.

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
python3 tools/validate_repository.py --root .
python3 -m pytest -q tests/test_repository.py
git diff --check
```

Also build the qualifying transfer example and run focused tests for every
changed graph, core, CT, route, or catalog surface. Regenerate tracked catalog
artifacts only when their Lean export changed, and inspect the resulting diff.

Only after all required checks pass, update
`examples/erdos_64_eg/IMPLEMENTATION_LOG.md`. Keep it a direct current-state
ledger of unconditional verification. Reconcile the whole ledger against the
compiled Lean declarations on every invocation; do not merely append the new
stage. Record:

- the verified manuscript section, theorem labels, and diagram nodes;
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
recorded. Do not start a second CT. Report the exact manuscript-to-CT mapping
and the declarations that connect its input to the preceding verified output.
