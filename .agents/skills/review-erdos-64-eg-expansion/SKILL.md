---
name: review-erdos-64-eg-expansion
description: "Audit and repair one completed round of the Erdős--Gyárfás Problem 64 expansion. Use after implement-next-erdos-64-eg-ct, or when a claimed frontier must be checked for unconditional Lean provenance, exact agreement with proofs/erdos_64_eg/erdos_64_proof.tex, TeX--Lean--web synchronization, practical local computation, sole-HSS trust, and maximal reuse through Core, CT, Routes, and Graph."
---

# Review One Erdős 64 Expansion Round

Review the most recently claimed CT stage, repair defects within that stage,
and stop. Do not implement the next CT. A clean review means that the current
paper claim, compiled Lean theorem, execution trace, generated proof view, and
implementation ledger describe the same unconditional result.

## Establish the review authority

1. Work from `git rev-parse --show-toplevel`; inspect `git status --short` and
   preserve unrelated edits. Treat the current declarations and claimed
   frontier as the audit scope; never assume that every dirty file belongs to
   the expansion round.
2. Read completely:

   - `.agents/skills/implement-next-erdos-64-eg-ct/SKILL.md`;
   - `.agents/skills/design-structural-exhaustion-proof/SKILL.md`;
   - the selected `implement-structural-exhaustion-ctN/SKILL.md` and, when
     used, `implement-structural-exhaustion-route/SKILL.md`;
   - the preliminary architecture, all Chapter 1 proof-flow diagrams, the
     detailed dependency row, and every cited definition and proof in
     `proofs/erdos_64_eg/erdos_64_proof.tex`;
   - `OfficialStatement.lean`, `InternalProblem.lean`, every Erdős `CT*.lean`,
     `Erdos64EG.lean`, `Tests.lean`, `WebExport.lean`, `README.md`, and
     `IMPLEMENTATION_LOG.md` under `examples/erdos_64_eg`; and
   - every changed or consumed declaration in `Core`, the selected CT,
     `Routes`, and `Graph`, plus the non-Erdős transfer example.

3. Inspect the compiled authorities rather than trusting prose summaries:

   ```bash
   jq '.tactics[] | {tacticId, capability, capabilityProfiles, terminals, residualKinds}' generated/lean-machines.json
   jq '.routes' generated/lean-machines.json
   jq '.example.manuscript' generated/examples/erdos-64.json
   ```

The manuscript specifies the mathematics, the official Lean statement fixes
the problem boundary, and kernel-checked declarations determine what has
actually been proved. Generated files are checked projections, never sources
to edit by hand.

## Freeze the exact CT block

Reconstruct the frontier independently from the theorem-bearing endpoint,
imports, `WebExport.lean`, and the implementation log. Identify the one CT
added by the reviewed round and all diagram nodes covered by that single CT;
one CT may encompass several nodes. Follow arrows and prerequisites rather
than assuming node-number order.

Before repairing anything, write an audit row:

| Manuscript labels and nodes | Previous verified Lean output | CT/profile and route | Concrete local universe | Claimed terminal/residual | Exported theorem | Work bound |
|---|---|---|---|---|---|---|

List every new theorem-level manuscript claim and its exact Lean declaration.
Exclude later CTs even if the manuscript discusses them nearby.

## Audit unconditional Lean provenance

Count the stage as unconditionally verified only if every check below passes.

1. The public endpoint starts from the official object, baseline, and target
   avoidance, or constructs its prior verified context internally. It does not
   accept the new conclusion, a CT outcome, a terminal equality, a route
   result, a capability, a response-correctness theorem, a survival
   hypothesis, or another author contract that the stage is meant to derive.
2. The new input is constructed from the exact preceding execution output on
   the same dependent context. Require a typed `previous` field or a theorem
   proving provenance; audit any context equality instead of rebuilding a
   look-alike context.
3. Every problem-specific mathematical object, predicate, decider, semantic
   bridge, and finite datum required by the manuscript is defined. Reject
   `True`, `False`, empty universes, opaque booleans, or caller data used as
   placeholders unless an exact theorem proves that they are the manuscript
   semantics.
4. The public framework runner is actually executed. Retain its
   terminal-indexed outcome, typed path and trace, semantic soundness,
   totality, and deterministic or branch-specific facts required by the CT.
   An interface, wrapper, structure, or definition without an execution is not
   a completed stage.
5. If a particular terminal is claimed, derive it from earlier theorems and
   the runner. Do not assume the premise that rules out the other terminals.
   If the mathematics is a dichotomy, export the exhaustive dichotomy rather
   than declaring one branch unconditionally.
6. Check all branches and all nodes belonging to the selected CT block. Do not
   mark only the first diagram node implemented.

Search the reviewed dependency cone for `sorry`, `admit`, unsafe declarations,
new axioms, and proof surrogates. Use `#print axioms` on the endpoint and the
new semantic theorems. The sole permitted external theorem is the declared
Hegde--Sandeep--Shashank theorem, and only declarations whose proof genuinely
uses that node may inherit it. A noncomputable proof-selected certificate is
acceptable only when its existence is proved and the executable CT scans the
declared local data rather than pretending to compute that choice.

## Check the manuscript mathematics against Lean

For every cited definition, lemma, displayed identity, and case split, compare
hypotheses and conclusions in both directions:

- prove that each executable predicate is equivalent to the manuscript
  predicate;
- verify constants, index ranges, cardinalities, inequality directions,
  strictness, endpoint conventions, and natural-number subtraction;
- verify that every manuscript dependency is provided by an earlier Lean
  output, not by a later-stage fact; and
- verify that the Lean conclusion is neither weaker nor differently scoped.

When Lean exposes a paper error, repair the paper only with mathematics already
kernel-verified in this round. Update the affected definition or theorem,
adjacent proof, formulas, dependency row, and diagram wording consistently,
while preserving stable semantic labels where their mathematical subject is
unchanged. Search every downstream `\cref` and formula for consequences of the
correction. Never weaken or rewrite the paper merely to conceal an unproved
Lean obligation, and never insert Lean declaration names into LaTeX labels or
mathematical prose.

If the manuscript claim cannot be recovered from its stated strategy and
verified mathematics, do not invent a new argument. Keep the public endpoint
at the previous unconditional frontier, mark the reviewed step unimplemented
in the Lean-owned proof crosswalk and current-state ledger, and report the
exact missing mathematical implication.

## Enforce practical structural exhaustion

Audit the computation that the runner performs, not just the theorem's logical
truth.

- Require an explicit finite local universe and observable order where the CT
  needs one.
- Require exact primitive-check accounting and a
  `Core.PolynomialCheckBudget` or CT-native polynomial bound in the declared
  problem size.
- Reject enumeration of all `SimpleGraph V`, all subgraphs, all ambient
  contexts, all colorings, or a recursively expanding frontier.
- Require every recursion to expose a structurally or well-founded decreasing
  measure.
- Restrict `native_decide` to fixed, genuinely small finite tables with a
  proved semantic reflection theorem; never use it to traverse a variable
  graph universe.
- Prefer proof-carrying local certificates and finite response coordinates.
  Do not charge a proof-selected witness as if it were an executable global
  search.

If the current API forces impractical computation, fix the reusable contract
and add regression coverage. Do not hide the computation in Erdős-specific
code.

## Audit framework ownership and transfer

Classify every declaration introduced or materially changed by the round:

| Dependency | Required owner |
|---|---|
| Generic problems, contexts, finite collections, rank, or arithmetic machinery | `Core` |
| One CT's runner, result, residual, trace, or generic semantic theorem | That CT namespace |
| Residual-to-trigger conversion, context transport, or route provenance | `Routes` |
| Mathlib graph objects parameterized by degree, target predicate, boundary, or local certificate | `Graph` |
| Power-of-two/Mersenne arithmetic, fixed constants, and official bridges | `examples/erdos_64_eg` |

Apply the parameterization test declaration by declaration: if replacing
degree three, path order thirteen, or the power-of-two target leaves the
statement meaningful, extract it to the framework. Erdős files may retain
only concrete data, reflection proofs, thin instantiations, fixtures, export
names, and genuinely problem-specific arithmetic. Do not move Erdős names or
constants into `Core`, and do not introduce framework imports of an example.

Confirm that a named textbook example outside `examples/erdos_64_eg` consumes
the exact new graph/core/CT/route profile, executes the same public runner, and
proves its trace, semantics, totality, and practical bound. A generic CT
fixture using an unrelated adapter is insufficient. If the two examples
repeat the same proof shape, extract it and make both applications thin.

Change a core or CT contract only for a demonstrated general API defect, then
rebuild every existing consumer. Difficulty with one Erdős lemma is not an API
defect.

## Reconcile TeX, Lean, web, and the ledger

Treat `Erdos64EG/WebExport.lean` and its `erdosManuscript` descriptor as the
authoritative crosswalk. For every implemented proof step `p` mapped to stage
`s`, let `D(s)` be the union of stage primary/evidence declarations,
interface-binding declarations, and incoming-link evidence including
`automationDeclarations`. Require the union of `p`'s
`ExampleDeclarationGroup`s to equal `D(s)` exactly.

Verify both navigation directions:

- TeX label or diagram node -> proof step -> workflow stage -> grouped Lean
  declarations; and
- Lean declaration -> declaration group and role -> plain/formal explanation
  -> exact TeX label and nodes.

Require every displayed stage to map to exactly one proof step, every label and
node to exist uniquely, theorem fragments to include their adjacent proof, and
`explainedDeclarations == displayedDeclarations`. Mark the reviewed step
`implemented` only after the unconditional audit passes. Keep the first future
step `next` without a stage ID or verified declaration group. Regenerate with
`make export`; never hand-edit `generated/examples/erdos-64.json`.

Reconcile all of `IMPLEMENTATION_LOG.md`, rather than appending a success
paragraph. It may list only kernel-checked unconditional claims and must name
the exact prior output, runner, terminal or residual, trace, semantic theorem,
totality theorem, work bound, transfer example, and next frontier. Keep README
and top-level imports consistent with the same endpoint.

## Repair and validate

Fix the root layer first: generic semantics in Core/CT/Routes/Graph, concrete
instantiation in Erdős, mathematical prose in TeX, and finally the Lean-owned
web crosswalk and generated projection. Add regression tests for every defect
found. Repeat the audits until clean; do not advance another CT.

Run all checks affected by the round, including:

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

Run focused Lean builds for the selected CT and transfer example before the
full suite. Inspect generated diffs and the final `#print axioms` output. Do
not report a clean review if a required check fails.

Finish with a concise verdict containing: the reviewed labels/nodes and CT,
the unconditional endpoint and provenance chain, any mathematical correction
made to the paper, abstractions moved to framework layers, transfer coverage,
local work bound, TeX--Lean--web coverage, trust result, and validation
commands. If the stage fails, identify the last unconditional endpoint and the
single precise gap; do not describe the failed stage as implemented.
