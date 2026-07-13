---
name: design-structural-exhaustion-proof
description: Select and chain structural-exhaustion CTs for a new Lean theorem from a manuscript or mathematical proof. Use when mapping proof prose to CT1-CT17, choosing reusable graph or core profiles and typed routes, auditing local finite universes, or coordinating an end-to-end verified example implementation.
---

# Design a Structural Exhaustion Proof

Translate the supplied mathematics into the smallest practical chain of existing CT contracts. Implement the mathematics stated by the source; do not invent replacement lemmas, global universes, or proof assumptions.

## Establish the formal authority

1. Work from the repository root returned by `git rev-parse --show-toplevel`.
2. Read the exact public theorem and the manuscript section that proves the requested slice.
3. Read `README.md`, `docs/architecture.md`, and the relevant portion of `framework/branch_closure_methodology_extended.tex`.
4. Inspect the compiled registry before choosing a CT:

   ```bash
   jq '.tactics[] | {tacticId, title, capability, capabilityProfiles, terminals, residualKinds}' generated/lean-machines.json
   jq '.routes' generated/lean-machines.json
   ```

5. Treat the compiled Lean declarations and catalog as authoritative. Treat generated prose and diagrams as inspection views.

## Select CTs by mathematical role

Use the manuscript's operation, not superficial vocabulary, to select a tactic.

| CT | Select it for |
|---|---|
| CT1 | A target certificate or a finite search for a realization. |
| CT2 | A minimal-counterexample deletion or exhaustive local replacement step. |
| CT3 | Equality or compression of finite local response vectors across compatible contexts. |
| CT4 | Assigning demands to eligible payers and comparing fibre capacity. |
| CT5 | Locating unsupported local witnesses or aggregating their contributions. |
| CT6 | The first failure in an explicit order, or the ledger obtained when every local check is active. |
| CT7 | Realization in a context, a distinguishing context, or exact neutrality. |
| CT8 | Repeated exact types followed by response comparison and possible removal. |
| CT9 | An overloaded fibre in a finite label partition. |
| CT10 | A direct datum, a missing class, or promotion after exhaustive classification. |
| CT11 | Localizing a negative finite total to one cell. |
| CT12 | Well-founded peeling with restoration and a verified decreasing continuation. |
| CT13 | Tier-one assignment, canonical fallback, reconciliation, and deficit comparison. |
| CT14 | Comparing aggregate lower mass with optional capacities and label multiplicities. |
| CT15 | A target-relative rank drop or a full-rank capacity ledger. |
| CT16 | Exhausting support and comparing the resulting closed code with a target code. |
| CT17 | Bounded compatibility, scale, survivor, and orbit arithmetic. |

Prefer one CT that exactly matches the prose over several CTs that simulate it indirectly.

## Reuse framework profiles first

Search for an existing constructor before defining a raw capability. In particular, inspect:

- `Graph.MinimumDegreeCycle.StaticInput` for graph targets with deletion criticality;
- `Graph.EndpointParityCycle.Profile` for the maximal-path CT6-to-CT9 cycle pipeline;
- `Graph.GreedyColoring` for CT12 peeling, CT4 color choice, and CT1 validation;
- `CT1.TargetCertificateEncoding` and `CT1.TargetEncoding`;
- `CT2.LocalDeletionCapability` and `CT2.Capability.deletionOnly`;
- `CT3.TargetCompressionContract`;
- `CT4.FunctionalCardinalityProfile`;
- `CT9.ParityCapacityOneSpec`;
- `CT11.NegativeBudgetProfile`;
- `CT12.ListPeeling`;
- `Core.FiniteSaturation.Machine`.

Read the matching external example when one exists: `examples/even_cycle`, `examples/erdos_64_eg`, `examples/greedy_coloring`, or `examples/mantel`.

## Write the execution map

Before editing Lean, record one row for every selected manuscript step:

| Source step | CT/profile | Local input | Author primitives | Expected terminal or residual | Next consumer | Work bound |
|---|---|---|---|---|---|---|

Require every row to identify the exact local universe being inspected. Reject a row that says only "all graphs", "all subgraphs", "all colorings", or another ambient exponential universe.

Use a registered route only for these compiled residual flows:

- CT1 avoidance to CT2;
- CT2 separating context to CT3;
- CT2 criticality to CT10;
- CT6 active ledger to CT9.

For any other sequence, compose proved theorem outputs explicitly. Do not represent ordinary theorem composition as a registered route.

## Enforce practical local computation

- Build `FinEnum` values from proof-specified local data. Use `Core.OrderedCollection` only when first-hit order is observable and use `Finset` for unordered sums and cardinalities.
- Prefer a supplied certificate over searching for one. Prefer a finite coordinate response with a reflection theorem over deciding the target on glued ambient objects.
- State the exact number of primitive checks. Prove a `Core.PolynomialCheckBudget` or the CT's native work-bound theorem against a declared input size.
- Use only structurally decreasing recursion. For CT12 and finite saturation, expose the decreasing measure consumed by the framework runner.
- Do not enumerate `SimpleGraph V`, every subgraph, every coloring function, or a recursively expanding universe of contexts.
- Keep reference semantics as the proof authority. Add an optimization only with a theorem equating it to the reference result.

If the manuscript's local step is not practical under the current API, generalize the framework contract or graph layer so the local data and work theorem become reusable. Do not hide the issue in application code.

## Implement the selected chain

1. Define one `Core.Problem` and shared contexts.
2. Read and follow each selected `.agents/skills/implement-structural-exhaustion-ctN/SKILL.md` completely.
3. Read and follow `.agents/skills/implement-structural-exhaustion-route/SKILL.md` for every registered route used.
4. Implement only problem-specific primitives in the example package. Put theorem-independent finite machinery in `Core`, graph mathematics in `Graph`, and CT execution semantics in the relevant CT namespace.
5. Invoke the public reference runner. Retain the terminal, typed path, and terminal-indexed outcome together.
6. Prove semantic soundness, totality, the expected terminal, the exact trace, and the local work bound.
7. Add a small concrete fixture that pins execution without serving as a substitute for the general theorem.

Do not leave declarations for later proof stages half-filled. Omit future stages until their manuscript section is selected.

## Completion gate

Finish only when the requested slice:

- contains no admissions, unsafe declarations, caller-authored outcomes, or hidden global solvers;
- compiles through the external package boundary;
- exposes the exact theorem proved, the CT executions used, and their typed traces;
- passes the architecture linter and repository validator;
- has no manual node obligations; and
- describes the current implementation directly without claiming unimplemented manuscript stages.
