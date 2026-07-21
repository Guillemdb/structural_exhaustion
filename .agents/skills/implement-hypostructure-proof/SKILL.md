---
name: implement-hypostructure-proof
description: Implement a new theorem as a thin Hypostructure Lean application from problem registration through accumulated residuals, CT execution, framework-owned routes, closure, trust evidence, and practical work bounds. Use for end-to-end proof formalization, new external example packages, manuscript-to-Lean implementation, or coordinating Graph/PDE and CT specialists.
---

# Implement a Hypostructure Proof

Implement the supplied mathematics through live public capabilities. Read
`references/proof-work-packet.md` and fill it while working.

## Ground the proof

Read the theorem, its proof source, the four Hypostructure authority documents,
the relevant migration rows, and the exact live modules. Use
`$understand-hypostructure-framework` when the capability surface is unclear and
`$design-hypostructure-proof` to select the CT chain.

Classify every needed feature as kernel checked, source-only, or planned. Use a
source-only or planned feature only after `$extend-hypostructure-framework`
completes its public vertical slice. Never reproduce missing Core, CT, or Routes
machinery inside the application.

## Register the application root

Create or extend an external package that depends on `hypostructure` and imports
only Mathlib, Hypostructure, and its own modules. Define:

1. the irreducible `Core.Problem` and public target;
2. optional well-founded progress only when the proof actually descends;
3. domain semantic equivalence and target invariance;
4. one theorem-owned initial residual containing only root assumptions; and
5. one `Core.Residual.Ledger.initial` stage.

Never seed later conclusions, target avoidance, selected branches, CT outcomes,
or migration status in the root residual.

## Implement the directed proof

For each mathematical node:

1. consume the literal predecessor stage;
2. retrieve inherited values through typed `Core.Residual.Query` or active-focus
   queries rather than copied fields or rederivation;
3. contribute only mathematics first established at that node;
4. use Core decisions/focus for exhaustive branches;
5. invoke the CT's public automation or domain constructor;
6. let framework-owned routing preserve and extend the full ledger; and
7. keep every nonterminal residual typed with a declared consumer.

Application code must not construct `Core.Routing.Profile`, call route advances,
restage ledgers, choose a CT result, or fabricate a detached carrier. If a route
or query is missing, implement the parameterized facility at its owning layer.

## Prove the execution contract

Retain and expose the terminal-indexed outcome, exact typed trace, semantic
soundness, exhaustiveness/totality, determinism where promised, and the actual
`Core.PolynomialCheckBudget`. Test every complementary residual, not only the
desired branch. Add `Core.Metadata.DeclarationMetadata` with no manual
obligations for public executable declarations.

Keep computation local: use predecessor-owned finite schedules, finite response
tables, and proof-carrying certificates. Reject ambient graph universes,
continuum enumeration, unbounded completion search, or recursive exploration
without a registered decreasing measure.

## Respect domain ownership

Use `$implement-hypostructure-graph-proof` for packed finite graph semantics and
`$implement-hypostructure-pde-proof` for represented PDE semantics. Fixed theorem
constants and arithmetic remain in the application. A reusable declaration must
move to Core, the CT, Routes, Graph, or PDE and receive a neutral or second-domain
fixture before the application consumes it.

## Validate and report

Run the smallest focused package build, relevant fixtures, the import firewall,
`#print axioms` on public endpoints, and the application integration checks.
Report the theorem endpoint, CT chain, literal provenance chain, framework
extensions, all residual branches, work bound, trust result, and commands. Do
not claim completion while a manual obligation, untested residual, planned API,
or failed check remains.
