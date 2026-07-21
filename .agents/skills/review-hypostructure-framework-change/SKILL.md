---
name: review-hypostructure-framework-change
description: Adversarially review a Hypostructure Core, CT, Routes, Graph, or PDE change for ownership, minimal capabilities, literal accumulated-ledger preservation, complete execution, residual coverage, locality, work bounds, transfer, imports, migration evidence, and trust. Use before accepting framework extensions or status promotions.
---

# Review a Hypostructure Framework Change

Assume the change is incomplete until the evidence in
`references/framework-review-checklist.md` is satisfied.

## Reconstruct the claim

Inspect the diff, dirty worktree, relevant API sections, migration rows, source
modules, fixtures, and real consumers. State exactly what capability is claimed,
which layer owns it, and whether the change claims source presence, kernel
evidence, execution, parity, mathematical closure, or integration.

Never infer a higher status from a lower one. A registry row, declaration,
`.olean`, fixture, parity theorem, and public theorem are different evidence.

## Audit architecture and imports

Apply the parameterization test declaration by declaration. Reject application
constants in framework modules, domain dependencies in Core or CTs, route logic
outside Routes, and reverse imports. Run `tools/check_hypostructure_imports.py`;
reject legacy, generated, parity, compatibility, handoff, or migration-state
dependencies in production.

## Attack the capability boundary

List every field and classify it with `Core.Provision`. Reject author inputs
that provide an outcome, selected branch, successor, route, trace, work count,
closure, final theorem, or data that should be queried from the predecessor.
Require complete `Core.Metadata` with no manual obligations.

Check that all finite schedules are exact residual-owned data. Reject detached
replacement carriers, ambient graph universes, continuum enumeration, hidden
powersets, and recursion without a decreasing measure.

## Audit ledgers and routes

Require the literal complete predecessor, stable root residual, typed queries,
and exactly one framework-owned ledger extension. For a route, verify that a
typed `Core.Routing.Profile` performs semantic discovery and real target
execution. A `Routes.Registry.Entry`, including `baseline`, is not executable
evidence. Applications must not see route plumbing.

## Audit executable completeness

For CT work, require the full Spec-to-Automation vertical slice, domain
constructors, and public execution. For every change require all outcomes,
typed residuals, exact trace, semantic soundness, totality, determinism where
promised, and a proved `Core.PolynomialCheckBudget`. Exercise every branch with
small fixtures and pin deterministic order.

Require transfer at the abstraction's claimed level: neutral plus applicable
Graph/PDE fixtures for shared code, or two named consumers for a domain profile.
A fixture that bypasses the public executor does not count.

## Audit trust and migration evidence

Search the dependency cone for `sorry`, `admit`, `unsafe`, and unauthorized
axioms. Run `#print axioms` on public endpoints. Any external Graph/PDE contract
must be exact-name allowlisted, locally stated, and covered by a decision record;
final theorem or target-completeness assumptions are forbidden.

Verify that refreshed CSV statuses follow the guide's vocabulary and evidence
rules. Reject parity as authority and reject status promotion from stale `.olean`
files or generated views.

## Issue a verdict

Return PASS only when there are no blocking or required-cleanup findings and all
focused checks pass. Otherwise return FAIL with the first exact violated
contract, its owner, affected consumer, and the evidence needed to clear it.
Do not repair code unless the user also requested implementation.
