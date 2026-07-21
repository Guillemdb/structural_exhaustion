---
name: implement-hypostructure-ct6
description: Implement Hypostructure CT6 ordered activity analysis. Use for a first failed site, row, scale, or window; clean-prefix evidence; an exhaustive active ledger and contribution total; Graph monitored-site scans; or PDE fast-track row and window schedules.
---

# Implement Hypostructure CT6

Use CT6 for one deterministic pass over a predecessor-owned order that returns the first failed local condition or certifies activity everywhere and builds the exact contribution ledger.

## Gate the live contract

1. Read row `ct.ct6` in `migration/hypostructure/api-feature-matrix.csv`.
2. Read `hypostructure/Hypostructure/CT6/{Spec,Capability,State,Search,Execution,Theorems,Automation}.lean`.
3. Inspect `hypostructure/Hypostructure/{Graph,PDE}/CT6.lean` and `hypostructure/Hypostructure/Fixtures/CT6.lean`.
4. Confirm current declarations and fresh `.olean` evidence, for example with `cd hypostructure && lake env lean Hypostructure/Fixtures/CT6.lean`. Check any proposed downstream route in the feature matrix and live route source separately.

The generic, Graph, and PDE CT6 slices are currently present. The specialized CT6-to-CT9 route is currently marked `planned`; do not recreate its item adapter in an application. Recheck live status, and use `$extend-hypostructure-framework` for any missing CT or route surface.

## Author the ordered local test

Define `CT6.Spec` with predecessor-indexed `Index` and `FailureData`, the local `Failure` predicate, proof-dependent `failureData`, and the contribution function.

Define `CT6.Capability` with a `Core.Residual.Query` for the exact failure order, a primitive failure decider, and a polynomial proof for `localCheckBound`. The order must be the literal finite schedule in the predecessor ledger; use `Query.residual`, `latest`, `preserve`, or `map` rather than detaching it.

Treat local semantics, diagnostic extraction, contributions, the order query, decider, and work envelope as author primitives. Treat the first-hit proof and clean prefix or exhaustive active ledger, exact total, terminal, outcome, trace, work count, and accumulated stage as framework outputs in `Core.Provision` metadata.

## Execute and verify both outcomes

1. Call `CT6.execute spec capability previous`.
2. For `.firstFailure`, consume `FirstFailureResidual.member`, `.failed`, `.cleanPrefix`, and its exact `data`.
3. For `.activeLedger`, consume `ActiveLedgerResidual.activeAt`, exact `entries`, and `activeTotal`; never reconstruct the ledger from the order.
4. Prove predecessor retention, `result.verified`, `result.trace_exact`, `run_total`, determinism, outcome exhaustiveness, exact scan accounting, and `checks_le_polynomial`.
5. Route a generated residual to another CT only through a separately kernel-checked framework route that consumes the full stage and preserves all ledger queries.

For graphs, use `Graph.CT6.orderedActivitySpec` and `orderedActivityCapability`. For PDEs, use `PDE.CT6.orderedActivitySpec` and `orderedActivityCapability` for exact row, scale, or window schedules against a queried represented state.

Use `Fixtures/CT6.lean` as the acceptance standard: pin a Graph first failure and a PDE active-ledger result, including first-hit order, clean/exhaustive semantics, exact entries and total, exact trace, work, and predecessor retention.

## Practicality and carrier rules

The CT performs one pass and charges `failureOrder.card`. Do not feed it an expanding frontier, an unbounded scale family, or an application-generated replacement schedule. Use a well-founded framework peeling/saturation capability when the mathematics grows or revises the frontier.
