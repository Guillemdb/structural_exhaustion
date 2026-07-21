---
name: implement-hypostructure-ct8
description: Implement Hypostructure CT8 exact-type repetition and response analysis. Use for ordered residual-owned state sequences, first repeated finite types, response-separating contexts, certified strict removal, graph recurrence, or PDE profile and scale recurrence.
---

# Implement Hypostructure CT8

Use CT8 to find the first equal-type pair in an ordered predecessor-owned sequence, compare that pair across every exact response context, and return no repetition, separation, or a certified strict removal.

## Gate the live contract

1. Read row `ct.ct8` in `migration/hypostructure/api-feature-matrix.csv`.
2. Read `hypostructure/Hypostructure/CT8/{Spec,Capability,State,Search,Execution,Theorems,Automation}.lean`.
3. Inspect `hypostructure/Hypostructure/{Graph,PDE}/CT8.lean` and `hypostructure/Hypostructure/Fixtures/CT8.lean`.
4. Confirm current declarations and fresh kernel evidence, for example with `cd hypostructure && lake env lean Hypostructure/Fixtures/CT8.lean`. Matrix status, source presence, and fresh `.olean` evidence must agree before use.

The generic, Graph, and PDE recurrence slices are currently present. If the required exact-type universe, response coverage, progress notion, output, or adapter is missing, do not simulate it in an application; use `$extend-hypostructure-framework`.

## Define only recurrence primitives

Define `CT8.Spec` with predecessor-indexed states, exact types, response contexts and values, a removal type, `exactType`, `response`, and `StrictlySmaller`.

Define `CT8.Capability` with exact `Core.Residual.Query` values for:

- the ordered state list;
- the complete exact-type universe; and
- the complete response-context universe.

Also supply response-value equality, the removal operation for the framework-selected pair, its strict-progress theorem, and a polynomial envelope. Never pass a chosen pair, response result, or removal certificate.

CT8 derives the lexicographic `orderedPairSchedule` from the queried list and obtains exact-type decidability from the queried complete universe. Treat only the semantic operators, typed queries, equality, removal, strictness, and work proof as author primitives or inferred inputs. Treat pair discovery, response scan, selected context, removal certificate, terminal, trace, and ledger extension as framework outputs in `Core.Provision`.

## Execute all recurrence outcomes

1. Call `CT8.execute capability previous`.
2. Consume the generated terminal:
   - `.noRepetition` with `NoRepetitionCertificate`;
   - `.separation` with `SeparationResidual`; or
   - `.removal` with `RemovalCertificate` and its universal response equality and strictness proof.
3. Use the result projections guarded by terminal equality; never repeat the pair or context scan to recover evidence.
4. Prove literal predecessor retention, `result.verified`, `result.trace_exact`, the relevant terminal-forcing theorem, `run_total`, determinism, outcome exhaustiveness, `checks_exact`, `checks_le_limit`, and `checks_le_polynomial`.

For graphs, use `Graph.CT8.orderedRecurrenceSpec` and `orderedRecurrenceCapability` so removal is a graph strictly below the queried source. For PDEs, use `PDE.CT8.profileRecurrenceSpec` and `profileRecurrenceCapability` so removal is a represented state below the queried source.

Use `Fixtures/CT8.lean` as the acceptance pattern: test neutral no-repetition, Graph response separation with pinned first pair and context, and PDE strict removal with response equality, exact work, trace, and kernel-audited semantics.

## Practicality and carrier rules

The pair schedule is framework-derived and quadratically bounded by sequence length; the full check bound adds one response-context pass. Require the input sequence and complete finite universes to come from the residual. Never enumerate all objects of a type, generate an unbounded recurrence sequence, or construct a replacement carrier at the node.
