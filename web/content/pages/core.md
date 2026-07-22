# Core

Core is the domain-independent proof engine. It owns state transport and execution while leaving mathematical meaning to applications and domain layers.

## Problems and contexts

`Problem` separates ambient objects, baseline validity, and branch state. Optional progress and semantic-equivalence capabilities add well-founded descent or representation-invariant reasoning only when a proof needs them.

## Residuals and proof ledgers

A residual is stable across the proof program. Each stage extends a dependent ledger, so later nodes can query old facts without copying them into application records.

## Decisions, focus, and joins

Core computes certified alternatives, selects active branches, preserves untouched siblings, and joins typed predecessor stages. Applications provide evidence, not caller-chosen outcomes.

## Coordinates and assembly

Domains register primitive coordinate actions and reconstruction laws. Core composes paths, transports evidence, and performs local-to-global assembly.

## Execution, budgets, routing, and closure

Executors return typed outcomes and traces with polynomial check budgets. A route is executable only when a typed transition supplies discovery, target input, a target executor, and full-ledger preservation.
