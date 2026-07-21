---
name: implement-hypostructure-graph-proof
description: Implement finite graph theorems through Hypostructure's Graph layer, including packed objects, graph problems and targets, isomorphism semantics, coordinates, deletion, boundary/gluing, responses, progress, Graph CT constructors, and practical fixtures. Use for new graph applications, reusable graph profiles, or graph-specific framework gaps.
---

# Implement a Hypostructure Graph Proof

Read `references/graph-proof-work-packet.md`, `GRAPH_LAYER_API.md`, the relevant
Core/Graph source, and the closest Graph fixtures for semantic registration and
CT branch coverage completely. Do not assume one fixture covers both concerns.

## Check live Graph support

Verify every proposed module against `migration/hypostructure/api-feature-matrix.csv`,
source, a fresh build, and a consuming fixture. Treat planned contraction,
budget, theorem, external-boundary, route, or CT-adapter rows as unavailable
until implemented. Use `$extend-hypostructure-framework` for a missing reusable
surface; do not implement it in the graph application.

## Register graph semantics

Use `Graph.FiniteObject` as the irreducible object. Register the baseline and
branch state as a `Core.Problem`, then define the public target through a
`Graph.TargetInterface`. Prove graph-isomorphism invariance and derive the Core
semantic equivalence and target invariance through Graph.

Use existing Graph primitives for induced objects, deletion, boundary,
interfaces, gluing, finite views, minimality, progress, responses, and rooted
returns. Keep fixed graph names, constants, path lengths, coloring alphabets,
and theorem-specific arithmetic in the application.

## Build the residual-owned local data

Start one root ledger from the packed input. Derive every later vertex, edge,
piece, context, response coordinate, or schedule from the literal predecessor
through typed queries. Preserve occurrence identity and exact enumeration order.
Never enumerate all `SimpleGraph V`, all subgraphs, all colorings, all ambient
contexts, or a powerset merely because the type is finite.

## Use Graph CT constructors

Select the CT by its domain-independent mathematical role, then prefer the live
constructor under `Hypostructure.Graph.CTN`. The Graph layer may translate
primitive graph semantics into a CT capability and prove graph-target bridges;
the CT owns search, outcomes, residuals, traces, soundness, totality, and work.

Call the matching `$implement-hypostructure-ctN` for the exact contract. If the
Graph adapter or CT automation is incomplete, extend it generically with a
Graph fixture and, where semantically meaningful, a neutral or PDE fixture.

## Keep applications thin

Let Core own residual ledgers, queries, decisions, focus, assembly, and budgets.
Let Routes own CT transitions. Application code supplies only concrete graph
data, primitive deciders, source mathematics, and public bridges. Reject graph
wrappers whose only purpose is to conceal application-authored routing or a
caller-supplied CT result.

## Validate

Build the Hypostructure package, the focused Graph fixtures, and the external
application package. Run the import firewall and `#print axioms` on public
semantic theorems. Exercise each terminal and residual on small named graphs;
pin deterministic search order and primitive-check counts. Report transfer to
at least one non-target graph example for every new reusable profile.
