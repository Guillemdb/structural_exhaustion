# HYP-0015: Graph contraction is a reusable coordinate primitive

Status: proposed

Date: 2026-07-22

Matrix rows: `graph.contraction`

## Missing Use Case

Later graph nodes need a finite contraction coordinate that deletes one
vertex name, preserves the source schedule discipline, and exposes the
contracted vertex type for downstream routing. The capability must not be
encoded as an application-specific bridge constant.

## Ownership

Graph owns the contraction coordinate because it changes only graph
representation and graph adjacency semantics. Core owns the typed ledger
execution around any contraction result, but not the graph-specific vertex
redirection.

## Public Author Inputs

- One packed finite graph.
- One surviving vertex name.
- One deleted vertex name.

The caller does not provide a successor graph, a progress claim, or a route.

## Framework Outputs

- The contracted vertex type.
- The contracted graph adjacency relation.
- The contracted finite object with a filtered vertex schedule.
- A strict vertex-count decrease theorem.

## Residual Branches

The primitive is not a dichotomy. The complementary branch is handled by
whatever later graph node consumes the contracted object.

## Both-Sides Test

The graph fixture contracts a one-edge finite graph on `Fin 2` and checks the
strict vertex-count decrease.

There is no PDE-specific analogue of graph contraction itself; PDE reuse is
indirect, through the shared finite-coordinate discipline in Core.

## Fixtures

- One-edge contraction fixture.
- Strict vertex-count decrease theorem.

## Compatibility Impact

This adds a new graph coordinate primitive and no application-specific
constants. It does not alter existing graph deletion, induced restriction, or
target semantics.
