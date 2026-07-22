# HYP-0006: Explicit overlap under unrestricted graph gluing

Status: implemented

Date: 2026-07-21

Matrix rows: `graph.boundary-overlap`, EG node 13 obligation

## Missing Use Case

Graph gluing identifies common boundary labels and takes the union of both
edge sets. Either side may own a boundary-to-boundary edge, so local degrees
and local edge counts do not add directly. The Graph layer previously exposed
the union but lacked the exact overlap object and inclusion--exclusion laws
needed to state a rigorous replacement contract.

This gap became visible while translating original EG Node 13. It is a generic
fact about finite graph gluing, not an EG-specific repair.

## Ownership

The capability belongs to Graph. Boundary-edge ownership, graph degree,
edge-count cardinality, and graph lexicographic progress are graph semantics.
Core continues to own replacement execution, ledger extension, decisions, and
routing once a Graph profile supplies the semantic transfer facts.

## Public Author Inputs

- A labelled `BoundaryPiece` and `OutsideContext` already present in a
  residual-owned decomposition.
- For degree transfer, equality of local boundary-degree profiles and equality
  of actual overlap-degree profiles against that same context.
- For progress transfer, local lexicographic progress and equality of overlap
  edge counts against that same context.

The caller does not supply a glued graph, a final degree function, a global
edge count, or a routing result.

## Framework Outputs

- The graph of boundary edges owned by both sides.
- Its degree profile and edge count.
- Equality between embedded contribution intersection and the embedded
  overlap graph.
- Exact glued-degree inclusion--exclusion.
- Exact glued-edge-count inclusion--exclusion.
- Final boundary-degree equality under the two necessary equalities.
- Global lexicographic progress under local progress and equal overlap count.

## Residual Branches

This module contains semantic identities, not a decision. It deliberately does
not turn missing overlap agreement into a closure. A replacement executor must
either receive an agreement theorem from an approved producer or preserve the
failure as a typed residual.

## Both-Sides Test

The positive fixture uses a nonempty overlap and proves both
inclusion--exclusion identities plus strict-progress transfer when overlap is
unchanged. The negative EG-source fixture constructs equal local profiles with
different overlap and proves that final degree equality and global strict edge
progress fail.

There is no PDE interpretation of graph edge overlap; transfer is established
with two independent finite graph fixtures rather than leaking graph
vocabulary into Core.

## Fixtures

- Exact nonzero overlap degree and edge count.
- Exact degree and edge inclusion--exclusion.
- Strict-progress transfer with equal overlap count.
- Kernel counterexample to transfer from local profiles alone.
- Public theorem axiom audits within the standard Mathlib footprint.

## Compatibility Impact

This is an additive Graph API and does not restrict the existing gluing context
class. It does not approve or instantiate a correction to original EG Node 13.
The immutable source remains unchanged, and the node remains mathematically
open pending an explicit repair decision.
