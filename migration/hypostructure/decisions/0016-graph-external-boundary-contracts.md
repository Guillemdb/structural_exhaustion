# HYP-0016: Graph external theorem contracts are exact-name trust entries

Status: proposed

Date: 2026-07-22

Matrix rows: `graph.external-boundary`

## Missing Use Case

Some graph rows need a reviewed black-box theorem boundary: a stable source
reference, exact local hypotheses and conclusion, and an explicit allowlist
entry. This should not be encoded as a route, a node output, or a theorem
specific application record.

## Ownership

Graph owns the boundary packaging because the contracts refer to graph theorem
statements and graph targets. Core owns only the surrounding metadata and
ledger bookkeeping. The allowlist remains a reviewed trust artifact, not a
proof engine.

## Public Author Inputs

- One declaration reference.
- One local hypothesis proposition.
- One local conclusion proposition.
- One proof from the hypotheses to the conclusion.

## Framework Outputs

- A named local theorem contract.
- An explicit allowlist container.
- A membership predicate for reviewed entries.
- A reusable black-box theorem boundary for graph consumers.

## Residual Branches

There is no complementary mathematical branch; the contract is either
registered or it is not. Any unresolved trust decision remains external to the
Lean theorem.

## Both-Sides Test

`Hypostructure.Fixtures.GraphExternal` registers three local graph theorem
contracts and proves that each source is listed in the allowlist.

There is no PDE analogue at this exact graph trust boundary, although PDE may
reuse the same Core provision primitives for its own external contracts.

## Fixtures

- Three local graph theorem contracts.
- Reviewed allowlist membership for each source.
- `#print axioms` audit with no added axioms.

## Compatibility Impact

This adds no axiom and no routing semantics. It only packages the exact-name
graph trust boundary already described by the API.
