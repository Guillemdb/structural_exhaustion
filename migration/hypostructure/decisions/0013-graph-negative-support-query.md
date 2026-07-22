# HYP-0013: Parameterized negative-support query surface

Status: implemented

Date: 2026-07-22

Matrix rows: `graph.negative-support`

## Missing Use Case

The Part-V graph branch needs a literal connected finite support, a negative
signed charge, and an exhaustive split according to an ambient degree
threshold. The legacy route mixed graph observables, application constants,
and branch transport. The new API must expose only the graph contract and
derive all classifications from predecessor-owned queries.

## Ownership

The support carrier and ambient degree classification belong to Graph. Core
owns binary decisions, residual extensions, and routing. The charge formula,
connectivity proof, baseline, scale, and threshold remain application or PDE
contract inputs.

## Public Author Inputs

- A finite support in one `FiniteObject`.
- Its connectivity proposition and signed point-charge function.
- A proof that the support charge is negative.
- A threshold read from the predecessor query.

The caller does not provide a selected high center, complementary residual,
successor stage, copied graph, or route.

## Framework Outputs

- High-center and no-high predicates with derived decidability.
- A proof-selected high witness when the high predicate holds.
- The complementary no-high theorem.
- Query projections for high centers and both decisions.
- The generic no-high ambient-degree consequence under explicit baseline
  compatibility.

## Transfer

The query projections are domain-neutral at the residual boundary and can be
consumed by PDE finite signed-support contracts. Graph owns only the degree
projection; no route or ledger transport is implemented in this module.
