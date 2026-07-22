# HYP-0012: Focus refinement is derived from inherited finite tags

Status: proposed

Date: 2026-07-22

Matrix rows: `core.focus-refinement`, PDE rows 5 and 6

## Missing Use Case

PDE row 6 must run only on row 5's exact target-visible terminal while
retaining the complete row-5 stage. A new decision stage would replace the
literal predecessor, and a public raw refinement constructor would let an
application install an arbitrary selector and claimed work budget. The latter
would reopen the same ownership hole closed when `Residual.Focus.Profile`
received a private constructor.

The first refinement draft also defined the dynamic budget by evaluating the
complete refined selector again. The actual executor was single-pass, but
that definition made its public accounting equation tautological and obscured
the active-parent and inactive-parent schedules.

## Ownership

Core owns branch focus, inherited active queries, finite-tag inspection,
selector composition, work accounting, and the conditional ledger extension.
Graph and PDE may choose a framework-generated tag query and a fixed expected
tag. They do not own a raw predicate decider, selector trace, budget, focus,
or successor.

The abstraction is domain-neutral: the tag can be a Graph CT terminal, a PDE
fast-track terminal, or a finite neutral-fixture value. Core contains no graph
or analytic vocabulary.

## Public Author Inputs

- An existing framework-owned `Residual.Focus.Profile`.
- One `ActiveQuery` reading an exact value from that focus.
- A pure projection from that value to a finite tag.
- One fixed expected tag and its `DecidableEq` instance.

The public surface is `ActiveQuery.tagEqualTo`; `ActiveQuery.equalTo` is its
identity-projection specialization. The raw `Refinement` constructor is
private. Callers cannot provide a child decision, decision count, polynomial
budget, selected proof, or expected route.

## Framework Outputs

- A counted child equality decision costing exactly one tag inspection.
- A refined focus over the identical predecessor type.
- Parent-plus-child exact work when the parent is active, whether the child
  accepts or rejects.
- Parent-only exact work when the parent is inactive.
- An independently defined dynamic budget and a theorem equating it with the
  actual single-pass selector.
- `ActiveQuery.selectedTag`, which reads the inherited value once and returns
  it with the equality proof retained by the refined focus.
- The existing generic `narrow` and `refinementProof` queries for downstream
  proof-indexed reads.

## Residual Branches

An inactive parent remains inactive and the child comparison is skipped. An
active parent whose tag differs from the expected tag becomes an inactive
child and receives no child payload. An accepted child remains active. All
three cases retain the literal predecessor; no sibling is converted into the
selected branch.

## Both-Sides Test

`Hypostructure.Fixtures.Focus` is the domain-neutral side. It exercises an
accepted Boolean equality, a rejected Boolean equality under an active
parent, and an inactive parent. It checks the actual selector constructors,
the exact `2`, `2`, and `1` counts, a refined focused extension, inherited
query access, child-proof access, and literal predecessor retention.

`Hypostructure.Fixtures.PDERow5DirectedExhaustiveness` is the PDE side. It
selects only the target-visible row-5 terminal, proves that the positive-gap
and zero-quotient siblings are rejected by the actual selector, and retrieves
the complete target-visible payload through `selectedTag` without a second
ledger read.

Graph consumers may instantiate the same API with a framework-generated CT or
route terminal. No graph-specific constructor is required.

## Fixtures

- Accepted child and exact parent-plus-child work.
- Rejected child with an active parent and the same exact work.
- Inactive parent with no child work.
- Accepted and rejected actual selector constructors.
- Refined focused extension and literal predecessor retention.
- Complete row-5 target-visible payload equality.
- Standard axiom audit with no `sorryAx` or trust-boundary widening.

## Compatibility Impact

Any external record literal constructing `Focus.Refinement` is intentionally
rejected. Such a caller must expose a finite inherited tag and use
`tagEqualTo`, or add a separately reviewed Core decision capability if the
operation is not equality inspection. There is no compatibility facade.

The row-5 target-visible focus now uses the sealed tag API. Row 6 may consume
only that public focus and query. This decision changes no EG mathematics,
baseline theorem, or trust assumption.
