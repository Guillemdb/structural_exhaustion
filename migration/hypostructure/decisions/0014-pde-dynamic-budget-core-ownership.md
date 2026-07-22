# HYP-0014: Dynamic budgets are Core-owned and reused by PDE

Status: proposed

Date: 2026-07-22

Matrix rows: `core.dynamic-budget`, `pde.budget`

## Missing Use Case

PDE rows need a residual-indexed comparison between a current quantity and an
available limit, where the quantity may be energy, flux, or another ordered
analytic size. The generic contract must live in Core so Graph and PDE can
share the same ownership and proof shape.

## Ownership

Core owns the residual-indexed quantity-versus-limit profile because the
contract is domain-neutral: it consumes only a predecessor query, an ordered
quantity, and a comparison proof. PDE owns only the thin namespace umbrella
that reexports this Core profile for analytic consumers.

## Public Author Inputs

- One residual-indexed current quantity.
- One residual-indexed limit quantity.
- One preorder on the quantity type.
- One proof that the current quantity is bounded by the limit at every
  predecessor.

## Framework Outputs

- A reusable Core dynamic-budget profile.
- Current and limit accessors.
- A pointwise `current_le_limit` theorem.
- A PDE-facing alias namespace with no additional routing or data handling.

## Residual Branches

There is no complementary branch beyond the pointwise comparison itself; the
framework does not infer a different quantity, a new route, or a problem
constant.

## Both-Sides Test

`Hypostructure.Fixtures.GraphBudget` exercises the same Core profile on a
graph-facing quantity.

`Hypostructure.Fixtures.PDEBudget` exercises the PDE-facing alias on an
energy-like real quantity.

## Fixtures

- Graph dynamic-budget fixture.
- PDE dynamic-budget fixture.
- Kernel-checked public alias theorem.

## Compatibility Impact

This adds no problem-specific constant and no routing machinery. Existing
graph consumers continue to use the Core profile, and PDE consumers can now
name the same contract from the PDE namespace.
