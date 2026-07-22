# HYP-0008: Represented PDE generator-state presentation

Status: implemented

Date: 2026-07-21

Matrix rows: `pde.generator-form`, PDE row 2

## Missing Use Case

The first executable `GeneratorForm M State` carried `M` only as an index.
Nothing required a form state to denote a valid state of `M.equation`, so a
downstream row could not recover the represented local equation object from
the ledger. That was too weak for both finite fixtures and the continuum
row-2 contract.

## Ownership

The attachment belongs to PDE. Core has no equations, atlas windows, or
restriction semantics. The equation model already owns valid
`EquationState`s and nested restriction, so `GeneratorForm` should reference
those existing objects rather than create another application carrier.

This decision does not move continuum admissibility into the framework. The
PDE boundary still owns the analytic contracts listed in issue 0002.

## Public Author Inputs

- One state type already carrying its additive real-module structure.
- One registered atlas window.
- A total realization of each state as a valid `EquationState` for the
  registered equation on that window.
- The existing generator, form, topology, closure, decomposition, positivity,
  and sector laws.

The caller does not provide a second equation, a copied residual, a custom
restriction operation, or a route.

## Framework Outputs

- `GeneratorForm.equationState`, recovering the represented state attached to
  any generator state.
- `GeneratorForm.restrictEquationState`, using the registered atlas and
  equation restriction on any nested window.
- Literal row-2 ledger registration retaining the complete row-1 predecessor.

## Residual Branches

This registration is not a dichotomy. A missing state presentation means the
row-2 capability cannot be constructed. Missing continuum contracts remain
the explicit row-2 residual in issue 0002 and may not be replaced by a finite
or degenerate form.

## Both-Sides Test

The neutral finite fixture presents a real scalar as the exact scalar
equation object and checks nested restriction. The represented NS2D fixture
presents every finite generator coordinate as the already validated row-1
zero equation state. Both use the same PDE API; neither claims continuum
admissibility.

## Fixtures

- Direct recovery of the finite scalar equation object.
- Recovery of the represented NS2D row-1 zero state from the row-2 form.
- Nested-window restriction through the equation model.
- Literal row-1 predecessor and root-residual retention.
- Standard trust-footprint axiom audits.

## Compatibility Impact

`statePresentation` is a new mandatory `GeneratorForm` field. All in-tree
constructors have been migrated directly; no adapter or default presentation
exists. PDE row 2 remains `kernel_checked` / `fixture_checked` and its NS2D
instance remains `not_started` until the continuum contracts in issue 0002
are represented and discharged.
