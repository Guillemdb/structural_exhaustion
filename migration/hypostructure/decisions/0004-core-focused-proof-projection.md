# HYP-0004: Core-owned focused proof projection

Status: implemented

Date: 2026-07-21

Matrix rows: `core.proof-projection`, EG node 12

## Missing Use Case

Some proof-program nodes derive one proposition entirely from facts already
available through an exact query on the active predecessor. They do not scan
new data, decide a mathematical alternative, or create a domain object. Before
this decision, an application had to define its own certificate or output,
extend the focused ledger manually, and separately claim a work bound.

EG node 12 has exactly this shape. The original proof defines target-complete
identification by equality of target response in every compatible outside
context. Node 12 records the direct universal-response consequence of the
node-11 registration. The step is a proof projection, not a finite CT3 table
search.

The same shape occurs in PDE programs when a represented row fact follows
from an already registered normalization, equation identity, or invariant
observable without inspecting another schedule.

## Ownership

The capability belongs to Core. Its public types mention only a literal
predecessor, a `Residual.Focus.Profile`, a predecessor-indexed proposition,
and an exact `Focus.ActiveQuery`. It contains no graph response, boundary,
cycle, PDE, pressure, or equation vocabulary.

Core owns the private certificate, counted focused branch execution, ledger
extension, latest queries, and composed work budget. The proof projection adds
no local inspection, while the complete executor records exactly the
selection budget already owned by the focus. A domain layer owns the theorem
used to construct the query. An application only instantiates that domain
theorem at the current residual.

## Public Author Inputs

- The literal predecessor focus.
- A proposition indexed by the literal predecessor and its active proof.
- One exact `Focus.ActiveQuery` deriving that proposition from existing
  predecessor queries.

The caller does not supply a successor output, certificate constructor, work
count, ledger extension, branch match, route, or inactive-sibling payload.

## Framework Outputs

- A private proof certificate containing the projected claim.
- A `Focus.Stage` whose predecessor is definitionally the complete incoming
  stage.
- A successor focus with payload only on the active branch.
- Typed latest-certificate and latest-claim queries.
- An exact inherited focus-selection count and Core-owned polynomial work
  proof for the complete counted execution, including inactive outcomes, with
  zero additional projection checks.
- Preservation of every predecessor query and the root residual through the
  ordinary focused extension.

## Residual Branches

This executor is not a dichotomy. On an active predecessor, Core appends the
proof certificate. On an inactive predecessor, `Focus.runCounted` records the
framework-owned inactive outcome and appends no payload. It neither discards
nor fabricates a sibling branch.

If a purported projection needs candidate inspection or a new decision, this
API does not apply; the caller must use the matching CT or decision executor.

## Both-Sides Test

Graph interpretation: EG node 12 projects
`AtomResponse.contextUniversal_of_identified` for a coordinate system indexed
by the exact atom-profile certificate read from the node-11 registration.

Domain-neutral/PDE interpretation: the `ProofProjection` fixture projects an
equality already stored in an active ledger. The same executor can append an
analytic consequence of a represented PDE row because neither its claim nor
its query is constrained by Core.

## Fixtures

- Active execution appends exactly one private certificate.
- Inactive execution emits no payload.
- Literal predecessor, root residual, and old query values are preserved.
- The latest claim is indexed by the original predecessor rather than a copied
  state.
- Certificate checks equal the focus-selection budget exactly; the fixture's
  structural selector performs one check.
- The stored certificate count is equal to the same `executeCounted` result
  whose value produced the successor stage.
- The public counted executor exposes the exact selector count and polynomial
  bound even when the predecessor is inactive and no certificate exists.
- The polynomial envelope is proved by Core.
- Public endpoint axiom audits contain no authored assumptions.
- EG node 12 kernel-checks with the standard Mathlib trust footprint only.

## Compatibility Impact

This is an additive Core API. It does not import legacy modules or alter any
existing residual representation. Applications that previously hand-built a
proof-only output can migrate to this executor without changing their
mathematical claim. Semantic parity remains a separate migration gate; a
successful kernel build alone does not imply parity or cutover.
