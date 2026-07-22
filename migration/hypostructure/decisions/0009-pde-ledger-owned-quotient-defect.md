# HYP-0009: Ledger-owned represented quotient defect

Status: implemented

Date: 2026-07-21

Matrix rows: `pde.represented-quotient`, `pde.defect-geometry`, PDE row 4

## Missing Use Case

The first executable `RepresentedQuotient` accepted a total
`Ambient -> State` map unrelated to `GeneratorForm.statePresentation`.
Row 4 could therefore compute a defect from a form supplied out of band while
its predecessor ledger contained a different row-2 form. That violated both
the represented-state contract and literal-predecessor discipline.

## Ownership

The operator quotient belongs to PDE because it uses real-module state
carriers and registered generators. Core owns the typed query, accumulated
ledger extension, and exhaustive binary decision. Applications own only the
quotient, quotient generator, and defect geometry specialized to the exact
form returned by the predecessor query.

The continuum point-space quotient `q : X -> Q`, pullback `U`, operator-domain
facts, and analytic geometry membership remain PDE-boundary obligations. The
finite operator fixture does not establish them; issue 0003 tracks that work.

## Public Author Inputs

- A quotient module for the state carrier already presented by one
  `GeneratorForm`.
- Linear projection and lift maps with `project.comp lift = id`.
- A quotient generator.
- A declared positive defect geometry.
- Decidability of exact defect containment for the executable fixture.

The row-4 executor receives a typed predecessor query for the inherited form.
The quotient and quotient generator are dependent on the exact value returned
by that query. No ambient-to-state handoff, copied form, custom ledger output,
or application-selected route is accepted.

## Framework Outputs

- The exact operator defect `L_X U - U L_Q`, computed by PDE.
- A no-copy ledger extension containing that defect.
- An exhaustive Core decision between containment in the declared geometry
  and its literal negation.
- Exact predecessor and stable-root-residual preservation theorems.

## Residual Branches

Containment is the row-4 success output. Its complement is the typed statement
that the computed defect is outside the declared geometry. Row 4 does not
silently route or close that residual; resistance and harmonic routing belong
to later notebook rows.

## Both-Sides Test

The neutral scalar fixture uses an identity quotient with matching and
mismatching quotient generators. The represented NS2D zero-state packet uses
the same generic API and one bottom carrier: the matching run computes zero
and takes the contained branch, while the mismatching run computes `-id` and
takes the complementary branch.

Both executions read the row-2 form through a query preserved across row 3.
Neither imports an analytic contract or claims a continuum NS2D quotient.

## Fixtures

- Exact `Query.latest` and `Query.preserve` retrieval of the row-2 form.
- Literal row-3 predecessor and stable root-residual retention.
- Framework-computed zero and negative-identity defects.
- Success and complementary decisions under one fixed geometry.
- Standard trust-footprint axiom audits and an empty analytic boundary.

## Compatibility Impact

`RepresentedQuotient` is now indexed by the exact `GeneratorForm` and no
longer contains `represent` or `equivalent_project`. `registerDefect` now
requires a typed form query and dependent quotient inputs. All in-tree callers
were migrated directly; no compatibility adapter exists.

PDE row 4 remains `kernel_checked` / `fixture_checked`. Its NS2D instance
remains `not_started` until issue 0003's continuum contracts are represented
and discharged.
