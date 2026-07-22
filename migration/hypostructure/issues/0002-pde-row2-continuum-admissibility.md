# PDE row 2: continuum admissibility is not yet represented

Status: open

Date: 2026-07-21

Affected rows: PDE row 2 and every later row using its generator/form stage

## Authoritative requirement

`PDEs/10_continuous_extension.ipynb`, Standing Hypothesis 3.1 and Theorems
3.2-3.4, require a quasi-regular coercive closed form on an `L2` presentation,
the Beurling-Deny-LeJan local/jump/killing decomposition, a nonnegative
killing or boundary part, the sector estimate with
`E^s_1 = E^s + ||.||_2^2`, the associated right-process and capacity theory,
and the stated closed-projection behavior. The migration architecture treats
these as explicit primitive analytic contracts, not as consequences of the
framework.

## Current executable evidence

`Hypostructure.PDE.GeneratorForm` currently checks an algebraic generator
representation, symmetric/skew/boundary decomposition, sequential
closed-or-closable law, diagonal nonnegativity of the symmetric part, and a
weaker sector inequality. It now also requires a total
`RepresentedStatePresentation` into valid local equation states and derives
restriction to nested windows. The finite fixture checks those fields.

`HypostructurePDEExamples.RepresentedNS2DGeneratorFormPacket` extends the
literal row-1 ledger with a zero form, and
`RepresentedNS2DResourceBudgetPacket` extends that stage with a finite
zero-cost `Nat` resource transcript. Both are useful kernel and ledger
fixtures. Neither is a semantic continuum-admissibility theorem for
Navier-Stokes.

## Missing capability

The non-phantom equation attachment is now implemented. Before row 2 can be
an NS2D instance, the PDE layer must still represent and audit:

- the intended `L2` or Hilbert presentation and natural convergence;
- coercivity, Markovianity, and quasi-regularity;
- the strongly local, jump, and killing representation and its uniqueness;
- nonnegativity of the killing or boundary channel;
- the exact `E^s_1` sector bound and its operator consequences;
- right-process and capacity/polar availability; and
- typed absence evidence when any required primitive contract is missing.

These laws may be supplied as named author or imported contracts at the PDE
boundary, but they may not be replaced by an authored final theorem, an empty
metadata list, a degenerate topology, or a framework-generated closure claim.

## Status discipline

PDE matrix row 2 remains `kernel_checked` / `fixture_checked`, with
`ns2d_instance = not_started`. The represented packets may be listed as
fixture evidence only. Promotion to `integration_checked` requires the
remaining continuum capability, explicit `Core.Provision`/metadata records,
a literal row-1 successor, a typed missing-contract residual, and an
adversarial trust review.
