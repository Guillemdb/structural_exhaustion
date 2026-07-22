# PDE row 4: continuum quotient and defect registration

Status: open

Source: `PDEs/10_continuous_extension.ipynb`, Definition 1.1 and Definition
13.3 row 4

## Exact requirement

The continuum source registers a presented state space `X`, a represented
quotient `q : X -> Q`, the pullback `U f = f \circ q`, generators `L_X` and
`L_Q`, and the defect `E_q = L_X U - U L_Q`. Row 4 succeeds only when that
represented defect lies in the declared defect geometry. The complement is
the absence of a routed quotient certificate.

## Implemented evidence

`Hypostructure.PDE.Quotient` implements the operator-level algebra: a quotient
of the exact row-2 state carrier, a quotient generator, framework computation
of the defect, ledger registration, and exhaustive geometry containment.
`RepresentedNS2DQuotientDefectPacket` checks both branches on the finite
represented zero-state carrier and imports no analytic contract.

## Missing continuum contracts

- The presented measurable/topological spaces `X` and `Q` and represented
  point map `q : X -> Q`.
- Function or operator spaces on which the pullback `U`, `L_X`, and `L_Q` act.
- Proof that `U` is the represented pullback induced by `q` and is compatible
  with the public observable/quotient semantics.
- Domains and closedness needed to define both compositions on the intended
  continuum carrier.
- Identification of the computed operator defect with the notebook's `E_q`.
- The Navier--Stokes defect geometry and a proof of membership, or the exact
  complementary residual when membership fails.

## Promotion rule

The finite identity quotient validates API execution only. A zero generator,
zero defect, bottom carrier, or finite coordinate may not discharge any item
above. PDE row 4's `ns2d_instance` remains `not_started` until all required
continuum contracts are explicit and kernel-checked.
