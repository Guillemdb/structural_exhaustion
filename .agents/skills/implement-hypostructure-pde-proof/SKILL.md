---
name: implement-hypostructure-pde-proof
description: Implement represented PDE arguments through Hypostructure's PDE layer, including local models and atlases, equations and representations, coordinates, observables, local-tail assembly, compact extraction, budgets, CT constructors, fast-track rows, Navier-Stokes registration, and explicit analytic trust boundaries. Use for PDE applications, PDE fixtures, or reusable PDE framework capabilities.
---

# Implement a Hypostructure PDE Proof

Read `references/pde-proof-work-packet.md`, `PDE_LAYER_API.md`, the relevant
Core/PDE source, `migration/hypostructure/pde-row-matrix.csv`, and the closest
finite PDE fixtures for representation and CT branch coverage completely. Do
not assume one fixture covers both concerns.

## Separate registration from theorem closure

Register the represented PDE objects before claiming analytic consequences:

1. define the `PDE.LocalModel` and `PDE.LocalAtlas`;
2. register the represented equation and representation semantics;
3. expose only public represented observables and target meaning;
4. define coordinate restriction, recentering, rescaling, or gauge paths;
5. register exact local/tail decomposition and assembly laws; and
6. add resource transcripts or compact extraction only when proved.

A Navier-Stokes model instance or fast-track signature is not a regularity
theorem. A checked registration row does not close later PDE rows.

## Check row and capability status

Verify each required row independently in the PDE matrix and against source,
fresh `.olean` evidence, and fixtures. Preserve distinct kernel and integration
statuses. Planned fast-track, compactness, budget, closed-ledger, stochastic,
or external-boundary modules are not callable. Send missing reusable work to
`$extend-hypostructure-framework` instead of adding theorem-local machinery.

## Keep continuum mathematics primitive

Supply exact analytic inputs as local semantic laws or explicitly named imported
contracts at the PDE boundary. Never encode a continuum domain as a finite
enumeration. Use finite schedules only for represented observables, windows,
profiles, channels, classes, or certificate coordinates already owned by the
incoming residual.

Reject a capability that assumes the final theorem, route closure, target
completeness, or all complementary residuals away. Record every external axiom
by exact file and declaration in the trust allowlist and a decision record;
prefer proving finite and algebraic obligations inside Lean.

## Execute through shared CTs

Select CTs by domain-independent role. Prefer live `Hypostructure.PDE.CTN`
constructors to translate represented PDE semantics into the common capability.
Use `$implement-hypostructure-ctN` for search, states, outcomes, traces,
semantics, totality, and work. Core owns coordinates, ledgers, decisions,
assembly, compact retained obstructions, and resource accounting; Routes owns
transitions.

Every negative, escaping, nontransportable, deficit, equality, or missing-control
outcome remains a typed residual with a consumer. Do not erase an analytic gap
by marking the desired branch as an author primitive.

## Validate progressively

First compile an axiom-free finite fixture that exercises every branch. Then
compile the PDE example package and the specific represented model. Run the
import firewall, trust-allowlist checks, and `#print axioms` on public endpoints.
Report completed rows, remaining residuals, external contracts, work bounds,
and the exact distinction between model registration and proved theorem scope.
