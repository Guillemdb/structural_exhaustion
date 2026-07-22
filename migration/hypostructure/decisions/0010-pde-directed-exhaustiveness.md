# HYP-0010: Directed exhaustiveness keeps analytic and finite audits distinct

Status: accepted

Date: 2026-07-21

Matrix rows: `pde.structural-gradient`, `core.class-closure`, PDE row 5

## Missing Use Case

The row-5 plan named CT15, CT16, and class closure without an executable law
relating their terminals. CT15 full rank is only rank on one finite scheduled
family; it does not imply a spectral gap for a closed densely defined
operator. CT16 exact-code equality is independent of target visibility unless
the profile proves otherwise. Finally, an exhaustive miss in a finite class
family does not imply that every class of the ambient quotient is null unless
that family is target-complete.

Treating any of those implications as definitional would strengthen
Theorems 4.2--4.7 of `PDEs/10_continuous_extension.ipynb` and make the finite
fixture appear to prove a continuum theorem.

## Ownership

PDE owns the represented structural-gradient operator and the analytic
closed-range criterion. Core owns focused execution, counted CT generation,
finite class search, target-completeness checking, quotient propagation, and
the final exhaustive route. An application owns only represented operators,
finite schedules, primitive deciders, and the explicit analytic and semantic
bridge theorems for its model.

The generic PDE layer may derive a directed orthogonal decomposition from a
closed-range certificate. It may not accept a decomposition as application
output or derive closed range from finite rank alone.

## Public Author Inputs

- A closed densely defined real-Hilbert structural-gradient operator `G`.
- A genuine positive `gamma` and Poincare inequality on
  `D(G) intersect (ker G)^perp`, or the exact complementary rank audit.
- The analytic closed-range criterion for that operator.
- CT15 finite rank data and an explicit theorem taking either full-rank
  terminal to the genuine positive-gap certificate.
- An independent CT16 compactification code, including counted code
  computation and an exact work budget.
- A class-closure profile, quotient extension registration, and
  `ClassClosure.TargetComplete` proof.
- Laws aligning CT16 exact code with whole-quotient zero and CT16 mismatch
  with a target-visible class; proper support must be proved impossible when
  the row uses only the exact/mismatch audit.
- A semantic theorem that every target-visible boundary class is in-window,
  has positive target capacity, and has nonzero certified target flux.

Realization or nonpolarity of a positive-capacity class is not a row-5 input;
it remains a later target-realization obligation.

## Framework Outputs

- A positive structural-gap terminal carrying framework-derived closed range
  and directed exhaustiveness.
- A zero-boundary-quotient terminal carrying the generated closed-ledger
  propagation and literal `BoundaryZero` proof.
- An exact target-visible boundary residual carrying the first represented
  class, nonnull quotient proof, and its in-window/capacity/flux semantics.
- One focused extension of the literal row-4 predecessor, with the inactive
  geometry sibling unchanged.
- Exact branch-sensitive work equal to focus selection plus the CT15, CT16,
  and class-closure computations actually executed.

## Residual Branches

CT15 rank drop is only a route into the compactified quotient audit. It is not
itself a no-gap theorem. CT16 proper support remains a typed residual unless a
registered row-5 law excludes it. A nonzero target-visible boundary quotient
remains open until a later realization/nonpolarity certificate turns it into
a target-reaching path.

## Both-Sides Test

Finite fixtures must exercise at least:

- an identity structural gradient with a directly proved positive gap;
- a target-complete one-class quotient whose exhaustive miss proves literal
  quotient zero and installs propagation; and
- a nonnull represented quotient class whose CT16 mismatch agrees with the
  class-closure target-visible terminal.

Every finite-dimensional range is closed, so the quotient fixtures test
routing and ledger semantics. They are not examples of a genuinely
nonclosed finite-dimensional range.

## Compatibility Impact

`ClassClosure` now separates finite-family avoidance from
`TargetComplete` and exposes `BoundaryZero` only from both. CT16 work
accounting must count its code computation explicitly and reuse one support
scan. The row-5 executor will use the counted output-only CT15, CT16, and class
closure generators; planned route-registry metadata alone is insufficient.

The combined executor and all three finite terminals compile with their exact
work equations. The represented NS2D packet checks finite routing and ledger
integration only; continuum closed range and target realization remain
explicitly unimplemented analytic obligations.
