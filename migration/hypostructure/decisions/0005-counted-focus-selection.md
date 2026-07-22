# HYP-0005: Counted focused-branch selection

Status: implemented

Date: 2026-07-21

Matrix rows: `core.focus-selection-work`, `core.proof-projection`

## Missing Use Case

`Residual.Focus.run` executes the active predicate's decision procedure before
constructing either the active or inactive outcome. A downstream node could
previously report only its local payload work and claim an exact zero-check
executor even though focus selection itself had no registered work contract.
This made exact node-level accounting incomplete.

The issue is domain-independent. Graph proof chains inspect a stored branch
constructor before registering an atom or certificate; PDE row chains inspect
the same kind of accumulated branch tag before appending a represented fact.

## Ownership

Counted focus selection belongs to Core. It mentions only a predecessor-indexed
active proposition, its decision procedure, `Counted`, and a
`PolynomialCheckBudget`. It contains no graph or PDE vocabulary.

Every `Focus.Profile` now owns a counted selector, an exact polynomial
selection budget, and equality between the selector's reported checks and that
budget. Its constructor is private. Core exposes decision-generated yes/no
focuses, successor reindexing, and a proof-only always-active focus. The
ordinary proposition decider is a framework projection from the counted
selector.

## Public Author Inputs

Framework-generated decision focuses require no new application input. Their
selector performs one structural inspection of the stored decision
constructor. A node with no branch restriction may use Core's zero-check
`Focus.always`. Applications cannot construct a custom focus or attach a work
claim later at a consumer node; a new residual selector must first be expressed
as a framework decision.

## Framework Outputs

- `Focus.runCountedPayload` for selector-plus-payload work and its proof-only
  specialization `Focus.runCounted`, with routed value and checks obtained
  from the same selector evaluation.
- Equality of that exact result with `profile.selectionBudget.checks` and its
  polynomial bound.
- One-check profiles for Core's yes and no decision constructors.
- Exact budget reindexing through each focused successor.
- A proof-projection executor whose total work is focus selection plus zero
  additional proposition-inspection work.

## Residual Branches

Work accounting does not change branch semantics. `Focus.runCountedPayload`
constructs the active payload only on the selected branch and records an
inactive proof without payload otherwise. Both outcomes account for the same
selector execution; only the active outcome adds payload work. All predecessor
and sibling data remain in the literal accumulated stage.

## Both-Sides Test

Graph interpretation: the EG focused chain inherits a one-check structural
selector through every successor, including the Node 12 proof projection.

PDE/domain-neutral interpretation: `Hypostructure.Fixtures.Focus` advances a
Boolean decision twice and proves that yes selection, no selection, and the
successor focus retain the exact one-check budget. The mechanism does not
depend on Boolean semantics.

## Fixtures

- Yes and no decision-generated focuses each report exactly one check.
- A successor focus reports exactly its predecessor focus's selection count.
- The polynomial selection envelope is proved directly.
- `ProofProjection` records that selection count in its private certificate.
- Focused Graph CT1 accounts for selector plus certificate-validation work.
- Graph minimality, deletion criticality, slack-vertex independence, and
  boundaried-atom registration expose counted-first executors.
- Active/inactive outcomes and complete predecessor retention remain tested.
- Public endpoint axiom audits introduce no authored assumptions.

## Compatibility Impact

`Focus.Profile` now has a private constructor carrying a counted selector and
budget rather than a public bare `Decidable`. Existing framework-generated
profiles preserve their branch behavior. The change intentionally rejects
custom profiles that could hide selection work; callers migrate to a Core
decision or `Focus.always`. The uncounted `Focus.run` surface has been removed;
all focused executors now return a `Counted` result and may expose only its
stage projection after establishing the work contract. `Counted` and the
focused executor accept proof-valued outputs as well as data-valued outputs.
No legacy adapter or compatibility alias is introduced.
