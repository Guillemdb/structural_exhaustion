# HYP-0011: PDE defect routing requires explicit analytic alignment

Status: accepted

Date: 2026-07-21

Matrix rows: `pde.defect-routing-raw`,
`pde.direct-resistance`, `pde.defect-routing-alignment`, PDE row 6

Continuum row-6 status: `blocked` / `not_started`

Implementation status: the generic direct-resistance contract, source-neutral
CT13-to-CT7 executor, complete raw four-by-three terminal fixture, typed
unavailable-alignment residual, strict predecessor-indexed alignment wrapper,
exact work accounting, and independent finite orthogonal and pressure-gauge
fixtures are kernel checked. The strict wrapper computes the exact defect from
predecessor queries, reads the unchanged closed ledger and quotient, derives
the three semantic conditions, and delegates tag selection, routing, focus
construction, and proof-ledger extension to the framework. The represented
NS2D packet exercises only the inactive/raw integration path. No active
continuum row-6 alignment is implemented or kernel checked.

## Decision

PDE fast-track row 6 consumes the literal target-visible output of row 5. Its
framework execution has two rigorously separated layers:

1. A total, source-neutral raw execution runs CT13 and CT7 and records their
   exact generated outputs, traces, and actual work in one framework-owned raw
   transcript.
2. A semantic collapse is permitted only when the literal predecessor
   registers an analytic alignment contract that relates the raw transcript to
   one of the source-prescribed row-6 outcomes.

The raw execution order is CT13 followed by CT7. This is an operational API
order only. It does not assert that any CT13 constructor selects, enables,
disables, or determines CT7, and it does not assign PDE meaning to any CT13 or
CT7 constructor.

The default total execution runs CT7 on every active row-5 focus after CT13.
No cited source proves that CT7 runs only after CT13 `overlap` or `deficit`, so
the generic executor must not make that optimization. A future conditional
execution rule would require its own registered predecessor-owned theorem,
typed residual coverage, counted-work proof, and decision review.

If no analytic alignment contract is registered, the exact raw transcript is
returned with a typed `unaligned` status. This is an active framework residual,
not a fourth mathematical row-6 alternative and not a successful row-6
calculation. It cannot be passed to row 7 as though semantic routing had
completed.

When an alignment contract is registered, the framework, rather than the
application, performs the finite semantic classification. The contract may
prove only source-backed relations for the exact predecessor-owned analytic
objects and the exact generated transcript. It may not provide an expected CT
terminal, a selected semantic tag, a successor, a copied output, or a route.

The source-prescribed aligned outcomes remain exactly:

1. a finite-resistance route for the routable component, with the harmonic
   component proved zero;
2. a finite-resistance route for the routable component, with the exact
   harmonic component proved to belong to the predecessor-owned closed-class
   ledger; or
3. the exact nonroutable harmonic component as a target-visible residual.

The third outcome is not target realization. Capacity, nonpolarity, and any
target-reaching conclusion remain downstream obligations.

## Audit Correction

The cited PDE sources do not prescribe any exact map from

```text
CT13: tierOne | overlap | deficit | reconciled
```

or from

```text
CT7: realization | distinction | neutrality
```

to the three semantic row-6 outcomes. They also do not prescribe a subset of
CT13 terminals on which CT7 alone should run. The former accepted draft
incorrectly froze such a map. This revision withdraws it.

No individual CT label and no CT13/CT7 label pair has row-6 semantic force
without an explicit analytic alignment theorem. The raw transcript is
deliberately a product of generic CT observations. Its interpretation is a
separate mathematical obligation.

## Source Contract

This decision is limited by the following source statements.

### Continuous-extension source

`PDEs/10_continuous_extension.ipynb` supplies the row-6 mathematics:

- Definition 6.1 defines
  `R_W(E) = ||L_W^(-1/2) P_(ker L_W)^perp E||^2`, with value infinity when
  the displayed vector is outside the represented `L2` domain.
- Theorem 6.2 gives the orthogonal split
  `E = E_rt + E_harm`, with `E_harm` the kernel projection and `E_rt` the
  orthogonal projection. It states that `E_rt` is routable exactly when its
  resistance is finite and that a nonzero harmonic component is not directly
  routable.
- Theorem 6.3 gives the minimal-energy weak compensator for a finite
  resistance route and its exact energy identity.
- Theorem 6.4 gives the defect-aligned drift bound and controls the whole
  defect by the symmetric energy only when the harmonic component vanishes.
- Definition 13.1 records effective resistance plus the harmonic residual as
  the fast-track object for defect routing.
- Definition 13.3, row 6, requires the defect and geometry as input, computes
  resistance and the harmonic residual, accepts finite resistance with the
  harmonic component closed or zero, and leaves a nonroutable
  harmonic/target-visible residual otherwise.
- Definition 11.26 and Theorem 11.27 require every closed family to be
  propagated before a later invariant is computed and forbid rechecking it on
  the next quotient.

The notebook's separate commutator-routing extension, Theorems 6.8-6.20, is
not implied by a direct row-6 resistance certificate. A degenerate direct
geometry may use a hypocoercive bracket or positive-commutator fallback only
when that represented profile and its source theorems are separately
registered. A CT13 fallback label alone proves no bracket span, gap, Mourre
estimate, or commutator sign.

### Auditable-proof source

`PDEs/llm_auditable_proof_architecture_draft.tex` requires:

- declared coordinate and theorem-input contracts before an estimate is used;
- promotion of every uncovered kernel, representative, tail, or topology term
  to a named residual;
- closure only by a matching local theorem, imported theorem, or certified
  reduction to an already closed obstruction;
- distinct accounting for active-frontier and closed-ledger obligations; and
- in the local Stokes stress test, closure of the curl/CZ-controlled part while
  the harmonic-gradient and harmonic-pressure terms remain named until a
  compatible normalization closes them.

In particular, quotient or vorticity control does not imply raw velocity or
raw pressure regularity. A raw representative closes only after the removed
kernel is proved zero or sufficiently regular in the stated local contract.

### Overall-architecture source

`PDEs/overall_proof_architecture.tex` requires that pressure reconstruction,
gauge compatibility, retained obstruction, and ancestry be produced before a
downstream closure uses them. It explicitly forbids treating pressure
convergence as automatic and separates classification from closure. This ADR
therefore does not treat a CT label or raw CT transcript as an analytic
theorem.

### API-design source

`PDE_LAYER_API.md`, row 6, names CT13 followed by CT7 and the finite
orthogonal-decomposition and pressure-gauge fixtures. That ordering fixes the
raw framework composition. It does not establish a terminal-to-terminal
semantic map. Its shorthand "finite resistance with harmonic part closed" is
interpreted only with the exact conditions of Theorems 6.2-6.4, not as a new
implication.

## Literal Predecessor

The literal input is the complete row-5 stage:

```text
PDE.FastTrack.DirectedExhaustiveness.Stage row5Profile
```

The row-6 API derives, inside the framework, a counted focus selecting only
row 5's `targetVisibleBoundary` constructor. The row-5
`positiveStructuralGap` and `zeroBoundaryQuotient` constructors are inactive
siblings. Row 6 neither reruns them nor appends replacement data to them.

The framework-owned focus exposes an active query for the exact
`TargetVisibleBoundaryOutput` stored by
`DirectedExhaustiveness.Profile.outputQuery`. The application may not inspect
the focused constructor, reconstruct the row-5 payload, or pass that payload
as a detached argument.

All row-6 laws, including the direct-resistance law, CT13 capability, CT7
capability, closed-ledger access, and optional analytic alignment, are
`Core.Residual.Focus.ActiveQuery` values on that exact focus. They are not free
proof arguments and are not reattached after execution.

The required shape is:

```text
literal row-5 stage
  -> framework-owned target-visible focus
  -> ActiveQuery reads on that exact focus
  -> one CT13 output-only counted generation
  -> one CT7 output-only counted generation
  -> framework-owned RawTranscript
  -> framework alignment scan, when a contract is registered
  -> aligned semantic outcome or typed unaligned residual
  -> one focused row-6 proof-ledger extension
```

The temporary `Core.Residual.Focus.ActiveView` is a query adapter for shared
CTs. It is never installed as an application state or replacement residual.

If live Core cannot refine an existing focus by a sealed latest terminal while
retaining the literal predecessor, that is a Core framework gap. If live Core
cannot perform the finite alignment scan described below with actual work
accounting, that is also a Core framework gap. Neither gap may be emulated by
an application decision stage, custom handoff, Boolean route flag, or copied
state.

## Staged Ownership

### Stage A: total raw execution

Core owns a total active execution that:

1. reads the exact predecessor-owned CT13 and CT7 capabilities;
2. runs `CT13.generateCounted` exactly once;
3. sequences its result with `Core.Counted.bind`;
4. runs `CT7.generateCounted` exactly once, regardless of the CT13 terminal;
5. sequences that result with `Core.Counted.bind`; and
6. constructs one sealed `RawTranscript` containing the two actual generated
   values exactly once.

The transcript reports generic observations only. It contains no PDE terminal,
closed-ledger assertion, target-visible assertion, or routing decision.

### Stage B: analytic collapse

The literal predecessor owns a typed alignment registration, retrieved through
an active query. The registration is either:

- `unavailable`, carrying the named open obligation that no analytic alignment
  has been registered; or
- `available`, carrying an `AnalyticAlignment` contract for every raw
  transcript that can be generated from that exact predecessor view.

For an unavailable registration, Core emits `unaligned raw`. It performs no
semantic classification and loses none of the raw evidence.

For an available registration, Core scans the fixed finite schedule of three
source semantic tags against the contract's decidable alignment relation. The
contract's totality and functionality laws prove that exactly one tag is
selected. Its soundness law supplies the tag-indexed analytic evidence. The
framework then emits `aligned raw tag evidence`.

The application does not call the scan, match on CT outputs, select the tag, or
construct the row-6 result. Registering a relation and proving its laws is
analytic mathematics; evaluating it, choosing the unique tag, extending the
proof ledger, and routing the result are framework operations.

### Stage C: ledger extension

Core appends exactly one row-6 generated value to the accumulated proof ledger.
That value stores the raw transcript once and an interpretation indexed by that
same transcript. The semantic evidence may refer to the transcript but may not
copy either CT output into another field.

The mathematical closed-class ledger is not extended by raw execution,
alignment, or finite resistance. A harmonic-closed outcome proves membership
in the exact predecessor-owned closed ledger. It does not manufacture a new
entry. Any genuinely new target-null class requires a separate source-backed
closure and generic ledger-propagation executor.

## Component Ownership

### Core

Core owns:

- refinement of the row-5 focus and its exact selector count;
- the literal predecessor and stable root residual;
- `ActiveQuery`, `ActiveView`, and inherited-query preservation;
- sequential `Counted.bind` composition;
- the source-neutral raw transcript container;
- the finite semantic-tag scan and its actual check count;
- aligned versus unaligned framework status;
- the single focused proof-ledger extension;
- closed-class-ledger query preservation and no-rechecking evidence; and
- inactive-sibling preservation.

### CT13

CT13 owns:

- predecessor-owned payer, obstruction, and tier-two schedules;
- first eligible primary selection;
- canonical minimum fallback selection;
- overlap search, reconciliation ledger, and demand comparison;
- its four sealed outcomes and exact trace; and
- its actual output-only check count and polynomial envelope.

No PDE meaning follows from `tierOne`, `overlap`, `deficit`, or `reconciled`
without a registered analytic alignment relation for the complete raw
transcript.

### CT7

CT7 owns:

- the predecessor-owned representative pair and exact context schedule;
- the first realization scan;
- the response-distinction scan after generic realization failure;
- its realization, distinguishing, and neutral outcomes;
- finite-to-symbolic coverage; and
- its actual output-only check count and linear envelope.

No row-6 meaning follows from CT7 realization, distinction, or neutrality in
isolation. In particular, realization is not automatically harmonic closure,
neutrality is not automatically closed-ledger membership, and distinction is
not automatically target visibility.

### PDE

The generic PDE layer owns:

- the represented direct-resistance profile;
- derivation of the routable/harmonic decomposition from the exact registered
  defect and geometry, subject to an explicit analytic contract;
- source-neutral adapters from that profile to CT13 and CT7;
- the three semantic tags and their exact evidence predicates;
- the `AnalyticAlignment` law bundle and registration type;
- preservation and typed access to the predecessor-owned closed ledger; and
- the sealed row-6 output, output query, trace, status, and work theorems.

The PDE layer does not own a universal theorem that a particular CT label has a
particular analytic meaning. Such a theorem must be registered for the exact
profile and predecessor.

### Application

An application owns only represented defect/geometry data, exact finite
schedules, primitive deciders, fixed theorem constants, and proofs of the
analytic laws for its model. A Navier-Stokes application may own a named
imported pressure, spectral, or gauge theorem under the explicit PDE trust
boundary. It owns no focus, transcript, semantic scan, route, successor,
ledger mutation, work synthesis, or output constructor.

## Public Author Inputs

Every hard law in the strict API is an `ActiveQuery` on the exact row-5
target-visible focus. A free proof value with no predecessor index is not a
valid row-6 input. The live public registration is
`PDE.FastTrack.DefectRoutingAlignment.Profile`, parameterized by the literal
row-5 profile, local model, and represented defect quotient.

Its public fields are exactly:

1. `ResistancePotential`, the potential type used by the direct route.
2. One CT13 `Spec` and `Capability` over the framework-owned active view.
3. One CT7 `Spec` and `Capability` over that same active view. It is not
   selected by, reconstructed from, or conditionally supplied after CT13.
4. `defectRegistration`, an active query for the exact inherited
   `QuotientDefectRegistration` and its `DefectGeometry`.
5. `boundaryCoordinate`, an active query used to evaluate that registration
   on row 5's exact selected boundary carrier.
6. `resistanceContract`, an active query for `DirectResistanceContract` on
   the framework-computed exact defect. The contract registers the harmonic
   projection, resistance, compensator action and energy, minimality,
   nonroutability, and drift laws. The routable and harmonic components are
   derived definitions, not row-output fields.
7. Active deciders for harmonic zero and membership in the exact current
   closed-class ledger.
8. `zeroClosed`, an active proof that literal zero belongs to that unchanged
   ledger.
9. `routingComplete`, an active `RoutingCompleteAt` theorem giving exactly
   the source trichotomy: finite resistance with harmonic zero; finite
   resistance with a nonzero harmonic already in the current ledger; or the
   exact harmonic is target-visible.

The current ledger and quotient are derived from row 5 and exposed through
framework queries; they are not caller-provided copies. The strict profile
accepts no semantic tag, raw-output table, route, successor, selected
compensator, selected component, alignment relation, or ledger mutation.

Internally, `Profile.toRaw` constructs the lower-level
`DefectRouting.AnalyticAlignment`. Its relation ignores CT constructor names
and is exactly the three source conditions above. Core proves uniqueness from
zero closure and target-visible quotient nonvanishing, scans the canonical
three-tag schedule, and attaches the corresponding evidence. For the
target-visible case, the framework derives nonzero harmonicity and exact
nonroutability from visibility, `zeroClosed`, and the resistance contract; the
application supplies no separate nonroutability witness.

If a continuum application cannot prove `RoutingCompleteAt` for the exact
predecessor-owned objects, it cannot construct the strict profile. It may use
the lower-level raw profile with `unavailable`, which returns a typed
`unaligned` residual. No assumption, default table, partial match, or finite
fixture theorem may fill that gap.

## Framework Execution

The implemented generic executor has the following exact flow.

### 1. Focus

Core evaluates the row-6 focus once. Inactive row-5 siblings stop immediately,
retain the literal row-5 stage, and receive no row-6 payload.

### 2. Raw CT13 generation

On the active row-5 target-visible branch, the executor creates one
`ActiveView`, executes `CT13.generateCounted` exactly once, and binds the actual
generated value. It does not interpret the terminal or rerun CT13 to recover a
trace, fallback, overlap, reconciliation ledger, or count.

### 3. Raw CT7 generation

The executor next executes `CT7.generateCounted` exactly once on the same
active view and binds its actual generated value. This happens for every CT13
terminal. CT7 receives only its predecessor-owned spec and capability; the
application does not build a CT7 input by matching on CT13.

The executor then seals both actual generated values in one `RawTranscript`.
No semantic branch has yet been selected.

### 4. Alignment availability

The lower-level raw framework reads the predecessor-owned alignment
registration.

- With `unavailable`, it emits the transcript-indexed `unaligned` residual.
- With `available contract`, it proceeds to the framework semantic scan.

Availability is not inferred from a CT label. The absence of an alignment is a
normal typed open status, not an exception and not permission to guess.
`DefectRoutingAlignment.Profile` never asks an application to construct this
registration: after reading `RoutingCompleteAt`, its `toRaw` adapter installs
the unique framework-derived available alignment. Thus `unaligned` remains a
real raw residual, while every constructible strict profile is aligned by
proof rather than by default.

### 5. Framework semantic scan

Core scans the fixed three-tag schedule and calls `decidableRelates` once per
visited tag. `complete` proves that the scan finds a tag; `functional` proves
that the result is unambiguous; and `sound` constructs the corresponding
semantic evidence. The scan result, trace, and actual number of relation checks
are framework outputs.

The application may not perform this scan or hand its result to the executor.
No scan clause may pattern-match on CT13 or CT7 constructors unless a
source-backed registered alignment relation proves the resulting semantic
condition. Even then, the relation is local mathematics for that profile, not
a generic row-6 mapping.

### 6. Ledger discipline

The proof ledger receives exactly one focused row-6 output. The mathematical
closed-class ledger remains the exact predecessor-owned ledger:

- the zero-harmonic aligned outcome records the route and literal zero proof
  in the proof ledger;
- the harmonic-closed aligned outcome records the route and existing
  membership proof, without extending or copying the closed ledger;
- the target-visible aligned outcome records the route evidence and retains
  the exact harmonic component as a named open residual; and
- the unaligned outcome records the exact raw transcript and missing
  alignment obligation without asserting any of those three meanings.

Row 7 may read the unchanged closed ledger and a successful aligned row-6
output through preserved queries. It may not consume `unaligned`, reconstruct
CT outputs, or manually union ledgers.

Theorems 6.2-6.4 do not say that finite resistance makes the routable component
target-null. Row 6 therefore performs no closed-class-ledger extension from
finite resistance alone.

## Exact Public Outputs

The row-6 module exposes a constructor-sealed output-only result indexed by the
active view. Conceptually:

```lean
structure RawTranscript (profile) (view) where
  private mk ::
  ct13 : CT13.Routed profile.ct13Capability view
  ct7 : CT7.Generated profile.ct7Capability view

inductive Interpretation (profile) (view)
    (raw : RawTranscript profile view)
  | unaligned (missing : MissingAnalyticAlignment profile view)
  | aligned (tag : SemanticTag)
      (evidence : AlignedEvidence profile view raw tag)

structure Generated (profile) (view) where
  private mk ::
  raw : RawTranscript profile view
  interpretation : Interpretation profile view raw
```

The live lower-level declarations implement this observable contract:

- `RawTranscript` stores each actual CT output once and makes no semantic
  assertion.
- `unaligned` is a typed active residual carrying the missing analytic
  alignment obligation. Its enclosing `Generated.raw` preserves all work and
  trace evidence.
- `aligned` is indexed by the same raw value and one framework-selected tag.
  Its evidence proves the exact source semantic condition.
- No aligned evidence stores a second CT13 output, a second CT7 output, a
  copied predecessor, or a copied closed ledger.

The public output must not duplicate the row-5 output, defect, geometry,
decomposition, current ledger, target capacity, target flux, or inherited
proofs. Those values remain in the predecessor and are recovered through
preserved active queries. Terminal-refined accessors may expose proofs indexed
by the generated interpretation; public constructors may not.

The live raw and strict modules also expose:

- `Stage`, as one `Core.Residual.Focus.Stage` over the literal row-5 stage;
- a successor focus derived by Core;
- `Profile.outputQuery`, implemented through the latest ledger entry;
- preserved queries for the existing closed ledger and exact open residual;
- `generateActiveCounted`, `payloadBudget`, and `run`; and
- literal-predecessor, root-residual, exact-work, work-bound, trace,
  raw-preservation, and no-rechecking theorems.

## Work Accounting

Work counts primitive executable inspections, not mathematical energy,
capacity, resistance, or proof terms.

The baseline executor composes actual counted computations in this order:

```text
focus selection
  + CT13 generated checks
  + CT7 generated checks
  + alignment-relation checks when alignment is available
```

The implementation discipline is:

1. Bind `CT13.generateCounted` once with `Core.Counted.bind`.
2. Bind `CT7.generateCounted` once for every active focus, independently of
   the CT13 terminal.
3. Build `RawTranscript` with `Counted.map` or `Counted.pure`.
4. For `unavailable`, package `unaligned` without a semantic scan.
5. For `available`, run a framework-owned counted first-match scan over the
   three semantic tags and retain its actual prefix count.
6. Use proof-only packaging for `complete`, `functional`, `sound`, and ledger
   inclusion proofs; these add zero checks unless their implementation invokes
   a declared executable scan.
7. Reindex the active budget to the literal row-5 predecessor and compose it
   with the exact focus-selection budget.

The mandatory branch-exact equations are:

- inactive row-5 sibling: focus selector only;
- active and unaligned: selector plus actual CT13 checks plus actual CT7
  checks;
- active and aligned: selector plus actual CT13 checks plus actual CT7 checks
  plus the actual alignment-scan prefix.

There is no CT13-label-dependent CT7 work equation in this contract. A bound
may use the sum of the CT13, CT7, and three-tag scan envelopes, but the stored
actual count must come from the composed computation.

It is forbidden to run semantic generators and then manufacture
`checks := ct13.checks + ct7.checks`, reconstruct counts from terminals, rerun
a search in a proof, or attach a worst-case count as though it were actual.
Worst-case budgets are upper bounds only.

## Residual Consumers

| Row-6 result | Status | Consumer |
|---|---|---|
| raw transcript without analytic alignment | active `unaligned` residual | a source-backed predecessor-owned alignment contract; row 7 is unavailable |
| finite resistance, exact harmonic zero | successful aligned calculation | row-7 capacity input with the preserved ledger |
| finite resistance, exact harmonic ledger membership | successful aligned calculation | row-7 capacity input with the preserved ledger |
| exact target-visible harmonic component | active semantic residual | row 7 capacity/nonpolarity, or a separately registered commutator/gauge repair profile |

A direct-resistance failure not proved to be the harmonic projection cannot
enter the last row under a harmonic name. It remains inside the unaligned raw
status, or in a more precise typed routing residual supplied by a separate
source-backed profile, until an analytic theorem identifies it.

Pressure or gauge incompatibility is likewise a typed residual. The local
Stokes source permits closure of a normalized representative and permits raw
closure only under zero-or-smooth kernel compatibility. The executor may not
erase this distinction.

## Finite Both-Sides Fixtures

All generic fixtures must be axiom-free, contain no `sorry`, and print no
`sorryAx`. They use literal predecessors and active queries, not direct
constructors for sealed outputs.

The accepted suite is implemented by
`Hypostructure.Fixtures.PDERow6DefectRoutingRaw`,
`Hypostructure.Fixtures.PDERow6FiniteOrthogonalAlignment`, and
`Hypostructure.Fixtures.PDERow6FinitePressureGaugeAlignment`. The clauses below
remain the regression contract for those modules.

Finite fixtures may register explicit toy `AnalyticAlignment` contracts. Such
contracts are fixture mathematics only. They do not define the production
row-6 map and cannot be imported as a continuum or Navier-Stokes alignment.

### Raw-transcript independence fixture

Use finite CT13 and CT7 capabilities whose outcomes can be controlled
independently. The suite must cover every CT13 terminal and every CT7 terminal,
including enough cross-pairs to establish both of the following:

- one fixed CT13 terminal can coexist with different CT7 terminals; and
- one fixed CT7 terminal can coexist with different CT13 terminals.

Prefer the complete four-by-three product when the fixture remains small. Pin
the exact selected values, traces, actual check counts, literal predecessor,
stable root residual, and unchanged closed ledger. No case may infer a
semantic tag from either label.

### Unaligned fixture

Register `unavailable` on an active row-5 focus. The fixture must prove that:

- both CTs still execute exactly once;
- the raw transcript is retained exactly;
- the result is the typed `unaligned` residual;
- no semantic terminal or closed-ledger fact can be queried from it; and
- row 7 cannot consume it through the successful-output query.

Also cover an inactive row-5 sibling, which pays only the exact focus cost and
receives no row-6 payload.

### Finite orthogonal-decomposition alignment fixture

Use a finite real inner-product space with an explicit nonnegative
self-adjoint operator having positive and kernel subspaces. Register a local
toy alignment relation proved from that finite model, not from CT constructor
names. The suite must include:

- a defect entirely in the positive subspace, with finite resistance, exact
  compensator and energy identity, and zero harmonic component;
- a defect with a nonzero harmonic component already in the predecessor
  closed ledger; and
- a defect with a nonzero target-visible harmonic component retained as the
  exact open residual.

Each case pins the framework-selected semantic tag, relation-scan prefix,
tag-indexed evidence, raw transcript identity, predecessor identity, previous
ledger identity, and actual composed work. At least two cases should reuse the
same CT-label pair while producing different semantic tags from different
finite analytic data. This prevents the fixture relation from becoming a
disguised CT lookup table.

### Pressure-gauge toy alignment fixture

Use a finite algebraic local/CZ plus harmonic/gauge decomposition. Its local
alignment contract must prove, for that toy model only, that:

- the local controlled component is closed without copying it into an
  application state;
- a zero or registered gauge component has the appropriate source semantic
  evidence;
- an exact response mismatch remains a named harmonic/gauge residual only
  when the toy analytic relation proves target visibility; and
- representative transport is retrieved from the predecessor ledger.

This fixture tests generic execution, alignment ownership, representative
compatibility, and ledger behavior. It is not evidence for a
Calderon-Zygmund estimate, local Stokes smoothing, pressure compactness,
continuum spectral theory, or Navier-Stokes regularity.

## Continuum Trust Boundary

The continuum row-6 migration status is and remains:

```text
blocked / not_started
```

No continuum `AnalyticAlignment` is established by this ADR. A kernel-checked
generic raw executor, a kernel-checked finite toy alignment, or successful
coverage of every raw CT terminal does not change that status.

The live `PDE.DefectGeometry` records a positive bounded operator or a closed
symmetric-form presentation on a represented carrier. That registration alone
does not prove all of Theorems 6.2-6.4. A continuum instance must formalize or
explicitly import, for the exact predecessor-owned objects:

- self-adjoint realization and spectral projections;
- represented domains of `L_W^(-1/2)` and `L_W^+`;
- the orthogonal routable/harmonic decomposition;
- finiteness of direct resistance on each claimed branch;
- existence and minimality of the weak compensator;
- the compensation and energy identities;
- the defect-aligned drift estimate;
- literal membership of each harmonic class claimed already closed;
- preservation of the existing ledger and its quotient semantics;
- target visibility for each residual claimed target-visible; and
- any pressure/gauge normalization and raw-representative compatibility used
  by a Navier-Stokes instance.

The continuum instance must then register an exact predecessor-owned alignment
relation and prove its decidability or represented decision procedure,
soundness, completeness, functionality, and counted-work law. If continuum
decidability is unavailable, that is itself a named analytic obstruction; a
finite schedule may not stand in for it.

Until those theorems are formal Lean proofs, they remain named local analytic
contracts under the approved PDE external boundary with source identifier,
locality, representative status, topology status, and obstruction transport.
There is no final regularity axiom and no import whose conclusion is the final
row-6 terminal.

A finite-dimensional fixture proves only finite algebra and framework
execution. It cannot establish a continuum pseudoinverse domain, closed range,
pressure estimate, compactness passage, alignment theorem, or Navier-Stokes
result.

## Forbidden Implications

The implementation must not use any of the following implications unless the
exact predecessor-owned bridge theorem is registered and contributes to the
analytic alignment evidence:

- CT13 tier one implies finite resistance;
- CT13 reconciliation implies finite resistance;
- CT13 overlap or deficit identifies the harmonic projection;
- any CT13 terminal determines whether CT7 runs or may be skipped;
- any CT13 terminal determines a row-6 semantic outcome;
- any CT7 terminal determines a row-6 semantic outcome;
- any CT13/CT7 terminal pair determines a row-6 semantic outcome;
- CT13 overlap or deficit is the only admissible input to CT7;
- a total raw CT13+CT7 transcript is already a complete analytic routing proof;
- finite CT schedule completeness implies continuum spectral completeness;
- finite resistance implies closed range of the row-5 structural gradient;
- finite resistance implies target-nullity or closed-ledger membership;
- finite resistance of `E_rt` implies finite resistance of `E` when
  `E_harm != 0`;
- CT7 realization implies target realization or harmonic closure;
- CT7 neutrality implies closed-ledger membership;
- CT7 distinction implies target visibility;
- target visibility implies positive capacity, nonpolarity, or target reach;
- target-nullity implies literal zero;
- harmonic-ledger membership implies the raw representative is smooth;
- a regularized inverse implies an exact unregularized route;
- a CT13 fallback implies bracket, hypocoercive, or Morawetz closure; or
- a finite toy alignment implies the generic or continuum alignment.

These implications are false in general, stronger than the cited PDE sources,
or obligations of another registered row.

## Forbidden Implementation Shapes

The following are rejected even if they typecheck:

- an application `match` on row 5, CT13, or CT7 to choose an executor;
- a hardcoded generic table from CT13, CT7, or their product to semantic tags;
- conditionally running CT7 only on overlap/deficit without a separately
  registered theorem and total residual/work proof;
- an application function `RawTranscript -> SemanticTag` or selected alignment
  witness in place of the framework scan;
- treating `unaligned` as success, target visibility, or permission to enter
  row 7;
- an application-defined route enum, output record, handoff, or successor;
- a copied row-5 output, CT output, or inherited fact in the row-6 payload;
- a new application state containing the predecessor plus selected CT data;
- direct application calls to `Ledger.extend`, `ClosedClassLedger.extend`, or
  manual ledger-propagation construction;
- detached payer, obstruction, context, representative, or semantic-tag lists;
- a CT7 capability built by rerunning or matching on CT13;
- an uncounted focus predicate, relation scan, or terminal inspection;
- post-hoc work counts or worst-case counts presented as actual work;
- importing a finite fixture alignment into a production or continuum profile;
- a custom PDE search, trace, route, or closure outside CT13, CT7, Core, and the
  generic PDE row-6 executor; or
- any theorem whose only justification is that the intended branch should
  close.

## Compatibility Impact

The accepted implementation adds and kernel checks:

- reusable counted finite-search hit/prefix lemmas in `Core.Finite.Search`;
- source-neutral CT13-then-CT7 composition, typed alignment availability, and
  exact semantic-prefix work in `PDE.FastTrack.DefectRouting`;
- the generic `PDE.DirectResistanceContract`, with framework-derived
  decomposition, orthogonality, and finite-compensator equivalence;
- the strict `PDE.FastTrack.DefectRoutingAlignment.Profile`, which computes the
  inherited defect, derives target-visible nonroutability, installs the
  analytic relation, and exposes framework-owned semantic-tag focuses; and
- proof-relevant declaration metadata for primitive provisions, generated
  outputs, framework searches, generic theorems, and the composed work bound.

Acceptance evidence consists of focused and full Lake builds, complete
four-by-three raw terminal coverage, explicit unavailable-alignment coverage,
all three semantic outcomes in each independent finite analytic fixture,
exact relation-prefix and total-work equations, predecessor/root and
ledger/quotient preservation theorems, `#print axioms` output containing only
Lean/Mathlib standard axioms, the production import firewall, and the focused
migration/source-authority test suite.

One metadata representation limitation remains explicit: the current
`Core.Metadata.DeclarationMetadata.focusedLedgerQueries` field has one
homogeneous result universe, so it cannot aggregate this profile's
heterogeneous typed queries without artificial lifts. The accepted metadata
therefore records their provision boundaries and derived dependencies but
leaves that homogeneous list empty. This is an audit-schema limitation, not a
logical handoff or an application-owned copy.

Acceptance of a continuum row-6 instance additionally requires a formal or
approved imported analytic alignment satisfying the continuum trust boundary
for the exact predecessor. Until then, continuum PDE row 6 remains
`blocked` / `not_started`, regardless of finite fixture or generic executor
status.
