# Structural Exhaustion PDE Layer API

Status: target architecture. This document specifies the future
`StructuralExhaustion.PDE` package; it does not claim that these Lean
declarations currently exist.

## 1. Objective

The PDE layer specializes the domain-independent Core API for local and
continuum analysis. Its first full application is the Navier-Stokes proof
architecture in `PDEs/overall_proof_architecture.tex`. Its structural endpoint
is the fast-track instantiation sheet in
`PDEs/10_continuous_extension.ipynb`.

The application-facing rule is strict:

> A PDE proof row supplies only its new analytic theorem or invariant on the
> literal predecessor residual. The framework chooses and composes coordinate
> changes, transports the retained obstruction, performs local/global
> assembly, updates the ledgers, and routes every outcome.

The PDE layer must not become a second routing framework. It gives mathematical
meaning to Core profiles and exports canonical CT executors.

## 2. Mathematical authority

The API is derived from the following sources.

### Local proof-object requirements

`PDEs/llm_auditable_proof_architecture_draft.tex` requires every local state
to retain:

- center and scale;
- nested core and working windows;
- representative and quotient status;
- compactness topology;
- input and output contracts;
- retained obstruction;
- named failure alternatives; and
- an acyclic route or reduction to closure.

Its coordinate package is

```text
Gamma(S) = (center, scale, core, work, representative,
            quotient, topology, obstruction, input contract).
```

Its local analytic capsule is

```text
C = (window, state data, input, output, obstruction, failures, audit).
```

These are framework-owned derived stages. They are not records a theorem
application fills manually.

### Navier-Stokes routing requirements

`PDEs/overall_proof_architecture.tex` requires:

- the concentration gate and Type I/Type II split;
- Seregin extraction and ordered Type I classes;
- residual ancestry and descendant heredity;
- repaired-gauge Type II representations;
- compact, rough, multibubble, cascade, scale-collapse, carrier, terminal,
  and exterior branches;
- pressure/gauge compatibility at every extraction;
- explicit source-theorem provenance; and
- pointwise local-to-global regularity assembly.

The detailed analytic statements live in `PDEs/proof_setup.tex`,
`PDEs/paperIV_residual_branch.tex`, `PDEs/type_II_regularity.tex`, and
`PDEs/ns_perelman.tex`.

### Fast-track requirements

`PDEs/10_continuous_extension.ipynb` requires:

- a represented generator/form and public observable algebra;
- resource budgets B1-B4;
- quotient defects and defect geometry;
- closed-range or boundary-defect quotients;
- effective resistance and harmonic residuals;
- capacity and target compactification;
- SCRC cost/rigidity closure;
- conservative carriers and elliptic constraint tails;
- propagated closed ledgers;
- reduced flux radius and equality saturation;
- final affordable target completeness; and
- equivalence between every explicit estimate and one registered fast-track
  normal form.

## 3. Package boundary

The target dependency direction is:

```text
StructuralExhaustion.Core
        |
        v
StructuralExhaustion.PDE
        |
        +-- equation models, such as PDE.NavierStokes
        |
        +-- explicit analytic imports under PDE.External
        |
        v
theorem applications and fast-track row instantiations
```

Core knows no PDE vocabulary. The generic PDE layer knows local equations,
windows, forms, topologies, gauges, and limits, but no Navier-Stokes constants
or branch names. `PDE.NavierStokes` supplies the equation-specific semantics.
An individual proof supplies only current-row facts.

## 4. Minimal public registration API

The author-facing PDE API is split into one model registration and optional
capabilities. A monolithic record with every possible PDE tool is forbidden.

### 4.1 Local model

```lean
structure LocalModel where
  problem : Core.Problem
  atlas : LocalAtlas problem
  equation : RepresentedEquation problem atlas
```

`LocalModel` does not contain coordinate outputs, compact limits, residual
signatures, routes, CT results, a target, or an observable family. As in Core,
the target is supplied independently:

```lean
variable (Target : M.problem.Ambient -> Prop)
```

This permits several regularity, exclusion, or rigidity targets over the same
represented equation.

`PDE.RepresentationSemantics` is a separate
`Core.SemanticEquivalence` capability. Its default is equality; equation models
may instead register equality almost everywhere, gauge equivalence, or the
represented quotient relation. A target-bearing profile includes the matching
`Core.TargetInvariant`. Applications never transport a target theorem between
representatives manually.

### 4.2 Local atlas

```lean
structure LocalAtlas (P : Core.Problem) where
  Point : Type uPoint
  Window : Type uWindow
  contains : Point -> Window -> Prop
  nested : Window -> Window -> Prop
  core : Window -> Window
  LocalObject : Window -> Type uLocal
  restrict : P.Ambient -> (W : Window) -> LocalObject W
  core_nested : forall W, nested (core W) W
```

The atlas supplies local semantics. Core owns repeated restriction, nested
transport, and pointwise assembly. A global theorem registers an independent
`PDE.CoveringProfile` giving a residual-owned window at every relevant point;
a purely local theorem does not need a global covering field.

### 4.3 Represented equation

```lean
structure RepresentedEquation (P : Core.Problem) (A : LocalAtlas P) where
  EquationData : (W : A.Window) -> A.LocalObject W -> Type uEq
  satisfies : ... -> Prop
  restrictEquation : ...
```

Generator/form, conservative, elliptic-constraint, stochastic, or other
structure enters through separate capabilities. A bare local theorem need not
pretend to have all of them.

### 4.4 Public observables

```lean
structure ObservableInterface (P : Core.Problem) (A : LocalAtlas P) where
  Index : Type uIndex
  Value : Index -> Type uValue
  observe : (G : P.Ambient) -> (index : Index) -> Value index
  localReflect : ...
```

The family may be finite, pointwise, or analytically indexed. A CT requiring
finite execution receives an explicit residual-owned finite subfamily. Core
never enumerates all points, scales, functions, or measurable sets.

## 5. Coordinate primitives registered once

The generic PDE layer exports a coordinate-generator vocabulary:

```text
restrict | recenter | rescale | normalize | quotient | extract
```

An equation model supplies the primitive formulas and laws once through
`PDE.CoordinateModel`. It does not expose them at every theorem node.
Each local coordinate object has a framework-registered realization in the
ambient problem, as required by `Core.CoordinateSystem.realize`.

### 5.1 Required semantics

For each supported primitive, the equation model proves the target-independent
laws:

- source and target local windows;
- transformed local object and equation;
- representative and quotient transformation;
- topology transformation; and
- baseline preservation.

Separate, optional profiles prove the laws that depend on the active theorem:

- target-response naturality;
- retained-obstruction transport; and
- progress or routing-rank effect.

### 5.2 Core-derived operations

Core then derives:

- arbitrary coordinate paths and their execution;
- restriction followed by recentering and rescaling;
- gauge updates after a frame change;
- quotient projection after normalization;
- extraction in the topology registered by the current ledger;
- transport of every inherited fact and obstruction; and
- exact return to physical variables when a closure requires it.

A Navier-Stokes node therefore cannot manually build a rescaled velocity,
pressure gauge, repaired chart, or extracted profile output. It provides only
the parameters and semantic theorem attached to the incoming residual; the
canonical PDE executor obtains the corresponding coordinate action.

## 6. PDE decomposition and assembly profiles

### 6.1 Local/tail decomposition

`PDE.LocalTailAssembly` instantiates `Core.AtomContextAssembly` over the active
PDE representation semantics:

```text
local field + complementary tail = original represented field.
```

Its primitive API is only:

- localizer or cutoff;
- local response constructor;
- tail constructor;
- compatibility predicate; and
- exact reconstruction theorem.

The framework derives registration of both components, routing of an
uncontrolled tail, and recombination after both branches close.

### 6.2 Elliptic constraint tail

`PDE.EllipticConstraintTail` adds:

- the local elliptic inverse;
- proof that the tail is homogeneous on the core;
- a represented dyadic exterior schedule;
- low and decaying homogeneous modes;
- a gauge action on low modes; and
- semantic estimates for dyadic decay.

The framework computes the dyadic aggregate, gauge image, cokernel rank,
homogeneous-tail quotient, and exact residual route. The application does not
construct `p_local`, `p_tail`, the quotient, or the fallback branch by hand.

For Navier-Stokes this is the localized Calderon-Zygmund pressure plus harmonic
pressure tail, with pressure understood modulo functions of time or the active
repaired-gauge freedom.

### 6.3 Pointwise local-to-global assembly

`PDE.LocalClosureAssembly` consumes a framework-owned local closure at every
point and uses the atlas cover to derive the global statement. It is pointwise;
it does not synthesize a finite enumeration of the domain. The application
provides the local conclusion and its locality theorem only.

## 7. Compactness and profile extraction

`PDE.CompactExtraction` specializes the Core compactness profile with:

- an explicit local topology;
- a subsequence/extraction theorem;
- equation stability in that topology;
- representative and gauge stability;
- nonlinear-passage hypotheses;
- retained-obstruction persistence; and
- a descendant-realization theorem linking the limit to its ancestor.

The framework owns selection of the extraction stage and the descendant
residual. It may close the ancestor through the limit only after the
obstruction-persistence theorem is in the ledger.

Compactness failure is not an exception. It is classified by CT10 into exact
residual signatures such as missing topology, pressure compactness, diffuse
loss, exterior escape, multiple profiles, or scale instability.

## 8. Continuum fast-track registration

The full fast track accumulates the smallest primitive capabilities from which
the notebook invariants can be derived. In particular, row 4 reads the
generator/form already installed at row 2; it does not accept a second copy:

```lean
variable (formQuery : Core.Residual.Query Previous
  (fun _ => GeneratorForm M State))
variable (quotient : (previous : Previous) ->
  RepresentedQuotient (formQuery.read previous) Quotient)
variable (quotientGenerator : (previous : Previous) ->
  QuotientGenerator (formQuery.read previous) (quotient previous))

def row4 := PDE.registerDefect formQuery quotient quotientGenerator previous
```

The author does **not** provide:

- the quotient defect `E_q`; the framework computes `L_X U - U L_Q`;
- effective resistance or the harmonic projection as a hand-built split;
- a capacity verdict;
- a boundary, tail, or saturation quotient;
- a propagated closed ledger;
- a reduced profile space;
- a selected fast-track branch; or
- the final target-completeness verdict.

Those are framework outputs from optional row certificates.

## 9. Optional PDE capabilities

The PDE layer exposes small independent profiles.

| Capability | Author primitives | Framework-derived result |
|---|---|---|
| `GeneratorForm` | represented state presentation, domain, generator/form data, topology, closure, sector and decomposition laws | equation-attached generator/form stage with restriction to nested windows |
| `RepresentedQuotient` | projection and lift on the exact inherited form-state carrier, quotient generator | exact `L_X U - U L_Q` defect registered in the complete predecessor ledger |
| `DefectGeometry` | positive form/operator and domain facts | routable/harmonic split and resistance residual |
| `TargetCompactification` | affordable windows, shells, restrictions, flux reflection | escaping/in-window split and zero-flux residual ledger |
| `CapacityProfile` | affordable potentials and energy comparison | zero-capacity closure or positive-capacity residual |
| `SCRCProfile` | threshold, cost density, carrier identity, rigidity theorem | rigid/cost quotient and closure decision |
| `ConservativeCarrier` | divergence form, carrier identity, uniform remainder estimates | propagated carrier ledger and reduced sign input |
| `EllipticConstraintTail` | local inverse, homogeneous tail, dyadic bounds, gauge map | tail quotient, aggregation, and cokernel route |
| `FluxRadius` | descended loss and positive flux forms | strict, feeding, or equality decision |
| `SaturationProfile` | equality defects and saturation identities | saturation remainder and target-visible quotient |
| `RigidityProfile` | Liouville, Pohozaev, Noether, virial, or separator theorem | equality-quotient closure or exact residual |
| `CompactExtraction` | compactness and obstruction-persistence theorems | extracted descendant stage |
| `ProfileFamily` | residual-owned profiles, decoupling and mass laws | multibubble, cascade, peeling, and hidden-mass outcomes |

### 9.1 Generator-state attachment and analytic boundary

Every `GeneratorForm M State` must include a
`RepresentedStatePresentation M State`: one registered atlas window and a
total map sending each form state to a valid `EquationState` for `M.equation`
on that window. The PDE layer derives restriction of those states to every
nested window. This prevents the equation parameter from being phantom and
lets downstream rows query the exact represented equation state from the
ledger.

This attachment is semantic, not analytic. The current executable capability
does not derive an `L2` presentation, coercivity, Markovianity,
quasi-regularity, a Beurling-Deny-LeJan decomposition, nonnegative killing,
the exact `E^s_1` sector estimate, a right process, or capacity/polar theory.
Those are named PDE-boundary contracts required by the authoritative row-2
source before a Navier-Stokes instance can advance beyond fixture status. A
finite or zero-form packet may test registration and ledger preservation, but
it cannot discharge any of those contracts by degeneracy.

### 9.2 Quotient source and continuum boundary

`RepresentedQuotient form Quotient` is indexed by the complete inherited
`GeneratorForm`, not merely by a free state type. Its source carrier is
therefore exactly the represented row-2 state carrier. The row-4 executor
obtains that form only through a typed query preserved across row 3, computes
the intertwining defect, extends the ledger, and invokes Core's exhaustive
geometry decision.

This operator-level capability is the minimal executable algebra. It does not
by itself construct the continuum point map `q : X -> Q`, prove that `U` is
pullback along `q`, establish operator domains, or prove membership in a
Navier--Stokes defect geometry. Those obligations are explicit in issue 0003.
A finite identity-quotient packet is fixture evidence only and cannot promote
the continuum NS2D row.

### 9.3 Structural gradient and directed exhaustiveness

`StructuralGradient Potential Current` is a closed, densely defined
Mathlib `LinearPMap` between real Hilbert spaces. Its domain, range, and
kernel are the exact operator objects used by the row-5 source. A
`PositiveStructuralGap` contains a literal `gamma > 0` and the Poincare
inequality on `D(G) intersect (ker G)^perp`; it is not a finite-rank tag.

The pinned Mathlib release does not package the unbounded closed-range
criterion in the form required by Theorem 4.3. The model therefore registers
that analytic theorem as `ClosedRangeCriterion`. Given a genuine gap, the PDE
layer derives `ClosedRangeCertificate` and then constructs the orthogonal
represented/residual decomposition as a sealed
`DirectedExhaustivenessCertificate`. An application cannot provide the
projection outputs, and CT15 full rank alone cannot trigger this derivation.

The complementary route uses `Core.NormalForm.ClassClosure`. Its finite
exhaustive miss only proves invisibility of the registered family. Literal
vanishing of the whole quotient requires the separate
`ClassClosure.TargetComplete` law, which says that every nonnull quotient
class has a target-visible representative in that exact family. Core proves
`AvoidsTargetVisible` if and only if `BoundaryZero` under this law and only
then exposes zero-quotient propagation as row-5 closure.

CT16 is an independent compactification-code audit. Its support scan, closed
code computation, and equality comparison are counted operations with exact
budgets. The row-5 profile must prove that proper support is impossible and
that CT16 exact/mismatch terminals agree with class-closure zero/visible
terminals. CT16 does not recompute the class-closure scan and its code equality
has no quotient meaning without those bridge laws.

## 10. Fast-track rows and framework execution

Rows 1-4 are registration stages. They add certified capabilities to the proof
ledger but do not invent fake CT executions. Rows 5-18 use the CT machinery
shown below. A row may use a short CT chain because classification, accounting,
and terminal validation are distinct operations.

| Notebook row | Framework execution | Success output | Complementary residual |
|---|---|---|---|
| 1. Legal signature | Core certification node | registered local model | missing primitive contract |
| 2. Generator/form | Core certification node | generator/form stage | missing closability or sector evidence |
| 3. Budget | Core certification node | B1-B4 resource budget | nontransportable affordability |
| 4. Quotient defect | Core derived stage | computed represented defect | defect outside declared geometry |
| 5. Directed exhaustiveness | CT15 then CT16 and Core class closure | positive gap/closed range or target-complete zero boundary quotient | in-window target-visible positive-capacity nonzero-flux boundary defect |
| 6. Routing | CT13 then CT7 | finite resistance with harmonic part closed | nonroutable harmonic residual |
| 7. Capacity | CT14/CT1 | zero-capacity target exclusion | positive-capacity target witness |
| 8. Committor/operator | CT3 then CT7 | response-complete quotient | projection or residual obstruction |
| 9. Scale reaching | CT17 then CT12/CT11 | positive per-scale gap and finite-budget contradiction | zero-cost or moving-scale residual |
| 10. SCRC/boundary repair | CT10 then CT11/CT14/CT1 | boundary quotient closed | in-window rigid/cost residual |
| 11. Conservative carrier | CT5 then CT14/CT11 | carrier remainders ledgered | target-visible carrier remainder |
| 12. Constraint tail | CT3 then CT14/CT15/CT13 | tail quotient closed | dyadic, gauge-cokernel, or tail residual |
| 13. Ledger propagation | Core propagation executor | reduced quotient-compatible carrier | non-descending later invariant |
| 14. Flux sign | CT10 sign classifier then CT11/CT1 | strict draining margin | feeding profile or equality residual |
| 15. Borderline equality | CT14 then CT16/CT10 | zero saturation quotient | target-visible saturated class |
| 16. Rigidity/separator | CT7 then CT16/CT1 | equality quotient closed | equality-rigidity residual |
| 17. Stochastic lift | stochastic lifting executor over the same CT profiles | pathwise or annealed capacity/radius closure | stochastic target-visible quotient or missing martingale control |
| 17b. Expectation gauge/algebra | CT3 then CT13/CT15/CT14 | annealed gauge closure with the quenched leak routed or zero-capacity | target-visible positive-capacity fluctuation quotient |
| 18. Target completeness | CT16 then CT1 | final exclusion/regularity target | named in-window target-reaching class |

Every edge consumes the complete predecessor ledger. No PDE application may
invoke a bare route transition or construct the target CT input.

## 11. CT1-CT17 in the Navier-Stokes architecture

All CTs have a natural responsibility in the complete proof, even when only a
subset appears in the shortest conservative fast-track chain.

| CT | Navier-Stokes responsibility |
|---|---|
| CT1 | Validate epsilon-regularity, Liouville, capacity, rigidity, and final local-regularity targets |
| CT2 | Perform strict profile reduction, local replacement, or reduction to a lower-rank previously closed obstruction |
| CT3 | Compare local pressure/tail, gauge, quotient, and compatible-context responses |
| CT4 | Assign error demands or retained mass to windows, profiles, carriers, and capacity accounts |
| CT5 | Aggregate local concentration, energy, pressure, flux, and carrier contributions |
| CT6 | Select the first failed ordered Type I, residual, Type II, or fast-track row |
| CT7 | Produce a distinguishing tail, gauge, topology, target shell, or exact neutral context |
| CT8 | Handle recurrent hull states, repeated scale types, descendant recurrence, and removable repeated responses |
| CT9 | Detect multibubble/profile overload against finite mass or capacity |
| CT10 | Classify concentration, Type I/II, compactness defects, terminal classes, and fast-track normal forms |
| CT11 | Localize integrated error, dissipation, scale drift, or carrier failure to a supplied window/channel |
| CT12 | Peel profiles, bubbles, dyadic shells, scales, and descendant schedules with a well-founded measure |
| CT13 | Route primary/fallback resources: routable/harmonic, local/tail, gauge/decay/cokernel, or J1/J6/J7 |
| CT14 | Prove profile mass decoupling, hidden-mass exhaustion, dyadic summability, and aggregate capacity bounds |
| CT15 | Compute gauge cokernel, bracket/quotient rank, closed-range deficit, and target-relative active rank |
| CT16 | Audit whole compactified support, terminal-state completeness, saturation type, and final quotient code |
| CT17 | Execute bounded scale, shell, modulation, survivor, and target-thickening arithmetic |

## 12. Navier-Stokes model instance

The Navier-Stokes model registers the following once.

### Ambient and target

- Ambient object: suitable weak solution data with domain and time interval.
- Baseline: distributional equation, divergence-free condition, local energy
  inequality, pressure integrability, and declared source hypotheses.
- Target: local regularity at a candidate point, assembled pointwise into the
  global regularity conclusion.
- Retained obstruction: positive scale-invariant velocity or CKN
  concentration at the candidate singular point.

### Local atlas and coordinates

- Windows: backward parabolic cylinders with core/work nesting.
- Restriction: solution and pressure data restricted to a cylinder.
- Recenter: translate the selected concentration point or active profile.
- Rescale: parabolic Navier-Stokes scaling.
- Normalize: subtract pressure means or apply the repaired gauge.
- Quotient: pressure modulo time functions, harmonic modes, gauge directions,
  or already closed profile classes.
- Extract: local compactness, Seregin extraction, profile decomposition,
  terminal profile extraction, or hull limit in its registered topology.

### Observables and budgets

- scale-invariant `A`, `C`, `D`, and dissipation quantities;
- local velocity and pressure concentration;
- active-core and profile masses;
- modulation, scale-drift, carrier, and error-channel observables;
- energy, dissipation, capacity, and log-scale cost budgets.

### Decomposition profiles

- local pressure/CZ contribution plus harmonic tail;
- compact core plus diffuse or exterior context;
- profile family plus perturbative remainder;
- symmetric loss plus boundary flux and constraint remainder;
- equality defects plus saturation remainder.

The branch-specific papers supply semantic theorems for these primitives. The
framework constructs the route states and preserves ancestry.

## 13. Explicit analytic import boundary

Core and the generic PDE layer remain axiom-free. Analytic results not yet
formalized in Lean live under explicit equation-specific namespaces such as:

```text
StructuralExhaustion.PDE.External.NavierStokes.CKN
StructuralExhaustion.PDE.External.NavierStokes.LocalCompactness
StructuralExhaustion.PDE.External.NavierStokes.PressureCZ
StructuralExhaustion.PDE.External.NavierStokes.Liouville
```

Each imported contract records:

```lean
structure ImportedAnalyticContract where
  sourceId : String
  Input : Type u
  Output : Input -> Prop
  proof : forall input, Output input
  locality : forall input, LocalityStatement input
  representativeStatus : forall input, RepresentativeStatement input
  topologyStatus : forall input, TopologyStatement input
  obstructionTransport : forall input, ObstructionStatement input
```

The actual theorem or allowlisted axiom is declared only in `PDE.External`.
Replacing an import with a formal Lean proof does not change any CT, capsule,
or application API.

No final regularity axiom is allowed. Imports must be local mathematical rows
such as epsilon-regularity, compactness, pressure decomposition, div-curl,
profile stability, or a named Liouville theorem.

## 14. Internal capsule derivation

From the incoming residual, registered coordinate model, and one analytic
contract, the PDE framework derives the manuscript capsule fields:

| Capsule field | Owner |
|---|---|
| local window and scale | coordinate path from the predecessor residual |
| representative, quotient, topology | accumulated ledger queries |
| input contract | exact hypotheses required by the analytic theorem |
| output contract | theorem conclusion |
| retained obstruction | Core obstruction transport |
| failure routes | CT residual registry |
| audit checklist | canonical profile and source metadata |
| closure status | framework terminal/reduction checker |

An application never authors a capsule record or a failure-route list.

## 15. Failure semantics

The PDE layer treats the following as typed residuals rather than exceptions:

- no admissible core/work window;
- center or scale instability;
- unavailable representative or quotient;
- topology too weak for the requested passage;
- pressure or gauge incompatibility;
- compactness defect, diffuse loss, or exterior escape;
- nonroutable harmonic component;
- nonzero gauge cokernel;
- zero cost gap or feeding flux;
- nonzero boundary, tail, saturation, or equality quotient; and
- an imported theorem whose exact input contract is absent.

Each residual has a registered CT consumer or remains an explicit active
frontier. None may be converted into a stronger assumption.

## 16. Thin application criterion

A compliant Navier-Stokes row has the following conceptual shape:

```lean
noncomputable def pressureTailNode :=
  PDE.EllipticConstraintTail.advance previousResidual
    localInverseCertificate
    homogeneousTailCertificate
    dyadicEstimateCertificate
    gaugeActionCertificate
```

The application does not mention the selected window, composed coordinate
change, pressure split object, tail quotient, residual constructor, ledger
extension, route, or successor state. Those are PDE/Core outputs.

The full proof is complete when every required fast-track row is represented
by such a thin instantiation, every complementary residual has a consumer, and
the final target-completeness executor returns local regularity at every point.
