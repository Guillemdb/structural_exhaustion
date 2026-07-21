# Domain-Independent Structural Exhaustion Core API

Status: target architecture. Names in proposed Lean signatures are design
names, not declarations claimed to exist in the current library.

## 1. Purpose and authority

The Core API must support graph proofs and local PDE proofs without containing
graph, measure, topology, pressure, or equation-specific vocabulary. A theorem
application supplies only irreducible mathematical primitives and proofs about
its literal incoming residual. Core owns all state transport, coordinate-path
composition, local assembly, decisions, ledger updates, routing, and closure.

This design is informed by:

- `lean/StructuralExhaustion/Core/Problem.lean`, `Context.lean`,
  `ResidualRefinement.lean`, and `CTTransition.lean`;
- `framework/branch_closure_methodology_extended.tex`;
- `PDEs/llm_auditable_proof_architecture_draft.tex`, especially its coordinate
  package, residual-promotion, analytic-capsule, and obstruction-reduction
  contracts;
- `PDEs/overall_proof_architecture.tex`, especially its complete exit ledger
  and per-node capsule contracts; and
- `PDEs/10_continuous_extension.ipynb`, especially Definitions 11.26, 11.29,
  13.1, 13.3, and 13.5 and Theorems 11.27, 11.30, 13.2, 13.4, and 13.7.

The notebook adds one decisive requirement. A successful structural row must
be propagated into a closed mathematical ledger before the next invariant is
computed. Later checks run on the quotient by all previously closed classes;
they never re-estimate those classes.

## 2. Non-negotiable invariants

The target Core enforces the following invariants by type and executor design.

1. **One literal residual.** Every node consumes the residual emitted by its
   predecessor. It cannot manufacture a replacement carrier for convenience.
2. **One accumulated proof ledger.** Every proved property and data-bearing
   stage remains available through a typed query. Applications never copy an
   earlier output into a new record.
3. **Framework-owned coordinate paths.** Restriction, recentering, rescaling,
   normalization, quotienting, relabeling, and similar changes are primitive
   domain actions composed and executed by Core.
4. **Framework-owned assembly.** Applications prove decomposition and
   reconstruction laws. Core performs gluing, replacement, local/tail
   recombination, and pointwise local-to-global assembly.
5. **Framework-owned routing.** A CT executor decides or consumes a certified
   alternative, transports untouched siblings, extends the ledger, and returns
   the exact successor residual.
6. **No untyped remainder.** Every nonterminal result is a named residual with
   a registered consumer.
7. **No caller-authored outcome.** Applications provide semantic evidence,
   never a selected CT terminal, route, closure status, or target result.
8. **No rechecking.** A class placed in a propagated closed-class ledger is
   absent from every later quotient-compatible invariant.
9. **Explicit trust boundary.** Imported mathematics is exposed as named
   theorem contracts. Core itself introduces no domain axiom.

## 3. The irreducible problem kernel

The current `Core.Problem` contains `Ambient`, `Baseline`, `rank`, and
`BranchState`. The clean target separates optional progress from the truly
universal problem data:

```lean
structure Problem where
  Ambient : Type u
  Baseline : Ambient -> Prop
  BranchState : Ambient -> Type v

variable (Target : P.Ambient -> Prop)

structure Progress (P : Problem) where
  Measure : Type w
  lt : Measure -> Measure -> Prop
  wellFounded : WellFounded lt
  measure : P.Ambient -> Measure
```

`Target` remains external because one ambient problem may support several
target predicates. `Progress` is optional because finite classification,
charging, and direct target certification do not require minimality. A graph
profile may use a lexicographic size measure; a PDE profile may use scale,
defect rank, number of active profiles, or a routing ordinal.

Literal equality is not the correct reconstruction notion for every domain.
An optional representation capability supplies the semantic equivalence used
by coordinates and assembly:

```lean
structure SemanticEquivalence (P : Problem) where
  equivalent : P.Ambient -> P.Ambient -> Prop
  equivalence : Equivalence equivalent
  baseline_iff : equivalent G H -> (P.Baseline G <-> P.Baseline H)

structure TargetInvariant (E : SemanticEquivalence P)
    (Target : P.Ambient -> Prop) where
  target_iff : E.equivalent G H -> (Target G <-> Target H)
```

The default instance is equality. Graph uses graph isomorphism. PDE models may
use equality almost everywhere, gauge equivalence, or a represented quotient
relation. The domain layer registers this semantics once. Core performs all
subsequent transport, including branch-state transport supplied by the active
coordinate capability.

The existing context hierarchy remains the model:

- `BranchContext P` owns an ambient object, baseline proof, and branch state;
- `AvoidingContext P Target` adds target avoidance;
- `MinimalCounterexampleContext P Target` adds a well-founded smaller-object
  theorem when a `Progress` profile is present.

The residual is deliberately not a field of `Problem`. Each proof program
chooses its stable residual carrier, and `ResidualRefinement.State` stores that
literal carrier with its accumulated facts.

## 4. Two ledgers with different jobs

The word ledger denotes two independent structures. They must not be merged.

### 4.1 Proof ledger

The proof ledger is the existing dependent list of propositions and stages
about one residual:

```lean
State Residual facts
Node property
StageNode Stage
LedgerQuery facts Wanted
```

It answers questions such as "which pressure normalization was proved?" or
"which finite classification stage is available?" Core owns extension,
lookup, predecessor retention, focused decisions, and sibling transport.

### 4.2 Closed-class ledger

The closed-class ledger is mathematical data used by quotient-based proofs.
It records classes already proved target-null, residual-zero, gauge, exact,
subthreshold, rigidly excluded, capacity-zero, or otherwise closed:

```lean
structure ClosureOperator (Carrier : Type u) where
  close : Set Carrier -> Set Carrier
  extensive : forall S, Set.Subset S (close S)
  monotone : forall {S T}, Set.Subset S T -> Set.Subset (close S) (close T)
  idempotent : forall S, close (close S) = close S

structure ClosedClassLedger {Carrier : Type u} (C : ClosureOperator Carrier)
    (TargetNull : Carrier -> Prop) where
  classes : Set Carrier
  closed : C.close classes = classes
  targetNull : forall x, classes x -> TargetNull x
```

A finite graph profile may use identity or finite-equivalence closure. A PDE
profile may use topological, linear-span, submodule, cone, or
compactified-profile closure. Core therefore exposes an abstract closure
operation, not `IsClosed` or one fixed analytic representation.

Quotient formation is a separate semantic capability:

```lean
structure LedgerQuotient {Carrier : Type u} {C : ClosureOperator Carrier}
    {TargetNull : Carrier -> Prop} (L : ClosedClassLedger C TargetNull) where
  Quotient : Type v
  project : Carrier -> Quotient
  killsClosed : ...
  universal : ...
```

The domain layer proves this universal property once for its closure model.
The theorem application never supplies a quotient or a reduced carrier.

A propagation profile provides a represented transport from one carrier to the
next and proves that later observables descend through the enlarged ledger:

```lean
structure LedgerPropagation {Carrier : Type u}
    {C : ClosureOperator Carrier} {TargetNull : Carrier -> Prop}
    (L : ClosedClassLedger C TargetNull) where
  NextCarrier : Type v
  nextClosure : ClosureOperator NextCarrier
  nextTargetNull : NextCarrier -> Prop
  transport : Carrier -> NextCarrier
  nextClosed : ClosedClassLedger nextClosure nextTargetNull
  nextQuotient : LedgerQuotient nextClosed
  includesTransport : forall x, L.classes x ->
    nextClosed.classes (transport x)
  quotientCompatible : LaterInvariantDescends nextClosed
```

Core invokes the registered quotient, derives its canonical projection,
iterates ledger propagation, and proves the no-rechecking theorem. A theorem
application never constructs a reduced space or manually transfers a closed
family.

## 5. Framework-owned coordinate changes

Coordinate handling is a domain action system. A domain layer registers
primitive generators once; Core builds paths freely and executes them.

```lean
structure CoordinateSystem (P : Problem) where
  Coordinate : Type uCoord
  Object : Coordinate -> Type uObj
  realize : (coordinate : Coordinate) -> Object coordinate -> P.Ambient
  Primitive : Coordinate -> Coordinate -> Type uStep
  act : {source target : Coordinate} ->
    Primitive source target -> Object source -> Object target
```

Core supplies:

```lean
inductive CoordinatePath (C : CoordinateSystem P) :
    C.Coordinate -> C.Coordinate -> Type
  | nil : CoordinatePath C a a
  | cons (step : C.Primitive a b) (tail : CoordinatePath C b c)

CoordinatePath.run
CoordinatePath.append
CoordinatePath.mapObstruction
CoordinatePath.transportStage
```

The domain specialization supplies semantic laws for each primitive generator:

- admissibility or baseline preservation;
- branch-state transport;
- locality and window containment;
- target or target-response naturality;
- retained-obstruction transport;
- representative, quotient, or interface compatibility; and
- the declared progress effect, if any.

Core derives identity transport, path composition, composite soundness, ledger
transport, and exact predecessor handoff. An application node cannot expose
`append`, `run`, a transformed branch state, or a manually composed map.

Typical Graph generators are restriction to an induced support, rooting,
relabeling, deletion, contraction, and boundary replacement. Typical PDE
generators are restriction to a smaller window, recentering, rescaling, gauge
normalization, quotient projection, and subsequence extraction.

## 6. Locality and atom/context assembly

Locality is independent of graphs and PDEs:

```lean
structure Locality (P : Problem) where
  Window : Type uWindow
  nested : Window -> Window -> Prop
  LocalObject : Window -> Type uLocal
  restrict : P.Ambient -> (W : Window) -> LocalObject W
  restrictNested : forall {core work},
    nested core work -> LocalObject work -> LocalObject core
```

An atom/context profile describes exact local/global decomposition:

```lean
structure AtomContextAssembly (P : Problem) (E : SemanticEquivalence P) where
  Interface : Type uInterface
  Site : P.Ambient -> Type uSite
  interface : (G : P.Ambient) -> Site G -> Interface
  Atom : Interface -> Type uAtom
  Context : Interface -> Type uContext
  compatible : {i : Interface} -> Atom i -> Context i -> Prop
  atom : (G : P.Ambient) -> (site : Site G) -> Atom (interface G site)
  context : (G : P.Ambient) -> (site : Site G) -> Context (interface G site)
  assemble : {i : Interface} -> Atom i -> Context i -> P.Ambient
  extractedCompatible : forall G site,
    compatible (atom G site) (context G site)
  reconstruct : forall G site,
    E.equivalent (assemble (atom G site) (context G site)) G
```

An optional exact-interface profile explains compatibility through a boundary,
trace, moment, gauge, or overlap code. It is required for exchange and response
compression, not for every decomposition.

Given a target-invariance profile, Core derives:

- replacement of an atom in a compatible context;
- exact recombination of a controlled contribution and a residual;
- transport of target responses through assembly;
- family assembly over occurrences already owned by the residual ledger; and
- pointwise local-to-global conclusions from local closures.

For a graph, `assemble` is boundaried gluing. For a Calderon-Zygmund split it
is addition of the localized term and harmonic/nonlocal tail. For a classical
good/bad decomposition it is the good part plus the residual-owned atom family.

Core never enumerates an ambient continuum. A finite family must be the exact
family in the incoming residual. A countable family requires a domain-supplied
summability or finite-truncation theorem and a registered limit profile.

## 7. Compactness and retained obstructions

Compactness is modeled as a semantic capability, not as Core search:

```lean
structure CompactExtraction (C : CoordinateSystem P) where
  Sequence : Type uSeq
  Limit : Type uLim
  Topology : Type uTop
  term : Sequence -> Nat -> P.Ambient
  Extracted : Sequence -> Type uExtracted
  selector : {sequence : Sequence} -> Extracted sequence -> Nat -> Nat
  selectorStrict : forall {sequence} (extraction : Extracted sequence),
    StrictMono (selector extraction)
  limit : {sequence : Sequence} -> Extracted sequence -> Limit
  converges : {sequence : Sequence} -> Extracted sequence -> Topology -> Prop
  extract : forall sequence, Extracted sequence
  baselineClosed : ...
  obstructionClosed : ...
```

`converges` is the declared convergence of `term sequence` along
`selector extraction` to `limit extraction`. The domain supplies this
compactness theorem, convergence topology, equation stability, and
obstruction-persistence proof. Core owns the extraction stage, records the
subsequence identity, transports the coordinate path, and creates the
descendant residual and ledger entry.

This is the continuum analogue of selecting a finite representative. It does
not authorize a theorem application to close an auxiliary limit unless the
retained obstruction is transported to that limit.

## 8. Generic module normal forms

A specialization that adopts the continuum fast track registers every
remaining analytic closure calculation through one of the following three
domain-independent normal forms. Ordinary CT searches, classifications,
peeling steps, and routing transitions retain their own CT contracts and do
not need to be restated as analytic quotients.

### 8.1 Class-closure form

Input: a represented remainder family, target projection, and target-complete
closed-class ledger.

Framework decision:

- zero quotient: propagate the family into the ledger and continue on the
  reduced carrier;
- nonzero quotient: emit the exact target-visible class residual.

### 8.2 Sign/gap form

Input: a nonnegative loss or budget form `D`, a positive forcing/readout form
`N`, a normalized residual-owned family, and an exact comparison certificate.

Framework decision:

- strict radius below one or positive lower gap: close or register the
  quantitative estimate;
- radius above one: emit a feeding-profile residual;
- equality: emit the compactified equality residual for the next module;
- zero lower gap: emit the zero-cost profile or minimizing-sequence residual.

### 8.3 Equality-rigidity form

Input: the exact equality family from the predecessor, saturation identities,
a target-complete closed ledger, and optionally a positive separator.

Framework decision:

- zero equality quotient: propagate the equality family into the ledger;
- nonzero quotient: emit the target-visible equality-rigidity residual.

Applications provide forms, identities, reflection theorems, and certificates.
Core constructs no theorem-specific quotient, extremizer state, or closure
record.

## 9. Budgets and work bounds

Two budget APIs remain separate.

`PolynomialCheckBudget` measures verifier work over explicit finite data. It
continues to govern executable CT scans, tables, and compositions.

`ResourceBudget` measures mathematical affordability:

```lean
structure ResourceBudget where
  Resource : Type u
  le : Resource -> Resource -> Prop
  zero : Resource
  add : Resource -> Resource -> Resource
  ceiling : Nat -> Resource
  monotone : ...
  compositionTransfer : ...
  representationInvariant : ...
  staticDynamicComparable : ...
```

This is the Core form of notebook axioms B1-B4. Graph instances use natural or
rational cardinality/charge budgets. PDE instances use energy, dissipation,
capacity, cost, or a product resource. Core derives bounded composition and
ledger accumulation but not the domain inequality connecting a resource to the
target.

## 10. Closure and reduction

Core recognizes five proof-producing closure mechanisms:

1. direct target or contradiction certificate;
2. smaller-object contradiction through a `Progress` profile;
3. budget, capacity, or aggregate contradiction;
4. imported theorem with an exact named contract; and
5. acyclic reduction to an already closed obstruction.

An obstruction reduction contains a target closed stage, an obstruction
transport theorem, coordinate compatibility, and a strict routing-rank proof.
Core verifies the target is already closed and performs the transport. A name
match or isomorphic-looking state is never closure by itself.

Terminal statuses are framework-derived. `route` is an edge action, not a
closure status. A completed proof has no reachable active-frontier residual.

## 11. CT1-CT17 as domain-independent contracts

The CT identifiers remain fixed. Their primitive types and executors must not
mention graph objects or PDE objects.

| CT | Generic contract | Graph specialization | PDE/continuum specialization |
|---|---|---|---|
| CT1 | Certify a target realization or exact target avoidance | Cycle/path/coloring witness | Regularity, zero-capacity, rigidity, or target-flux certificate |
| CT2 | Strict-progress deletion, replacement, or reduction | Delete/replace a graph piece | Replace a local atom, select a minimal profile, or reduce to a lower-rank obstruction |
| CT3 | Compare exact responses under compatible contexts | Same-boundary graph response | Local/tail, gauge, or quotient response under compatible global contexts |
| CT4 | Assign demands to resources and compare capacity | Charges to vertices, ports, or labels | Assign defects/errors to carriers, windows, profiles, or budget accounts |
| CT5 | Aggregate local witnesses into a global account | Sum local graph contributions | Aggregate local energy, pressure, flux, defect, or concentration witnesses |
| CT6 | Select first failure in an ordered schedule | First inactive graph site | First failed fast-track row, scale, window, or ordered PDE class |
| CT7 | Classify response in an exact context | Distinguishing outside graph | Distinguishing tail, gauge, topology, or target shell |
| CT8 | Detect repetition and compare repeated responses | Repeated finite graph type | Recurrent profile, repeated scale state, hull recurrence, or removable orbit segment |
| CT9 | Detect overloaded finite fibres | Pigeonhole on graph labels | Too many active profiles, bubbles, carriers, or packets for the mass budget |
| CT10 | Exhaust a declared finite classifier | Attachment or structural type | Residual signature, terminal row, error channel, or fast-track normal-form class |
| CT11 | Localize an additive deficit | Negative finite graph budget | Localize an integral/error budget to a supplied window or finite component family |
| CT12 | Peel with well-founded decrease and restoration | Degeneracy or support peeling | Bubble/profile extraction, scale descent, dyadic peeling, or descendant exhaustion |
| CT13 | Use primary resources then canonical fallback | Tiered graph payer | Routable/harmonic split, gauge/decay/cokernel split, or canonical carrier selection |
| CT14 | Compare aggregate mass and multiplicity | Class mass versus label capacity | Profile mass decoupling, dyadic sums, hidden-mass exhaustion, or capacity aggregation |
| CT15 | Compute target-relative rank or full-rank ledger | Boundary/response rank | Gauge cokernel, bracket rank, closed-range gap, quotient rank, or active coordinate rank |
| CT16 | Exhaust support and compare the closed code | Whole-graph closed type | Final compactified class, saturation type, or target-complete quotient audit |
| CT17 | Exhaust bounded scale/compatibility arithmetic | Bounded target offsets | Scale windows, target shells, modulation orbit, survivor, or compactification arithmetic |

Continuum profiles do not make uncountable search executable. They either use
an explicit finite residual-owned schedule or consume an exact analytic
certificate whose conclusion has the same CT residual contract. The CT
soundness theorem is shared; only the capability profile differs.

## 12. Framework versus domain ownership

Core owns:

- residual identity and accumulated proof ledgers;
- coordinate paths and all composite transport;
- atom/context assembly and replacement execution;
- focused decisions and sibling transport;
- closed-class quotient construction and propagation;
- CT execution, cross-CT transitions, and closure status;
- finite enumeration over residual-owned occurrences;
- work-budget composition; and
- local-to-global assembly executors.

A domain layer owns:

- meanings of windows, atoms, contexts, coordinates, and primitive actions;
- semantic preservation and reconstruction laws;
- observable, topology, target, and obstruction semantics;
- canonical constructors turning domain data into Core profiles; and
- reusable imported-theorem interfaces.

A theorem application owns only:

- concrete parameters already present in the current residual;
- primitive predicates, forms, and local witnesses;
- exact semantic estimates or named imported contracts; and
- direct instantiation of the smallest matching domain profile.

## 13. Forbidden public surface

No Graph, PDE, or theorem application API may expose fields for:

- a composed coordinate change or transformed predecessor;
- a manually assembled or glued successor;
- a copied predecessor output or ledger alias;
- a route executor, route rule, transition constructor, or target trigger;
- a caller-selected decision result or closure status;
- a manually reduced carrier or propagated quotient ledger;
- an application-defined empty refinement state;
- a detached list replacing residual-owned occurrences; or
- an unnamed remainder with no registered consumer.

If an application needs such a field, the missing operation belongs in Core or
in a domain-owned profile constructor.

## 14. Acceptance criterion

The architecture is successful when a graph node and a Navier-Stokes
fast-track row have the same application shape:

```lean
noncomputable def nextNode :=
  FrameworkExecutor previousResidual localSemanticCertificate
```

The application names only the predecessor and the new mathematics. The
executor retrieves every inherited fact, performs all coordinate and assembly
work, updates both relevant ledgers, routes every outcome, and returns a
framework-owned successor stage.
