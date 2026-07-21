# A Domain-Independent Core for Structural Exhaustion

Status: design note. The records below marked as conceptual or schematic are
proposed API shapes, not declarations claimed to exist in the current Lean
library.

## Purpose

The fundamental Core object should not be a graph profile. It should describe
a ranked proof problem whose current residual can be refined, split, routed,
and closed while all established facts remain in one accumulated ledger. Its
main reusable structural extension should be an **atom/context decomposition**:
an ambient object is separated into controlled local data and complementary
global data, then reconstructed by an exact assembly law.

Graphs, PDEs, additive problems, and geometric problems then provide the
semantics of atoms, contexts, and assembly. Graph boundary gluing, a
Calderon-Zygmund good/bad decomposition, and a local-pressure/nonlocal-tail
split are instances of the same pattern. A local atom with a global context
and an assembly law is the central reusable capability for these arguments,
but it is not required by every structural-exhaustion tactic and therefore
should not be a field of the smallest Core problem record.

This document distinguishes:

- the Core that already exists in the repository;
- the smallest domain-independent mathematical kernel;
- the optional local-decomposition API shared by graph gluing and PDE
  local/tail decompositions;
- the profiles that the framework can derive from those primitives; and
- the facts that must remain specific to an application.

## The Existing Kernel

The current fundamental record is `StructuralExhaustion.Core.Problem`:

```lean
structure Problem where
  Ambient : Type uAmbient
  Baseline : Ambient -> Prop
  rank : Ambient -> Nat
  BranchState : Ambient -> Type uBranch
```

The target predicate is deliberately supplied separately. The associated Core
types add the proof state needed by structural exhaustion:

- `BranchContext P` stores one ambient object, its baseline proof, and its
  inherited branch state.
- `AvoidingContext P Target` records that the current object avoids the target.
- `MinimalCounterexampleContext P Target` records target avoidance and the
  theorem that every lower-rank baseline object satisfies the target.
- `ResidualRefinement.State` keeps one stable residual and a typed list of all
  facts proved about it.
- `Node` and `StageNode` add one proposition or one data-bearing stage to that
  ledger.
- focused decisions and continuation executors split or close one active leaf
  while Core transports all untouched siblings.

That is already close to the correct irreducible base. It has no graph
vocabulary and can describe a PDE proof without modification.

## The True Minimum

At the mathematical level, a structural-exhaustion problem needs only the
following data.

1. An ambient type `World` of objects under consideration.
2. A baseline predicate identifying admissible objects.
3. A target predicate expressing the theorem to be realized.
4. A well-founded notion of progress.
5. Dependent branch state for data inherited by every later step.
6. A residual carrier and an accumulated typed ledger.

A conceptual version is:

```lean
structure StructuralProblem where
  World : Type u
  Baseline : World -> Prop
  BranchState : World -> Type v
  Measure : Type w
  measure : World -> Measure
  measureLt : Measure -> Measure -> Prop
  measureLt_wf : WellFounded measureLt

variable (Target : StructuralProblem.World -> Prop)
```

The repository currently specializes `Measure` to `Nat` through
`Core.Problem.rank`. This is sufficient whenever a lexicographic or multiscale
rank can be encoded into a natural number. A genuinely general Core could use
a well-founded relation, but that is a generalization of the current API, not
a prerequisite for expressing a PDE instance today.

The target should remain separate from `Problem` unless all tactics in an
instance must share exactly one target. Keeping it separate permits several
target predicates to use the same ambient type, baseline, rank, and branch
state.

The residual is also distinct from the ambient object. A residual is the
current branch-local payload: an ambient object together with whichever local
index, failed alternative, budget account, scale, or interface is active. Core
must preserve its identity while adding facts. It must not replace it with a
fresh application-defined handoff object at every node.

## The Atom/Context Abstraction

The cross-domain abstraction is an exact decomposition of a world into a local
atom and a global context. "Global" means all data not owned by the active
atom; it need not literally be the set-theoretic exterior of a support. This
should be an optional Core profile, not a graph profile.

A Lean-shaped design is:

```lean
structure AtomContextDecomposition (P : Problem) where
  Site : (W : P.Ambient) -> Type
  Atom : Type
  Context : Type

  atom : (W : P.Ambient) -> Site W -> Atom
  context : (W : P.Ambient) -> Site W -> Context
  compatible : Atom -> Context -> Prop
  assemble : Atom -> Context -> P.Ambient
  extracted_compatible : forall W site,
    compatible (atom W site) (context W site)
  reconstruct : forall W site,
    assemble (atom W site) (context W site) = W
```

The exact dependent types may differ in Lean, especially when the piece and
context types depend on an interface. The important contract is mathematical:

- `atom` extracts the local contribution at one site;
- `context` extracts the complementary global contribution;
- `compatible` states when recombination is legal;
- `assemble` reconstructs an ambient object; and
- `reconstruct` proves that decomposition followed by assembly returns the
  original object.

For an additive decomposition, `compatible` may simply be `True`. Exact
interfaces belong in a stronger optional profile:

```lean
structure ExactInterfaceProfile (P : Problem)
    (D : AtomContextDecomposition P) where
  Interface : Type
  atomInterface : D.Atom -> Interface
  contextInterface : D.Context -> Interface
  compatible_iff_interface_eq : forall atom context,
    D.compatible atom context <->
      atomInterface atom = contextInterface context
```

The interface is not necessarily a geometric boundary. It is whatever data
must agree when atoms may be exchanged across contexts. Examples include graph
boundary labels and degrees, PDE traces and moments, frequency cutoffs,
conservation data, or matching conditions on an overlap region. A pressure
decomposition that only reassembles its original terms needs the base profile;
a PDE replacement or compactness argument comparing different local pieces in
the same tail may additionally need `ExactInterfaceProfile`.

This one-hole form is enough for a local pressure/tail split or a graph piece
with its outside graph. A decomposition with many simultaneous atoms adds a
finite residual-owned family:

```lean
structure AtomicFamily (P : Problem)
    (D : AtomContextDecomposition P) where
  Index : (W : P.Ambient) -> Type
  indices : (W : P.Ambient) -> FinEnum (Index W)
  atomAt : (W : P.Ambient) -> Index W -> D.Atom
  globalPart : (W : P.Ambient) -> D.Context
  assembleFamily : {W : P.Ambient} -> D.Context ->
    (Index W -> D.Atom) -> P.Ambient
  reconstructFamily : forall W,
    assembleFamily (globalPart W) (atomAt W) = W
```

This is schematic: a concrete Lean definition must handle the dependency on
`W` explicitly and may use a residual-owned occurrence ledger instead of a
`FinEnum`. The essential law is

```text
world = assemble(global context, family of local atoms).
```

For classical Calderon-Zygmund decomposition, the global context is the good
part `g`, the atoms are the bad pieces `b_Q`, and assembly is addition:

```text
f = g + sum_Q b_Q.
```

For a PDE pressure split on a cylinder, one often has a single active local
term and a tail or harmonic context:

```text
p = p_local + p_tail.
```

The same Core profile should support both cases. It must not assume that
assembly is graph union, vector addition, or any other domain operation.

The current executable framework is finite. Consequently, an `AtomicFamily`
must come from the literal current residual: for example, the bad cubes in a
fixed bounded region and finite scale range. It must not be manufactured by
enumerating an ambient continuum. A countable Calderon-Zygmund family would
require either finite truncations plus a limiting theorem supplied by the PDE
layer, or a separate `SummableAtomicFamily` capability whose convergence and
limit semantics are proved analytically. The branch router should never hide
that analytic passage to the limit.

Ledger facts may still be arbitrary analytic propositions: norm estimates,
distributional identities, compactness statements, or regularity bounds. Only
an executable branch choice needs finite observable data or a supplied exact
decision theorem. The intended PDE workflow is therefore to prove an analytic
estimate, register it once, derive a finite threshold or scale summary from
it, and let Core route that summary. Core should not attempt to decide an
arbitrary real-valued inequality by computation.

## Operations Derived from One Pattern

The atom/context API is useful because several apparently different proof
moves are modes of the same decomposition.

| Mode | Operation on the atom/context decomposition | Framework role |
|---|---|---|
| Replacement | Substitute a compatible atom and reassemble | CT2 minimal replacement |
| Response comparison | Compare target-relevant observables under contexts | CT3, CT7, CT8 |
| Localization | Infer that some atom carries a global defect | CT5, CT11 |
| Aggregation | Sum atom masses and compare with global capacity | CT4, CT14 |
| Peeling | Remove one atom, update the context, and decrease a measure | CT12 |
| Refinement | Split an atom into smaller atoms or enrich its observables | CT10, CT15, CT16 |
| Scale thickening | Compare atoms or contexts across bounded scales | CT17 |

Thus Core does not need separate graph-flavored concepts for a piece, fan,
shoulder, port, or boundary exchange. Those are domain views of atoms,
interfaces, observables, and budgets. Likewise, it does not need PDE-flavored
concepts for cubes, pressure tails, or cutoffs.

## Derived Capability Profiles

One large `GraphProblemProfile` or `PDEProblemProfile` would conflate
independent hypotheses. The reusable API should instead be a small base plus
composable capability records.

### Ranked avoidance

Input:

- `Problem`;
- `Target`; and
- a lower-rank theorem or a mechanism selecting a minimal avoiding object.

Framework consequences:

- avoiding and minimal-counterexample contexts;
- smaller-object closure;
- rank-drop contradictions; and
- the generic part of CT2 and CT15.

### Replaceable local decomposition

Input:

- `AtomContextDecomposition`;
- a candidate replacement piece;
- interface compatibility;
- baseline preservation;
- target transport under every compatible context; and
- strict progress after replacement.

Framework consequences:

- reconstruction of the replaced ambient object;
- preservation of the branch's baseline;
- a smaller-object target theorem;
- silent-exchange contradiction by minimality; and
- the generic closure side of CT2.

The application proves the semantic preservation lemmas. The framework owns
the replacement construction, progress invocation, routing, and ledger update.

### Finite response decomposition

Input:

- a local decomposition;
- a finite response coordinate type;
- a response function for a piece in a compatible context;
- a finite code for relevant contexts; and
- a reflection theorem relating the code to the actual target response.

Framework consequences:

- exact response rows;
- same-interface equivalence;
- distinguishing-context residuals;
- smaller representative selection when a size order is supplied; and
- the reusable machinery behind CT3, CT7, CT8, CT10, and CT16.

This is the domain-independent form of the graph same-boundary response table.
The graph layer should only explain what graph pieces, contexts, interfaces,
and target responses mean.

### Budgeted local decomposition

Input:

- a finite family of local sites or occurrences;
- a value, mass, defect, or demand attached to each site;
- an additive or subadditive global comparison;
- eligible payers and capacities when charging is used; and
- the semantic theorem connecting the account to the ambient problem.

Framework consequences:

- deterministic assignment;
- missing-payer and overloaded-fibre splits;
- local witness aggregation;
- localization of a negative total;
- tier reconciliation; and
- aggregate mass-versus-capacity closure through CT4, CT5, CT11, CT13, and
  CT14.

The framework can perform finite accounting. It cannot invent the analytic or
combinatorial inequality that says the accounting controls the original
problem.

### Peelable decomposition

Input:

- a local item selected from the current residual;
- a removal operation;
- a well-founded decrease;
- a restoration or recombination operation; and
- preservation theorems.

Framework consequences:

- the finite schedule;
- deterministic next-item selection;
- termination;
- accumulated restoration data; and
- CT12 routing.

Again, Core owns execution and the ledger. The application supplies only the
meaning of removal, restoration, and preservation.

## A PDE Instantiation

Consider a local pressure decomposition of Calderon-Zygmund type. Schematically,

```text
p = p_local + p_tail.
```

This fits the same local-decomposition interface as graph replacement.

| Core concept | PDE interpretation |
|---|---|
| `World` | A solution, normalized counterexample, or solution-plus-domain package |
| `Baseline` | The PDE, admissibility, energy class, normalization, and scale regime |
| `Target` | The desired regularity, decay, boundedness, or exclusion statement |
| `rank` | Induction scale, number of bad cylinders, concentration level, or encoded multiscale rank |
| `BranchState` | Fixed norms, scale data, decomposition choices, and inherited estimates |
| `Site` | A ball, cube, spacetime cylinder, or frequency block |
| `Atom` | The localized velocity, forcing, vorticity, or local pressure contribution |
| `Context` | Exterior data, harmonic pressure tail, far-field forcing, and boundary traces |
| `Interface` | Cutoff traces, moments, fluxes, overlap data, or boundary values |
| `assemble` | Addition, extension plus correction, or reconstruction of the global field |
| `response` | A finite family of target-relevant local estimates or threshold decisions |
| budget | Energy, enstrophy, pressure mass, bad-scale count, or a Carleson-type account |

For the pressure split, the local atom can be the singular-integral response to
the cutoff nonlinear term. The context contains the nonlocal tail, often
represented by a harmonic contribution on the smaller region. Assembly is the
identity that recombines those terms into the original pressure. When later
steps compare or replace local terms, an optional interface records exactly
the normalization, trace, moment, or overlap data needed for those operations.

The decomposition itself is not a dichotomy: the local term and tail coexist
and both are registered on the same residual. A later framework decision may
split on which estimate dominates, whether a threshold is crossed, or whether
one component can be absorbed.

The framework can then manage a branch such as:

```text
current residual
  -> decompose into local term plus tail term
  -> register both components and estimates in the same ledger
  -> decide a finite scale or threshold alternative
  -> localize a failed global budget to one cylinder
  -> peel a good scale or route a bad-scale residual
  -> close by rank decrease, target realization, or budget contradiction
```

Core should own that control flow. The PDE package must still prove the actual
Calderon-Zygmund estimate, harmonic-tail estimate, cutoff commutator bound,
and reconstruction identity. Those are mathematical semantics, not routing
machinery.

## What Can Be Automated

Once the profiles above are instantiated, the framework can derive:

- exhaustive binary or finite decisions from supplied deciders;
- first-failure selection on a supplied finite schedule;
- exact preservation of the incoming residual and accumulated ledger;
- sibling transport through focused branch decisions;
- response-table comparison and distinguishing coordinates;
- deterministic demand-to-payer assignment and capacity checks;
- finite-sum localization and aggregate comparisons;
- well-founded peeling execution;
- minimality invocation after a certified strict decrease; and
- terminal closure when a registered certificate contradicts the active
  residual.

It cannot derive domain theorems merely from names. In a graph proof it cannot
invent that gluing preserves minimum degree or creates a target cycle. In a PDE
proof it cannot invent an elliptic estimate, a pressure decomposition, or an
epsilon-regularity theorem. Such facts are primitive semantic bridges supplied
once by the domain layer and then consumed through generic Core executors.

## Ownership Boundary

The intended dependency direction is:

```text
Core.Problem
  + Core residual/ledger/routing
  + optional Core capability profiles
      -> domain semantics (Graph, PDE, additive, geometric, ...)
          -> theorem-specific parameters and local facts
```

Core owns:

- branch state and residual identity;
- typed fact and stage registration;
- decisions, continuation, and sibling transport;
- finite schedules and deterministic execution;
- work accounting;
- well-founded progress invocation;
- CT output types and transitions; and
- closure executors consuming registered certificates.

The domain layer owns:

- the meaning of atoms, contexts, interfaces, and assembly;
- reusable preservation and reflection theorems;
- domain-native rank and budget interpretations; and
- reusable constructors turning domain objects into Core capabilities.

The individual theorem application owns:

- concrete parameters;
- the current residual's local mathematical witnesses;
- theorem-specific semantic estimates; and
- direct instantiation of domain or Core profiles.

It should not own ledger reconstruction, handoff records, copied predecessor
outputs, branch routing, or custom closure state.

## Recommended Core Hierarchy

The practical hierarchy is compositional rather than object-oriented:

```text
Problem
  + Target
  + residual ledger
        |
        +-- RankedAvoidance
        |
        +-- AtomContextDecomposition
        |     +-- ExactInterface
        |     +-- Replaceable
        |     +-- FiniteResponse
        |     +-- SupportStratified
        |
        +-- FiniteLocalFamily
        |     +-- Budgeted
        |     +-- Chargeable
        |     +-- Aggregatable
        |
        +-- Peelable
```

No application must implement every branch of this hierarchy. A proof imports
only the capabilities used by its manuscript steps. CT executors ask for the
smallest matching profile and return framework-owned residual stages.

## Design Conclusion

The fundamental Core base class is the existing idea of `Core.Problem`, paired
with a target, a well-founded progress principle, and the stable residual
ledger. The atom/context/assembly abstraction is the next reusable layer. It is
the common structure behind graph boundary replacement and PDE local/tail
decomposition, but it should remain an optional `AtomContextDecomposition`
capability rather than becoming part of every problem.

From that capability, the framework can derive the control structure of
replacement, response compression, finite accounting, localization, peeling,
and closure. Graph-specific objects such as paths, fans, and degree profiles,
and PDE-specific objects such as pressure tails, cutoffs, and analytic norms,
belong only in their respective semantic layers.
