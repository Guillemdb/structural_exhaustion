# Erdős--Gyárfás Chapter 1 Strategy Translation Plan

## Purpose

This document is a translation map for the remaining Chapter 1 nodes.  It
does not introduce new proof strategies or alter the paper's Branch A and
Branch B conclusions.  Those branches are already closed mathematically in
the paper.  The task is to express their existing node sequences as
Hypostructure CT executions and then package each cohesive sequence as a
reusable strategy.

The current Hypostructure package already contains the node carriers through
the implemented frontier and the `OnlyTypeAOrB` checkpoint.  The original
repository stores much of the later proof in `Erdos64EG/Shared` rather than
standalone `NodeX.lean` files.  Those shared files are the authoritative
source for the remaining CT inputs, terminal payloads, and paper arithmetic.

## Translation Rules

Every translated strategy must satisfy the following shape:

1. Its input is the literal predecessor residual and accumulated ledger.
2. Every CT receives data through a Core query or a Graph adapter.
3. CT-to-CT routing is performed by the framework route registry.
4. A strategy adds one typed ledger extension, or a framework-owned composed
   extension, and never copies earlier payloads into a new application record.
5. Every terminal is a paper-defined outcome: closure, Type A continuation,
   Type B continuation, or an explicitly named remaining residual.
6. The strategy exposes an exhaustive terminal theorem and a composed work
   bound.
7. Numerical constants, P13 labels, hot/cold predicates, and paper budgets are
   supplied by the EG contract, never by Core strategy machinery.

The reusable abstraction is therefore a **strategy schema**, not a new CT.
The schema composes existing CTs and routes; its EG instance supplies only
the contract primitives and the paper's terminal theorem.

## Already Available Strategy Blocks

These are the blocks that should be reused directly when translating the
remaining nodes.

### Target-or-Avoid

Source: nodes 5--7, `Shared/CT1.lean`, `Shared/CT1InducedP13.lean`.

Composition:

```text
CT1 target realization
  -> target terminal
CT1 target avoidance
  -> target-avoiding residual
```

The same schema is reused for Mersenne cycles, induced P13 avoidance, four
cycle avoidance, fan-window cycles, and two-window cycles.  Only the Graph
target profile and the supplied certificate differ.

### Minimality and Certified Reduction

Source: nodes 8--14, `Shared/CT2.lean`, `Shared/CT3.lean`.

Composition:

```text
lexicographic minimal selection
  -> CT2 deletion/criticality
  -> CT3 boundary response classification
  -> certified replacement contradiction or hereditary residual
```

This is the reusable minimal-counterexample compression strategy.  It should
be used for both the early boundaried atom proof and the later local
replacement arguments.

### Packing and Remainder

Source: nodes 15--18, `Shared/CT12InducedP13Packing.lean`,
`Shared/CT10P13LabelAlgebra.lean`.

Composition:

```text
CT1 induced-P13 decision
  -> HSS closure of the avoiding branch
  -> CT12 maximal induced-P13 packing
  -> CT10 finite attachment-label classification
```

The output is the exact selected packing, remainder, legal label table, and
ledger provenance.  No family of packings or graphs is searched.

### Entropy and Finite Budget Split

Source: nodes 19--24 and 48--55, `Shared/P13SequentialEntropyFiltration.lean`,
`Shared/P13SequentialWindowLedger.lean`,
`Shared/P13ExactWeightedRate.lean`.

Composition:

```text
Core threshold split
  -> CT15 finite rank/bit budget
  -> sequential hot/cold filtration
  -> CT4/CT5 compatible-completion accounting
  -> CT9/CT14 capacity or overflow terminal
```

The framework must preserve the realized/open completion alternatives.  It
must not turn a supplied numerical bound into a constructed completion or
silently discard the cold residual.

### Sparse Surplus and Local Port Ledger

Source: nodes 61--84 and the corresponding shared CT6/CT9/CT14/CT15 files.

Composition:

```text
CT11 connected negative-budget localization
  -> high/no-high decision
  -> Type B high-center port classification, or Type A support profile
  -> CT5 local incidence ledger
  -> CT9 capacity/compatibility split
  -> CT14 mass/deficit comparison
```

The current Graph connected-support adapter and `OnlyTypeAOrB` theorem are
the entry checkpoint for this block.  The rest of the block must consume the
literal support and ledger; it must not reconstruct a support from a branch
label.

### Pair, Token, and Overload Accounting

Source: nodes 125--144, `Shared/CT15SparsePairResponses.lean`,
`Shared/CT9AllPairAnchorLedger.lean`,
`Shared/CT9CapacityTokenLedger.lean`,
`Shared/CT9CoupledClassOverload.lean`.

Composition:

```text
CT15 sparse-pair response coordinates
  -> CT9 free/blocked and anchor classification
  -> CT9 capacity-token partition
  -> CT9 coupled class overload
  -> CT13/CT14 matching, star, or aggregate terminal
  -> CT3 homogeneous-response continuation
```

The complete pair schedule is one residual-owned finite schedule.  The
strategy must not enumerate graph families, Boolean cubes, matching families,
or powersets.

## Branch A Translation

Branch A is the no-high continuation after the Type A/Type B checkpoint.  Its
paper content is already closed; the translation target is the following
ordered CT program.

### A1. Type A Support Contract

Input: the Node 61 connected negative support and its preceding remainder
ledger.

Graph obligations:

- connected support;
- ambient cubicity;
- internal subcubicity;
- induced-P13 freeness;
- internal three-core freeness;
- exact support inclusion in the selected remainder.

Reusable machinery: `Graph.SupportComponents.Connected`, CT2 criticality,
the Graph induced-subgraph and HSS adapters.

Output: a `TypeASupportProfile` carrying only the proven support facts and a
canonical receiver schedule.

### A2. Canonical Receiver Trace

CT sequence:

```text
CT12 ordered support scan
  -> first low-degree receiver in the first occupied layer
  -> rooted shortest trace certificate
```

The trace strategy must expose the clean cubic prefix and the receiver's
internal degree bound.  It must use the declared support schedule and never
search all paths.

### A3. Completion Ports and Anchored Returns

CT sequence:

```text
CT6/CT10 receiver-port coordinate scan
  -> CT2 non-bridge certificate
  -> Mathlib reachability-to-simple-path extraction
  -> anchored return coordinate
```

The anchored return is a proof-carrying graph object.  The strategy does not
enumerate walks or return families.

### A4. First Entry, Connector, and Spectrum

CT sequence:

```text
ordered prefix scan of an anchored return
  -> first support entry
  -> CT5 connector/channel extraction
  -> CT1 target-avoidance response
  -> finite response spectrum
```

The output is the exact Type A continuation-coordinate family required by the
paper.  Its terminal alternatives are the paper's continuation classes,
absorption/removal conclusion, or the smaller-object/CT8 residual.  These are
not new conclusions; they are the existing Branch A terminals expressed as
typed residuals.

### A5. Remaining Type A Producers

The chapter-1 definitions require the following producer contracts before the
final strategy can be assembled:

- D5: canonical cubic-to-receiver trace family and response-preserving
  continuation classes;
- D7: compatible-context response evaluator on the active interface;
- CT8 removal/repetition certificate for two response-equivalent continuations;
- the exact Branch A handoff terminal used by the paper's exit (7).

The existing raw Type A coordinate and rooted-path-family machinery should be
lifted into these CT contracts.  No new Type A theorem is needed.

## Branch B Translation

Branch B is the high-surplus continuation.  Its paper proof is the Type B
local charge and global token argument.  The translation should be assembled
from the following strategy stages.

### B1. High-Center Fan Profile

CT sequence:

```text
CT10 incident-port classification
  -> CT9 same-center capacity/compatibility decision
  -> CT7 adjacency-response comparison
  -> CT5 shoulder and assigned-incidence ledger
```

The profile returns the paper's compatible open pair or triangular alternative,
with the exact degree-four side preserved as its own terminal.

### B2. Fan Certificate and Local Deficit

CT sequence:

```text
CT9 marked-label capacity packing
  -> CT9 non-singleton refinement
  -> CT14 certificate-closed mass
  -> CT14 hybrid-incidence capacity comparison
  -> CT1 direct-cycle and two-window avoidance
```

The output is the paper's literal fan-closed port, closed-neighbour count,
hybrid credit ledger, and positive-deficit Type B local certificate.
The fixed P13 label arithmetic remains an EG contract/table; the capacity
machine is Graph-generic.

### B3. Candidate and Residual-Center Ledger

CT sequence:

```text
CT14 positive-deficit candidate construction
  -> CT4/CT5 assigned-incidence payment
  -> CT11 residual-center localization
  -> CT13 primary/fallback payer selection
  -> Type B residual-center terminal or Type A boundary residual
```

This is where the paper's exact Type B-to-Type A boundary must be represented
as a typed terminal.  A negative or unpaid residual is not silently closed;
it is the paper's explicit Type A continuation input.

### B4. Window Join and Capacity Tokens

CT sequence:

```text
CT15 sparse-pair response profile
  -> CT9 anchor ledger
  -> CT9 window/remainder/primitive token partition
  -> CT9 coupled class overload
  -> CT13 matching/star fallback
```

The strategy consumes the exact selected P13 packing and active surplus slots.
Its two paper terminals are the overloaded homogeneous pattern and the
quadratic capacity bound.

### B5. Homogeneous Response and Final Type B Closure

CT sequence:

```text
CT14 overloaded-fibre projection
  -> maximal matching/star certificate
  -> CT16 closed-code or CT3 response repetition
  -> CT8 smaller-object/removal conclusion
```

This translates the paper's final Type B homogeneous-pattern argument.  The
classifier uses the fixed finite code schedule supplied by the EG contract;
the framework owns the first-hit scan, repetition certificate, and terminal
routing.

## Shared Strategy Schemas Needed

The following generic schemas are sufficient to express both branches and
should be implemented once in Core, with Graph adapters where graph semantics
are required:

| Schema | CTs | Reusable role |
|---|---|---|
| `OrderedWitnessScan` | CT6, CT12 | First failure, first receiver, first repetition |
| `FiniteResponseClassifier` | CT3, CT7, CT8, CT10 | Response classes, separators, repeated types |
| `CapacityLedger` | CT4, CT5, CT9, CT13, CT14 | Charges, fibres, payer choice, overload |
| `SupportLocalization` | CT11, CT12 | Negative support, peeling, connected schedules |
| `TargetAvoidingContinuation` | CT1, CT2, CT7 | Certified avoidance and inherited semantic responses |
| `RankAndBudgetSplit` | CT15, CT17 | Finite rank, scale, entropy, and survivor arithmetic |
| `ClosedCodeExhaustion` | CT16, CT8 | Exact finite code scan followed by repetition/removal |

Each schema should expose a typed input contract, a terminal family, a single
ledger-preserving execution, exhaustive terminal coverage, and a composed work
bound.  Branch A and Branch B should be thin compositions of these schemas.

## Implementation Order

1. Freeze the paper terminal contracts for D5 and D6 from Chapter 1.
2. Lift the existing Type A coordinate producers into the
   `OrderedWitnessScan` and `TargetAvoidingContinuation` schemas.
3. Lift the existing Type B fan, charge, and token producers into
   `CapacityLedger` and `SupportLocalization`.
4. Implement the missing CT8/CT16 terminal consumers for response repetition
   and closed-code exhaustion.
5. Register the Branch A and Branch B route graphs using framework routes.
6. Prove the branch-local exhaustive theorem at each strategy boundary.
7. Add one non-EG Graph fixture per generic schema, then add the EG
   instantiations and validate in five-node batches.

The final theorem should therefore be a composition of the paper's existing
Branch A and Branch B terminal contracts, not a new `OnlyTypeAOrB`-style
logical shortcut.  `OnlyTypeAOrB` remains the intermediate checkpoint that
selects which already-defined paper continuation strategy receives the exact
predecessor ledger.
