# Temporary Core strategy proposals

This file is intentionally separate from `hypostructure/Hypostructure/Core/Strategy.lean`.
It records generic strategy patterns that PDE rows may need and that could also
be reused by Graph.  No PDE equation, Navier--Stokes constant, CT-specific
predicate, or external theorem belongs here.

## Existing surface checked

The current Core file already provides contracts, dichotomies, routed joins,
sequential composition, branch pipelines, work profiles, terminal
certificates, and `binaryContract`.  The proposals below should not duplicate
those declarations.

## Candidate additions

### 1. Finite scan with typed survivor

Generic shape:

```text
finiteScanContract
  (Item : Previous -> Type)
  (schedule : Previous -> FiniteEnumeration (Item previous))
  (accepts : Previous -> Item previous -> Prop)
  (decider : ...)
  (survivor : Previous -> Finset/Enumeration accepted items)
```

The strategy should scan the complete residual-owned schedule and produce one
of two typed terminals:

- `allAccepted`, carrying the checked ledger;
- `survivor`, carrying the exact first failed item and its membership proof.

It must derive the first failed item from the schedule rather than accept a
caller-supplied index.  This is useful for PDE observable windows, dyadic
scales, pressure channels, and Graph vertex scans.

### 2. Ordered first-failure strategy

Generic shape:

```text
orderedFailureContract
  (schedule : Previous -> FiniteEnumeration Item)
  (failure : Previous -> Item -> Prop)
  (decider : ...)
```

The output retains a clean-prefix certificate, the first failed item, and the
remaining suffix.  The prefix/suffix split must be derived from the incoming
enumeration and preserve predecessor ownership.  This generalizes PDE CT6
window schedules and Graph ordered support scans.

### 3. CT-chain adapter

Generic shape:

```text
ctChain
  (first : Contract Previous)
  (continuation : first-result -> Contract literal-first-stage)
```

This should expose a typed work composition and preserve every intermediate
ledger stage.  It must be a thin wrapper over existing `chain`/
`dependentChain`, not a second routing framework.  A PDE row may then specialize
it as CT10 -> CT11 -> CT1, while a Graph row may use CT2 -> CT3.

### 4. Branch-local continuation

Generic shape:

```text
branchContinuation
  (split : Dichotomy Previous)
  (left : ... -> Contract literal predecessor)
  (right : ... -> Contract literal predecessor)
```

The existing routed APIs should be preferred.  Add a new declaration only if
the current `BranchPipelines`/`runRouted` surface cannot expose branch-local
work and terminal certificates without reconstructing payloads.

## Acceptance requirements

- The strategy is domain-independent and usable by both PDE and Graph.
- Every finite scan consumes an incoming residual-owned enumeration.
- Every complementary branch remains a typed residual.
- No strategy assumes a theorem conclusion or external output in advance.
- Work bounds and predecessor preservation are part of the generic contract.
- Axiom and universe checks pass in an isolated Core fixture before any PDE
  specialization uses the strategy.

## PDE specialization mapping

PDE files should provide only adapters such as radius/window schedules,
observable predicates, pressure/gauge semantics, flux estimates, and analytic
soundness laws.  They should call the eventual Core strategies rather than
reimplementing scan, branch, composition, or terminal routing logic.
