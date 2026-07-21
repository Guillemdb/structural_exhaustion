# Repair design: product-fit dichotomy and curvature-free degradation route

## Status and scope

This is a level-2 structural repair worksheet.  It does not modify
`original_erdos_64_proof.tex`, the live manuscript, the Lean development, or
the web diagram.  It freezes the gap between the full curvature-rank output
and the powered entropy comparison, and designs an exhaustive branch that
uses only the existing residual, its accumulated ledger, and framework-owned
routing.

The repair deliberately does **not** request a graph switching theorem.  It
applies the methodology's hypothesis-extraction rule: the extra hypothesis
needed by the node-[48] powered-cost argument becomes a decidable branch
predicate.  Its positive side keeps the original Part-IV flow.  Its negative
side is retained as a typed residual and sent to the curvature-free closure
that the original paper already declares in `rem:closure-robust`.

## Frozen defect

The verified node-[32] no branch proves full target rank for the raw curvature
coordinates.  The node-[48] powered comparison additionally needs the exact
finite product-fit statement

```text
543958 ^ rOmega <= 111286 ^ rOmega * stateCount.
```

The finite table certifies the two one-coordinate cardinalities `543958` and
`111286`.  Full target rank alone does not prove the displayed product
inequality for the literal realized-state carrier.  The invalid repair would
be to add that implication as a theorem or hypothesis.  The admissible repair
is to decide the product-fit statement on the current residual.

## Exact incoming state

The split is executed only on the literal residual reaching node [48].  The
single accumulated ledger already contains:

- the fixed minimal target-avoiding graph and its selected induced-`P13`
  packing;
- the exact `P13`-free remainder;
- the node-[21] curvature table values `543958`, `432672`, and `111286`;
- the node-[22] window-density output on the surviving branch;
- the node-[30] wedge and net-deficiency inequalities;
- the node-[32] no/full-rank certificate, transported through node [47];
- the near-cubic and target-uncompressibility invariants established earlier.

No node in this repair defines another graph family, state family, remainder,
checkpoint, or handoff object.  If a finite realized-state view is needed to
evaluate product fit, it must be a framework projection of this incoming
residual.  The view is not new mathematical state.

## The admitted dichotomy

Let `ProductFit(B)` denote, on the incoming branch state `B`,

```text
543958 ^ rOmega(B) <=
  111286 ^ rOmega(B) * realizedStateCount(B).
```

The framework decides this proposition and appends exactly one of the
following proof-relevant facts to the same residual ledger:

1. `ProductFit(B)`;
2. `not ProductFit(B)`.

For diagnostic precision, the second constructor may also retain the
canonical first failed coordinate/prefix produced by the existing finite
conditional-fibre checker.  That witness explains *where* the product
telescope failed.  It is not an assumption, a new carrier, or a prerequisite
for the curvature-free route.

### Both-sides admission test

| Field | Positive side | Negative side |
|---|---|---|
| Meaning | The powered table cost fits the literal realized-state count. | The powered table cost is unavailable on this residual. |
| Payment | Pays the curvature currency used at nodes [48], [53], and the small-budget edge into [54]. | Pays no curvature currency; explicitly disables every consumer of that currency. |
| Forced residual | Original node-[48] output. | `CurvatureCostUnpaid`, retaining the same graph, remainder, packing, and all curvature-independent ledger facts. |
| Measurability | Exact natural-number comparison on finite data projected from the current residual. | The decidable negation of the same comparison; optionally a canonical first failure. |
| Route | Original `[48] -> [49] -> [50] -> [51]/[53] -> [54]/[55]` flow. | Framework-owned degradation handoff to the window-only net-charge interface beginning at [56]. |

All four blanks of the methodology's both-sides test are filled.  The split
spends only recorded finite data and therefore passes the
bookkeeping-versus-new-theorem test.

## Directed repair flow

```text
node [47]: full curvature target rank
                  |
                  v
      framework decision: ProductFit?
           / yes                    \ no
          v                          v
 node [48]: powered cost       CurvatureCostUnpaid
          |                          |
          v                          | forget only curvature currency
 original Part-IV flow               | preserve the complete residual ledger
 [49] -> [50] -> [51]/[53]           v
          |                       robust window-only interface
          +----> [54] closes          at node [56]
          |
          +----> [55] -> [56] <-------+
                         |
                         v
             existing net-charge/local-analysis chain
             CT5 -> CT11 -> Type A / Type B consumers
                         |
                    C1--C5 closure
```

The negative edge does not pretend to satisfy `Node53Large`.  It bypasses
nodes [48]--[55], whose only new role is curvature/entropy routing, and enters
the common node-[56] interface directly.  This distinction is essential:
failure to pay curvature cost does not imply the node-[53] large-budget
inequality.

## Why node [56] is the correct join

The original paper states in `rem:closure-robust` that the large-budget
closure outside the explicit residuals does not require the curvature-rank or
forced-cost magnitude.  It uses instead

```text
theta <= theta_win + o(1)
```

and the resulting window-only estimate

```text
(positiveDeficiency(R) - surplus(R)) / |R|
  <= tau_win + o(1) < 1/4.
```

The current Lean node [56] confirms this dependency separation: its local
proof retrieves the node-[30] net-deficiency cap and proves
`tau_win < 1/4`; it does not use `Node55Output.largeBudget`.  Consequently the
mathematical trigger for the robust join is not “node [53] was large.”  It is
the curvature-independent window-density and net-deficiency ledger already
present before node [48].

The framework repair should therefore expose the **common trigger actually
consumed by node [56]**:

```text
WindowOnlyNetChargeInput :=
  inherited node-[22] window-density fact
  + inherited node-[30] finite net-deficiency cap
  + the literal incoming remainder and surplus ledger.
```

Both the original `[53] no -> [55]` path and the new `not ProductFit` path
project this same trigger from their accumulated residual.  Core owns the
projection and the join.  Application code proves no route equality and
constructs no replacement residual.

## CT decomposition of the negative branch

The negative branch is closed by an existing curvature-free CT chain rather
than by analyzing all possible failed fibres.

### Stage R1: framework degradation handoff

Input: the incoming residual plus `not ProductFit`.

Operation: retain the full ledger, mark the curvature-cost currency as
unavailable, and project `WindowOnlyNetChargeInput`.

Output: the exact trigger consumed by the node-[56] budget step.  This is an
acyclic typed handoff, so it needs preservation, routing, and trigger proofs,
but no decreasing measure.

### Stage R2: CT5 local-to-global bookkeeping

CT5 consumes the existing window, stub, remainder, and surplus accounts.  It
produces the finite net-deficiency comparison already represented at node
[56].  No curvature coordinate, product-fit witness, or state count appears
in this account.

### Stage R3: CT11 finite-sum localization

From `tau_win < 1/4`, the total net charge is negative.  CT11 localizes this
negative total to a connected admissible support.  Its payload retains
target avoidance, empty internal `3`-core, dyadic safety,
uncompressibility, and the canonical surplus assignment.

### Stage R4: existing Type A / Type B closure routes

The localized support is processed by the already declared local-analysis
branches:

- a realizing local exchange returns C1;
- a smaller target-equivalent replacement returns C2;
- a target-defective exact response returns C3;
- a capacity or aggregate net-charge violation returns C4;
- a completely checked finite local table returns C5;
- an intermediate Type A/Type B payload is sent only to its existing named
  consumer, preserving the original local-analysis flow.

No product-failure-specific graph theorem is introduced.  The only role of
`not ProductFit` is to select the robust currency-free route.

## Optional first-failure refinement (not load-bearing)

The framework's product checker can retain a canonical first failed prefix.
If later optimization wants to recover some curvature payment, that witness
may be inspected through the existing CT vocabulary:

- an empty next fibre is a finite missing-datum payload for CT10;
- an excessive survivor ratio is an overload payload for CT9;
- CT9 may route a homogeneous fibre to CT7, CT8, or CT10;
- CT7 closes by hit, defect, or compression when its exact trigger is met.

This refinement is not required for correctness of the repair.  It must not
delay or condition the robust node-[56] handoff, and it must not introduce a
second residual carrier.

## Required framework changes before Lean implementation

1. Provide a generic decision combinator that appends `P` or `not P` to the
   one accumulated residual and preserves every previous fact.
2. Provide a generic **degradation projection**: a branch may forget an
   unusable optional currency/certificate and expose a weaker consumer
   trigger already entailed by the ledger.
3. Provide a generic join on equal consumer triggers.  The two producers may
   carry different branch reasons, but application code sees only the common
   `WindowOnlyNetChargeInput`.
4. Make node [56] consume that common trigger, not the historical
   `Node55Active` shape and not `Node55Output.largeBudget`.
5. Preserve the original node-[53] no branch and node [55] statement.  Their
   ledger still records the large-budget fact even though the common
   downstream node-[56] theorem does not need it.
6. Record product-fit provenance only on the positive branch.  Nodes [48]
   and [54] must be unable, by type, to retrieve it on the degradation branch.

These are framework-level residual operations.  The Erdős layer supplies
only the local proposition `ProductFit` and the proof that the incoming
ledger entails `WindowOnlyNetChargeInput`.

## Lean obligation ledger

| ID | Obligation | Owner | Status |
|---|---|---|---|
| PF-1 | Define `ProductFit` from the literal incoming residual-owned finite data. | Erdős node-local statement | ready from existing quantities |
| PF-2 | Decide `ProductFit` without enumerating ambient graphs or universes. | Core finite decision | ready in principle |
| PF-3 | On `ProductFit`, construct exactly the powered certificate consumed by node [48]/[54]. | existing Core powered-budget machinery | existing arithmetic; reconnect required |
| PF-4 | On `not ProductFit`, retain a proof-relevant negative constructor. | Core decision carrier | framework work |
| DG-1 | Project `WindowOnlyNetChargeInput` from either incoming ledger. | Core entailment/projection | framework work |
| DG-2 | Prove the projection uses no node-[48] curvature-cost fact and no node-[53] large-budget fact. | dependency audit | supported by current node-[56] body |
| DG-3 | Join original node-[55] and degradation paths at the same node-[56] trigger. | Core branch join | framework work |
| NC-1 | Reuse node-[56] finite and real net-deficiency cap. | Erdős instantiation of CT5 | existing local proof |
| NC-2 | Localize negative net charge to an admissible support. | CT11 | original downstream obligation |
| NC-3 | Route every localized Type A/Type B outcome to C1--C5 or its declared consumer. | existing downstream CT chain | outside this repair's immediate code cut |

## Leaf-totality table

| Leaf | Result | Consumer | Closure status |
|---|---|---|---|
| `ProductFit` and node-[50] high | original nodes [51]--[54] | entropy terminal | unchanged |
| `ProductFit`, node-[50] low, node-[53] small | original node [54] | powered-budget terminal | unchanged once PF-3 is connected |
| `ProductFit`, node-[50] low, node-[53] large | original node [55] | common node-[56] trigger | unchanged |
| `not ProductFit` | curvature-cost-unpaid degradation residual | common node-[56] trigger | designed; DG-1--DG-3 remain |
| node-[56] localized Type A/Type B leaves | existing local analysis | C1--C5 / declared consumers | inherited downstream proof obligations |

## Progress and termination

The new split is acyclic.  Its negative side makes strict proof-state
progress by deleting the curvature currency from the set of live closure
accounts and entering the already ordered net-charge phase.  It cannot return
to the product-fit decision.  Optional CT9/CT10 diagnosis, if ever enabled,
must use a strictly shorter remaining coordinate suffix or a strictly refined
finite label; it is not part of the load-bearing route.

No ambient family is enumerated.  The product decision is one exact
natural-number comparison plus, optionally, a linear scan over the already
declared finite coordinate order.  All later work is symbolic ledger
transport and local CT execution.

## Red-team pre-audit

### Passed checks

- No graph switching theorem, simultaneous-realization implication, new
  axiom, or hidden global estimate is assumed.
- The positive branch is exactly the original Part-IV entropy route.
- The negative branch is not mislabeled as node-[53] large budget.
- The route uses the original paper's explicit curvature-free robustness
  statement.
- Node [56]'s present proof body is curvature-independent and does not consume
  its predecessor's `largeBudget` field.
- Both branches operate on one literal residual and one accumulated ledger.
- The proposed computation is local and practical.

### Open checks before merger

- Kernel-check the generic degradation projection and common-trigger join.
- Refactor node [56]'s input type so its mathematical contract exactly matches
  what its proof consumes.
- Re-run the dependency audit through the full Type A/Type B closure to ensure
  no later consumer retrieves `Node53Large` indirectly.
- Red-team every terminal downstream leaf and update TeX--Lean--web evidence
  only after those checks pass.

## Verdict

**DESIGN ADMITTED; IMPLEMENTATION NOT YET VERIFIED.**  The repair passes the
methodology's both-sides and bookkeeping tests.  The decisive design choice
is to route failed curvature product fit into the paper's existing
curvature-free net-charge closure, not to prove a graph switching theorem and
not to force the failure into the node-[53] large-budget inequality.

