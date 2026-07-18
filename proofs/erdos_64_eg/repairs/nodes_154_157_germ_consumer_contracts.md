# Nodes [154]--[157]: bounded-germ consumer contracts

Status: consumer-side prototype.  This note freezes the exact payload expected
from the F1--F5 producer and audits the G1--G3 consumers.  It does not claim
that node [153] constructs that payload, and it does not change the source
manuscript.

## Defect freeze

- Stable nodes: [154]--[157].
- Failed implication: the currently constructed graph-owned corridor data do
  not, for every selected cold half-edge, construct a fixed-size two-boundary
  germ with a complete finite response table and a proper replacement.
- Smallest verified ancestor: the same-window/corridor modules construct an
  actual selected window, actual component return data, and several D1--D7
  local clauses, but not the complete F5 payload below.
- Blast radius: the bounded-overlap extraction at [153], aggregate cold
  closure at [154]--[157], and hence the strict node-[24] density conclusion.
- Repair level: level 2 structural producer repair.  No conclusion is added as
  a hypothesis to the graph-owned producer.

## Exact abstract input from F1--F5

For one selected branch-excess incidence, F1--F5 must return exactly one of:

1. **F1/G1:** an actual cycle in the inherited graph, with a proof that its
   length satisfies the power-of-two target predicate.  An arithmetic length
   alone is insufficient.
2. **F2:** two literal pieces on the same fixed boundary and one literal
   compatible outside context on which their target truth values differ.
3. **F3/G3:** a proper atom and replacement on the same boundary, equality of
   boundary-degree profiles, target equivalence for every compatible outside
   context, internal target freedom, internal minimum degree, and strict local
   lexicographic decrease.
4. **F4:** the complete trigger of an already declared Type-B or route-8
   consumer, including its receiver/load/support/account fields.  Merely
   entering a high-degree vertex is not that trigger.
5. **F5:** a fixed-size owned two-boundary support with two same-interface
   representatives and a finite local context-code table.  The response table
   must have a reflection theorem for every enumerated code and a coverage
   theorem

   ```text
   forall outside : Context T, exists code,
     Target (glue replacement outside) <-> replacementResponse code = true
     and
     Target (glue source outside) <-> sourceResponse code = true.
   ```

The quantifier is over every literal context compatible with the fixed packed
piece, but the implementation does not enumerate those contexts.  The producer
supplies a symbolic projection to the fixed local code table.

The current Lean type `P13ColdGermLedger.ColdBoundedGerm` is the exact
consumer-side F5 contract.  Its fields must be constructed from graph-owned
F1--F5 data; accepting an arbitrary inhabitant does not verify node [153].

## G1--G3 contracts

### G1: actual dyadic target

Input: `ColdDyadicHit`, containing an actual `CycleWithLength` in `ctx.G`.
The existing one-check CT1 run consumes that same cycle and reaches C1.  There
is no search over graphs, cycles, or ambient contexts.

### G2: target defect

Input: `ColdContextDistinction`, containing the two exact representatives and
the selected outside context.  This implies the literal graph-layer
`TargetDefective` proposition.  The provenance-preserving route retains the
same left piece, right piece, outside context, ambient graph, baseline, and
branch state.

A target defect is **not yet** an exit-(4) or existing-ledger token.  Such a
consumer additionally needs its receiver, routed load, quotient support, and
charge update.  Therefore the sound G2 endpoint is the typed
`TargetDefectHandoff.Residual`; exit-(4) remains a separate producer/route
obligation.

### G3: silent exchange

Input: `ColdSilentExchange`, containing universal target equivalence on the
literal context type, internal target freedom, internal baseline preservation,
and strict local decrease.  `Compression.ofTargetComplete` constructs the
global smaller object, executes CT3, and contradicts minimality.  Equality on
the thirteen offset bits alone does not supply universal target equivalence.

### Finite same-interface table

`GermTable` enumerates only the fixed local row type.  CT10 certifies exhaustive
processing of that supplied row type with quadratic local work.  It neither
enumerates boundaried pieces nor proves that every graph-theoretic cold germ is
represented.  The F producer owes the graph-to-row coverage map.  Once a row
is supplied as a `ColdBoundedGerm`, the row-local G1--G3 classifier is total.

CT7 is unnecessary after `contextCoverage`: the finite Boolean scan already
returns either an explicit distinguishing code or equality of every code, and
coverage transports the latter to every literal compatible context.  CT8 is
appropriate upstream when two prefixes repeat the exact normalized state; it
does not by itself prove the packed reconstruction or response-coverage fields
required here.

## Both-sides and leaf table

| Predicate | Positive branch | Negative branch | Consumer |
|---|---|---|---|
| an actual hit is supplied | actual dyadic cycle | scan the fixed response table | CT1 / local scan |
| some row response differs | retain the first exact code and decoded context | all row responses agree | typed G2 / coverage to G3 |
| a target defect has an exit-(4) trigger | exact exit-(4) or existing-ledger route | retain target-defect residual | future typed route / `TargetDefectHandoff` |

| Branch | Local result | Certificate or consumer |
|---|---|---|
| G1 | actual target cycle | C1 through CT1 |
| G2 | exact distinguishing context | typed `TargetDefectHandoff.Residual` |
| G3 | target-complete smaller replacement | C2 through CT3/minimality |

The table is leaf-total only relative to the declared G2 handoff.  Calling G2
closed as exit-(4) without the additional token fields would be proof
injection.

## Lemma ledger

| Required statement | Exact inputs | Status |
|---|---|---|
| G1 executes CT1 on the same cycle | `ColdDyadicHit` | implemented by `g1Run`, `g1_terminal`, `g1_impossible` |
| G2 retains the same distinguishing context | `ColdContextDistinction` | implemented by `routeDistinction` and its exactness theorems |
| G3 executes CT3 and strictly closes by minimality | `ColdSilentExchange` | implemented by `g3Compression`, `g3Run`, `g3_impossible` |
| every supplied table row routes without existential witness loss | `GermTable` and one exact row | implemented in `P13ColdGermTableConsumers` |
| G2 constructs exit-(4) | target defect plus receiver/load/support/update | open; those latter fields are not yet produced |
| every graph-owned F5 germ maps to a supplied table row | completed F1--F5 producer | open upstream |

## Practicality

- The only scan is over `germ.contexts.orderedValues`, the fixed local table.
- CT1 and CT3 terminal consumers each execute one certified local check.
- CT10 work is quadratic in the explicit row-table cardinality.
- No graph, coloring, boundaried-piece, outside-context, or ambient completion
  universe is materialized.

