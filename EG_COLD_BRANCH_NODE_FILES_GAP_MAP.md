# EG Cold Branch NodeX File Gap Map

This document is limited to the cold-branch `NodeX.lean` files in
`examples/erdos_64_eg/Erdos64EG`.  It does not use shared modules or other
written material as requirements.  Shared declarations named here appear only
because a `NodeX.lean` file imports or calls them.

The goal is to identify what the current Hypostructure framework must provide
so these node files can be reimplemented as thin framework-native nodes using
only the previous residual and ledger.

## Node Files Covered

- `Node148.lean`
- `Node149.lean`
- `Node150.lean`
- `Node151.lean`
- `Node152.lean`
- `Node153.lean`
- `Node154.lean`
- `Node155.lean`
- `Node156.lean`
- `Node157.lean`
- `Node158.lean`
- `Node159.lean`
- `Node160.lean`
- `Node161.lean`
- `Node162.lean`
- `Node163.lean`
- `Node164.lean`

## Node-by-Node Feature Map

| Node | What the old node file does | Framework feature needed |
|---:|---|---|
| 148 | Focuses the node-146 no leaf, computes total/hot/cold demand, compares it to an allowance, and splits into cap/failure branches. | Generic focused numeric-cap decision over predecessor-owned quantities; problem constants read from contract; generated yes/no residuals. |
| 149 | Consumes the yes edge of node 148 and maps it to a terminal density-cap marker. | Proof-only terminal continuation for a previously decided branch; metadata for no new work. |
| 150 | Consumes the no edge of node 148 and exposes the cold-window count as a residual fact. | Residual-owned selected-subschedule query and count projection; no custom output object. |
| 151 | Filters cold windows into ambient-cubic and non-cubic lists; proves lossless partition, nodup facts, and surplus payment for discarded non-cubic windows. | Generic finite predicate filter with retained/discarded subfamilies, exact partition theorem, nodup preservation, and resource-payment ledger. |
| 152 | For retained ambient-cubic windows, builds a flattened branch-excess stub schedule and proves exact length bounds. | Dependent schedule flattening over predecessor-owned retained windows; exact per-entry contribution theorem; ledger-registered flattened schedule. |
| 153 | Builds a corridor producer from the current graph facts and runs a first-failure scan for every scheduled stub. | CT6/Graph corridor executor over a residual-owned stub schedule; graph-owned corridor producer read from ledger. |
| 154 | Splits the first-failure outputs into G1-hit and no-G1 branches. | Generic first-hit splitter over scheduled CT6 outputs; no application-owned route selection. |
| 155 | Closes the G1 branch by extracting a dyadic-cycle certificate and contradicting the inherited counterexample avoidance. | Core closure adapter for target-hit contradiction; Graph target-hit-to-target bridge. |
| 156 | Splits the no-G1 branch into G2 event and G3 silent residual; also exposes a G2 hot-handoff continuation. | Secondary event splitter plus framework-owned handoff route preserving accumulated ledger. |
| 157 | On G3, records that every scheduled entry has the silent/germ outcome. | Schedule-wide silent-outcome ledger query; framework-owned germ residual extraction. |
| 158 | Splits each germ by bounded same-interface scale and records bounded output. | Generic bounded-vs-long local support split, likely CT17/Core scale routing. |
| 159 | Builds CT3 coordinates, candidates, responses, admissibility, strict-smaller predicate, capability, input, run, and work bound for bounded G3 entries. | Graph same-interface CT3 constructor that derives spec/capability/input from the residual; no node-local CT3 table plumbing. |
| 160 | Splits CT3 runs into all-good terminals versus existence of a CT3 residual. | CT3 all-good-or-first-residual splitter over a finite schedule. |
| 161 | Extracts compression-style witnesses from good CT3 terminals: either compression candidate or known-row match. | CT3 public good-terminal witness query with a common replacement-witness interface. |
| 162 | Extracts exact CT3 residual objects for distinguishing-context or novel-row terminals. | CT3 residual query indexed by terminal plus framework-owned downstream route. |
| 163 | Converts good CT3 witnesses into finite same-interface replacement data and target-complete response table evidence. | Graph finite same-interface replacement API and CT3-to-replacement bridge. |
| 164 | Retrieves the finite same-interface replacement package from the node-163 ledger. | Generic ledger retrieval query for registered same-interface replacements. |

## Features Still Missing From Hypostructure

1. **Focused numeric-cap decision**

   Needed by `Node148.lean`.  It should take only predecessor residual queries
   and contract-provided constants, then emit framework-owned yes/no branches.
   Implemented as `Hypostructure.Core.Residual.NumericCap`: the framework
   consumes active ledger queries, performs the counted comparison, preserves
   the predecessor, and derives successor focuses.

2. **Proof-only branch terminal**

   Needed by `Node149.lean` and later terminal wrappers.  It should preserve
   the predecessor residual and record zero additional work.
   Implemented as `Hypostructure.Core.Residual.Terminal`.

3. **Selected finite subschedule residual**

   Needed by `Node150.lean`, `Node151.lean`, and downstream cold nodes.  The
   node should read a selected schedule from the ledger, not rebuild a list.
   Implemented as `Hypostructure.Core.Finite.SelectedSchedule`: the framework
   registers the predecessor-owned schedule, exact cardinality, exact schedule
   equality, membership transfer, and an attached member schedule for downstream
   graph/PDE construction.

4. **Finite predicate filter with resource payment**

   Needed by `Node151.lean`.  It should produce retained/discarded residual
   branches, partition evidence, nodup preservation, and payment of discarded
   entries by a ledger resource.
   Implemented at the abstract schedule level as
   `Hypostructure.Core.Finite.Partition`; the resource payment is a contract
   law over the rejected exact schedule.

5. **Dependent schedule flattening**

   Needed by `Node152.lean`.  It should flatten per-window branch-excess stubs
   into one residual-owned schedule with exact count evidence.
   Implemented as `Hypostructure.Core.Finite.Flatten`.

6. **Graph corridor CT6 executor**

   Needed by `Node153.lean`.  It should construct and run the corridor
   first-failure scan from graph facts already in the ledger.
   Implemented with Core ownership in
   `Hypostructure.Core.Finite.ScheduleEvents.focusedFromQueries`, which owns
   the residual schedule scan, hit/no-hit split, branch certificate, and
   downstream query surface.  The graph specialization is
   `Hypostructure.Graph.InducedPathCold.focusedCorridorEvents`; it supplies
   only graph-typed stage outputs.  The PDE specialization is
   `Hypostructure.PDE.CT6.focusedScheduleEvents`; it supplies only a represented
   state, local packets, and event predicates.  Fixtures now exercise both
   specializations through the same Core executor.

7. **First-hit / all-absent splitter**

   Needed by `Node154.lean`.  It should split a finite schedule of outcomes
   into first hit or universal no-hit residual.
   Implemented generically as `Hypostructure.Core.Finite.ScheduleEvents`.

8. **Target-hit closure bridge**

   Needed by `Node155.lean`.  It should turn the graph target hit into the
   current target predicate and close against the inherited avoiding context.
   Implemented as `Hypostructure.Core.Closure.closeTargetHit` with thin graph
   and PDE bridges in `Hypostructure.Graph.TargetClosure` and
   `Hypostructure.PDE.TargetClosure`.

9. **Secondary event/handoff splitter**

   Needed by `Node156.lean`.  G2 must route through framework-owned routing,
   not a hand-written handoff output.
   Implemented as `Hypostructure.Core.Finite.ScheduleEventRoute`: the event-hit
   branch is converted into a Core-owned route seed containing the exact item,
   schedule membership, runner output, and event proof, and Core routing owns
   the downstream enabled/disabled handoff.

10. **Silent/germ residual extraction**

   Needed by `Node157.lean`.  It should expose all scheduled silent outcomes as
   ledger data.
   Implemented at the abstract event-refinement level as
   `Hypostructure.Core.Finite.ScheduleEvents`.

11. **Bounded-vs-long scale routing**

   Needed by `Node158.lean`.  The framework should own the split and any scale
   arithmetic; node code should only instantiate parameters.
   Implemented as `Hypostructure.Core.Finite.ScaleRoute`.

12. **Same-interface CT3 constructor**

   Needed by `Node159.lean`.  It should derive CT3 coordinates, candidates,
   response, admissibility, strict-smaller facts, capability, input, run, and
   work from a bounded corridor residual.
   Implemented at the CT3/framework level as
   `Hypostructure.CT3.RunSchedule`: the framework consumes an already
   registered CT3 spec/capability, a residual-owned item schedule, and an
   item-to-input ledger query, then runs CT3 for every item and exposes the
   derived terminal schedule for the existing CT3 schedule classifier.  Its
   `runClassified` entry point performs the whole scheduled-run plus
   all-good/first-residual classification step without requiring applications
   to thread the intermediate contract.  Graph and PDE expose only thin
   adapters, `Hypostructure.Graph.CT3.runFocusedClassified` and
   `Hypostructure.PDE.CT3.runFocusedClassified`; neither adapter constructs
   response tables, selects routes, copies outputs, or introduces
   problem-specific state.

13. **CT3 terminal classifier**

   Needed by `Node160.lean`.  It should classify scheduled CT3 runs into all
   good terminals or a first exact residual.
   Implemented as `Hypostructure.CT3.Schedule`.

14. **CT3 good-terminal witness query**

   Needed by `Node161.lean`.  It should expose compression and known-row
   terminals through one replacement-witness interface.
   Implemented by `Hypostructure.CT3.ScheduleWitness` and
   `Hypostructure.CT3.SameInterface`: CT3 exposes framework-owned good witness
   queries on the all-good branch and uses them to register same-interface
   packages without graph/PDE applications selecting or copying terminal
   payloads.  The `PackageContract.registerClassified` executor composes CT3
   schedule classification with same-interface package registration directly,
   and Graph/PDE expose only forwarding adapters for that CT3-owned operation.

15. **CT3 residual query and route**

   Needed by `Node162.lean`.  It should retrieve distinguishing-context and
   novel-row residuals and route them without copying outputs.
   Implemented at the CT3/framework level by `Hypostructure.CT3.Schedule`,
   `Hypostructure.CT3.ScheduleWitness`, and
   `Hypostructure.CT3.ResidualRoute`: CT3 selects the exact first residual
   item, terminal, and witness from the residual ledger, then Core routing
   enables the downstream transition from that CT3-owned seed.  The
   `ResidualRoute.Contract.advanceClassified` executor composes CT3 schedule
   classification with first-residual routing directly; Graph/PDE expose only
   forwarding adapters for this CT3/Core-owned operation.

16. **Finite same-interface replacement API**

   Needed by `Node163.lean`.  It should package representatives, boundary
   compatibility, response tables, and target-complete evidence generically.
   Implemented in Core as `Hypostructure.Core.Response.SameInterface`:
   `VerifiedPackage` is the standard proof-carrying package shape and
   `VerifiedContract` registers item-indexed verified packages through the
   same focused ledger machinery used by graph and PDE applications.  CT3's
   same-interface bridge now calls that Core registration after the all-good
   branch is selected, so applications no longer manually run package
   registration after classification.

17. **Same-interface replacement ledger retrieval**

   Needed by `Node164.lean`.  It should retrieve the registered replacement
   package as a framework-owned ledger query.
   Implemented by `Hypostructure.Core.Response.SameInterface.Contract` and
   `VerifiedContract`: the framework exposes latest package retrieval, exact
   package-query equality, selected-package retrieval, and direct
   boundary-compatible/same-response/target-complete proof queries for verified
   packages.

## Porting Implication

The current cold-branch `NodeX.lean` files are not just thin applications of
CT3/CT6.  They manually perform filtering, schedule construction, branch
routing, CT3 table construction, witness extraction, and ledger retrieval.
Those are exactly the pieces that must move into Hypostructure before the
cold branch can be ported without custom state, copied outputs, or custom
handoffs.
