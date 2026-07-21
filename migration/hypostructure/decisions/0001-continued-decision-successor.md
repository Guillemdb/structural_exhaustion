# HYP-0001: Successor of a continued binary decision

Status: implemented

Date: 2026-07-21

Matrix rows: `core.continued-decision`, EG node 5

## Missing Use Case

`Core.Residual.Decision.continueYes` and `continueNo` could add the first
payload to one arm of a binary decision, but the resulting continuation had no
framework-owned successor operation.  EG node 5 must consume the exact
minimal-counterexample payload already attached on node 4's yes arm, append a
rooted-return certificate on that same arm, retain the target sibling, and
retain the complete node-4 ledger.  Implementing this by matching on the
continuation in the EG application would make routing and output construction
application-owned.

The same shape occurs in PDE row chains when one arm of a quotient, sign, or
geometry decision receives another certified row while the complementary arm
remains present for a later consumer.

## Ownership

The operation belongs to Core.  Its statement mentions only a dependent
binary decision, its current arm-indexed payloads, successor payload families,
and a ledger extension.  It contains no graph, cycle, PDE, quotient, or target
semantics.  Graph owns only the rooted-return certificate used by EG node 5;
the EG application supplies only that graph-level instantiation.

## Public Author Inputs

The caller supplies:

- the literal `ContinuationStage` predecessor;
- a local dependent computation from the current yes payload to the next yes
  payload;
- optionally, the symmetric computation on the no arm.

For the one-arm helpers, the untouched arm receives `PUnit`; no mathematical
claim or copied prior payload is supplied for it.

## Framework Outputs

Core constructs:

- the branch-indexed `ContinuationSuccessor`;
- the correct yes or no constructor after inspecting the current
  continuation;
- one `Ledger.Extension` whose predecessor is definitionally the complete
  incoming continuation stage;
- one-arm specializations that preserve the complementary arm without asking
  the application to route it.

The prior payload is an index of the new result and remains stored only in the
literal predecessor.  It is not copied into the new ledger entry.

## Residual Branches

- Yes arm: Core invokes the registered yes computation and emits its exact
  dependent successor.
- No arm: Core invokes the registered no computation, or emits `PUnit` for
  `continueYesBranch`.
- The symmetric `continueNoBranch` treats the yes arm analogously.

Neither branch is discarded.  Later consumers receive the whole successor
stage and use another framework continuation or closure operation.

## Both-Sides Test

Graph interpretation: EG node 5 advances node 4's minimal-counterexample arm
with `Graph.RootedReturnTargetAlgebra.AvoidanceCertificate`; the official
target arm remains in the predecessor tree.

Neutral/PDE interpretation: `Hypostructure.Fixtures.Decision` advances a
natural-number decision twice, reads the first payload in the second
computation, and proves exact predecessor and root-residual retention.  The
types are the same ones needed when a PDE quotient or sign branch receives a
later row certificate.

## Fixtures

- `Hypostructure.Fixtures.Decision.second_retains_first` checks literal
  predecessor retention.
- `second_retains_root_residual` checks the stable residual through both
  extensions.
- Positive and complementary root propositions are checked independently.
- EG node 5 kernel-checks the graph use with no application branch match.
- The production import/admission firewall checks constructor ownership and
  rejects application handoff or route declarations.

## Compatibility Impact

This adds a new Core capability and does not change an existing result type.
It removes the need to reproduce legacy `mapYesStage`-style plumbing in the EG
application.  No legacy module is imported, no compatibility alias is added,
and no assumption or external axiom is introduced.  Axiom audits remain within
`propext`, `Classical.choice`, and `Quot.sound` where Mathlib requires them.
The parity baseline remains unfrozen; node 5 is therefore only `typechecked`,
not `parity_checked` or `migrated_closed`.
