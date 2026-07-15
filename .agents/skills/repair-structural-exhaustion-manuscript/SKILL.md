---
name: repair-structural-exhaustion-manuscript
description: Repair a mathematical gap in a structural-exhaustion manuscript by reopening the exact residual branch, selecting finite local invariants with the framework's both-sides test, routing every outcome through CT contracts, and validating the repair in a separate sketch before merging it into the source manuscript. Use for false implications, missing cases, stale branch hypotheses, label/type defects, unconsumed residuals, circular normalizations, or any manuscript node that must be repaired without weakening the theorem or adding an assumption.
---

# Repair Structural-Exhaustion Manuscript

Repair a failed node as a new local residual branch. Preserve the theorem, consume only inherited branch data, and make every leaf return C1--C5 or a typed payload with a declared consumer.

## Non-negotiable rules

- Never repair a gap by weakening the theorem, adding the failed property as a hypothesis, or carrying a `magic assumption` downstream.
- Treat failure of a claimed property as positive structural information. Define the complementary residual and analyze it.
- Reconstruct the directed proof flow. Never infer a node's state by reading prose linearly or by importing facts from a sibling branch.
- Use local, finitely encoded data. Do not materialize a huge graph universe, recurse without a decreasing measure, or replace local bookkeeping by an unsupported global estimate.
- Keep every non-closing output typed. It must have one declared consumer, S-Rout at the producer, S-Trig at the consumer, and inherited-state transport.
- An absent manuscript lemma is a repair obligation, not a request for user input and not a stopping condition. Derive it from the exact branch state, or refine the residual and select a different invariant or route.
- Never end a repair by saying that the user must provide a local lemma, classifier, toggle, bound, or handoff. Proving or replacing precisely those missing statements is the purpose of this skill.
- Do not edit the source manuscript until the separate repair sketch passes the red-team skill.
- Use only the external inputs already authorized for the target proof. A new literature theorem is not a local repair.

## Required reading

Before acting, read `framework/branch_closure_methodology_extended.tex` completely. If it was already read completely in the current task and is unchanged, verify that fact and reread the sections governing the defect. At minimum revisit:

- branch states, the closure alphabet, and the general closure algorithm;
- admission and the bookkeeping-vs-theorem test;
- invariant selection, both-sides test, ladder, granularity, and parameter synthesis;
- selection policy, typed handoffs, and worksheet filling;
- the level-2 repair protocol, level-3 interface review, defect register, and repair taxonomy;
- the CT entries and EG instantiation rows implicated by the proposed route.

Read `references/repair-worksheet.md` before drafting the repair.

## Workflow

### 1. Freeze the defect

Record a defect row before changing mathematical claims:

- stable proof node and exact failed implication;
- smallest verified ancestor state;
- inherited invariants proved independently of the failed statement;
- descendant consumers and blast radius;
- exact residual class created by negating the failed conclusion;
- classification E, D, candidate S, and lowest applicable repair level.

Do not demote the theorem. The defect row describes the open residual while the repair is being developed.

### 2. Reconstruct the complete directed state

Trace every incoming path and outgoing edge in the Chapter 1 flow diagrams and dependency table. Write the active branch as

`B = (H0, order, exits, invariants, residual, vocabulary, queue, artifacts)`.

For every field, cite its producer. Separate inherited facts from facts proved only on other branches. List every excluded exit already accumulated on this path.

### 3. Normalize the failed claim

State the quantifiers literally. Distinguish, in particular:

- injection from surjection or realization;
- pairwise separation from simultaneous realization;
- quotient well-definedness from existence of representatives;
- independent coordinates from a full Boolean cube;
- a local context generator from all global completions.

Negate the exact missing conclusion and extract a canonical finite witness: first missing datum, inclusion-minimal forbidden pattern, first failure, first rank drop, first overloaded fibre, or minimal obstruction. Prove that the selector is deterministic and measurable from the recorded branch state.

### 4. Build the resource inventory

List only resources already available on the residual path: minimality, target algebra, exact types, finite labels, ledgers and remaining capacities, previous closed routes, finite computations, and authorized black boxes. Attach a price list saying exactly what each resource can pay for.

Run the bookkeeping-vs-theorem test. Reject any candidate lemma that restates the original problem globally.

### 5. Select an invariant by the both-sides test

Generate candidates mechanically from hypotheses of the lemmas or CTs you want to use. For each candidate `P`, fill all four fields:

- `P` pays what into which existing account;
- `not P` forces which bounded residual;
- how `P` is computed from the branch state;
- which CT consumes the negative payload.

Reject predicates that merely rename the gap. Prefer the earliest ladder-ready invariant. Keep branches separate whenever payload type, consumer, inherited state, or proof obligation differs.

### 6. Choose and register the CT route

Consume an already queued payload before inventing a fresh route. Match the residual to an existing CT contract and fill S-Def, S-Dich, S-Equiv, S-Pers, S-Det, S-Rout, S-Trig, S-Comp, S-Rest, and S-Meas as applicable.

A finite missing label normally enters CT10; a target-relative dependence enters CT15; a same-interface exchange enters CT7; a response defect enters CT3; a demand/payer failure enters CT4 or CT13. This is a diagnostic ordering, not permission to force the residual into the wrong contract.

If no existing route accepts an expressible residual, perform the methodology's level-3 interface review. Add one reusable producer-consumer contract only after defining the payload, unique consumer, S-Rout, S-Trig, certificates, recovery edges, and transfer example. Extend the data language only after proving a genuine level-4 expressibility gap.

An already-closed branch is an admissible consumer when the repair proves a legal typed handoff to its exact entry state. For every such reuse, prove all of the following:

- the new residual constructs the closed branch's full trigger payload, rather than merely resembling its informal description;
- every invariant read by the consumer is transported from an earlier producer on the current path;
- the consumer closure and all of its dependencies are independent of the failed node and of the proposed repair;
- the dependency order is strictly forward into an already verified subgraph, or a declared cycle carries S-Rest and a strictly decreasing S-Meas;
- the branch table records the handoff and the reused C1--C5 certificate.

Reject a handoff whose consumer proof, normalization, budget, or trigger depends transitively on the node being repaired. That is circularity, even when the destination branch is currently colored verified.

### 7. Derive every missing local lemma autonomously

Treat each unproved implication exposed by the CT worksheet as the next theorem to derive, not as a blocker to report. In particular, if the repair requires a product-or-route classifier, first-failure lemma, toggle, structural blocker, token assignment, persistence theorem, or legal handoff, prove it from the frozen branch state.

Use the following repair loop until the obligation is discharged:

1. Rewrite the desired lemma with all quantifiers and only the inputs actually available at its node.
2. Negate it and extract the least finite counter-witness or first failed local move.
3. Apply the both-sides test to that witness and generate the next invariant from the hypotheses of available CT consumers.
4. Attempt the lowest-level proof using existing Core, Graph, CT, and Routes lemmas.
5. When the attempt fails, record the exact false subimplication and a finite countermodel when one exists; do not ask the user for the missing result.
6. Return to the methodology's selection policy, change the invariant granularity, split the residual further, or route it to a dependency-independent closed branch with an exact trigger.
7. If no existing contract expresses the successful mathematical argument, perform the level-3 interface review and implement the reusable contract, route, certificates, and transfer example.
8. Re-run the complete branch table and red-team audit after every refinement.

Do not preserve a failed candidate as a hypothesis. A countermodel rejects only that candidate implication; it does not demote the theorem. Its complement becomes a new positive structural residual and the repair loop continues.

The loop may stop without a merged repair only after an explicit mathematical impossibility has been proved for the exact incoming branch state and the level-2, level-3, and level-4 methodology audits have shown that no local invariant or expressible payload remains. Mere absence of a lemma from the manuscript or repository never satisfies this condition.

### 8. Draft outside the manuscript

Create a dedicated file under `proofs/<problem>/repairs/`. The sketch must contain:

- the frozen branch state and exact residual definition;
- the canonical selector and all well-definedness lemmas;
- the both-sides table and invariant ladder position;
- CT worksheets and typed payload tuples;
- persistence across every local move;
- a complete branch table whose leaves are C1--C5 or declared handoffs;
- a local computation budget and termination measure where relevant;
- the proposed TeX theorem/lemma statements and matching Lean contracts.

Do not write placeholders such as “standard,” “similarly,” “generic,” or “the remaining cases are finite.” Name and discharge each case.

### 9. Prototype the reusable mathematics

Formalize generic finite logic, graph facts, CT machinery, and routes in Core, Graph, CT, or Routes. Keep problem code to concrete data and thin instantiations. For a new or changed CT contract, add a small non-target example that exercises the same route.

Use proof-carrying local certificates when direct computation is not polynomial in the ambient graph. Verify certificates locally; never enumerate the ambient graph family.

### 10. Red-team before merge

Invoke `$red-team-structural-exhaustion-manuscript-repair` on the sketch. A FAIL verdict blocks source-manuscript edits. Repair the sketch and repeat until every blocking finding is discharged and the verdict is PASS.

### 11. Merge and synchronize

Only after PASS:

1. integrate the settled branch into the original manuscript without changing its theorem;
2. update the Chapter 1 diagram, dependency table, invariant/reverse indexes, branch table, worksheets, payload registry, and defect history;
3. implement or synchronize Lean statements and executions;
4. update web coverage and implementation logs from actual Lean provenance;
5. run focused Lean builds, manuscript checks, web checks, and repository checks.

Do not call a node verified because downstream theorems happen to hold. Verification is node-local: exact predecessor inputs, exact local conclusion, no unproved assumptions, and a compiled proof term.

## Completion report

Report the repaired residual, selected invariant, CT route, closure of both sides, reusable framework changes, red-team verdict, and checks run. Do not ask the user to supply an unfilled schema or missing consumer contract. If an audit exposes one, re-enter step 7 and derive, refine, or replace it. Leave the original manuscript unchanged during those iterations. Only a proved impossibility for the exact branch state after the complete methodology audit may be reported as an unresolved scope obstruction.
