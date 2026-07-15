---
name: red-team-structural-exhaustion-manuscript-repair
description: Adversarially audit a proposed structural-exhaustion manuscript repair before it is merged. Use to test a repair sketch for quantifier errors, branch leakage, circular normalizations, injection-versus-realization mistakes, hidden assumptions, incomplete CT routes, nonlocal computation, missing persistence or termination, TeX--Lean mismatch, and any branch leaf that lacks a C1--C5 certificate or typed consumer.
---

# Red-Team Structural-Exhaustion Manuscript Repair

Assume the proposed repair is wrong until every claim is supported by the exact incoming branch state and every residual has a local, typed, terminating route.

## Independence and authority

- Audit the separate repair sketch, not a summary of it.
- Read the implicated manuscript sections, Chapter 1 flow diagrams, current Lean contracts, and `framework/branch_closure_methodology_extended.tex` repair rules.
- Read `references/red-team-checklist.md` and fill it explicitly.
- Do not edit the original manuscript or declare a merge ready while any blocking finding remains.
- You may repair the sketch and generic/prototype code, then rerun the audit. The final verdict must apply to the resulting files, not an earlier draft.
- A blocking missing lemma is an internal repair task, not a request for user input. Hand it immediately back into the repair methodology, derive or replace it, and audit the resulting branch again.

## Audit workflow

### 1. Reconstruct provenance independently

Trace all incoming branch paths to the repaired node. Rebuild the branch-state tuple and compare it field by field with the sketch. Reject facts derived later, facts belonging to sibling branches, and facts whose producer depends on the failed claim.

Check all outgoing edges. The repair must cover the complete node/CT block, including side branches and handoffs, rather than only the manuscript's next paragraph.

### 2. Attack the quantifiers

Rewrite every central claim with explicit domains, codomains, witnesses, and dependency order. Look specifically for:

- injective quotient maps presented as realization of all states;
- pairwise witnesses presented as one simultaneous witness;
- `for every coordinate there exists a state` exchanged with `there exists a state for every coordinate`;
- context equivalence checked on a subset presented as all contexts;
- quotient representatives assumed to exist or be compatible;
- rank independence presented as a full Boolean cube;
- existential local objects used canonically without a tie-break.

Construct the smallest finite countermodel compatible with the stated hypotheses whenever possible. A countermodel to an intermediate implication is blocking even if downstream conclusions are plausible.

### 3. Audit the residual, not an added assumption

Confirm that failure of the disputed property creates a defined residual branch. Reject repairs that:

- weaken or condition the main theorem;
- add the missing property to the standing hypotheses;
- rename the failed conclusion as an invariant;
- leave the negative side with no bounded witness or consumer;
- silently discard the residual because another branch closes elsewhere.

Run the both-sides test. Both sides must make strict recorded progress and use resources available before the split.

### 4. Audit every CT contract

For each invocation, check its exact trigger and all applicable schema obligations. Verify:

- S-Def objects are finite/measurable and actually available;
- S-Dich alternatives are exhaustive and disjoint where required;
- S-Equiv covers every compatible target-relevant context;
- S-Pers transports the whole inherited branch state;
- S-Det records all tie-breaks;
- S-Rout payload fields match the registry;
- S-Trig follows from the payload without an extra hypothesis;
- S-Comp uses the same currencies and units;
- S-Rest restores the state expected at re-entry;
- S-Meas strictly decreases on every non-closing cycle.

Reject an interface-changing payload until its unique consumer and producer/consumer obligations are registered at framework level.

For a handoff into an already-closed branch, independently compute the consumer's transitive dependencies. Verify exact trigger implication, inherited-state transport, S-Rout, S-Trig, and that no dependency path returns to the failed node or to a lemma whose proof uses the proposed repair. A verified color or manuscript claim is not evidence of acyclicity. If the handoff is intentionally cyclic, require S-Rest and a strict S-Meas decrease on every return.

### 5. Audit leaf totality and practicality

Enumerate the repair's branch table. Each leaf must be C1--C5 or a typed handoff whose consumer is already admitted. “Finite cases remain,” “route later,” and an open worksheet are failures.

Inspect the execution model. Reject:

- enumeration of all ambient graphs or all unbounded completions;
- an exponential search whose parameter is not a fixed/local interface;
- recursion without a recorded natural measure;
- a global density/entropy theorem smuggled in as bookkeeping;
- a certificate whose checker must redo the full search.

Accept finite local tables and proof-carrying certificates when their size and checker cost are explicit and practical.

### 6. Audit formal correspondence

Compare TeX statements with Lean declarations literally. Check theorem hypotheses, universe, graph finiteness/simplicity assumptions, branch-state inputs, conclusion strength, and trust base. Search for `axiom`, `sorry`, `admit`, `Classical.choice` hiding data, or a problem-specific lemma that belongs in Core/Graph/CT/Routes.

The only allowed external theorem for the Erdős--Gyárfás proof is its registered HSS interface. Any other unproved mathematical input is blocking.

### 7. Issue a verdict

Classify findings as:

- **Blocking:** mathematical falsehood, missing branch, unproved schema, hidden assumption, nonterminating/nonlocal computation, or TeX--Lean mismatch.
- **Required cleanup:** artifact or abstraction defect that would make provenance incomplete.
- **Advisory:** readability or organization with no effect on correctness.

Return **PASS** only when there are no blocking or required-cleanup findings, all focused checks pass, and the source manuscript is still unchanged from the pre-sketch baseline. Otherwise record **FAIL** in the audit artifact, name the first exact failing obligation, and invoke the repair loop on that obligation. Do not present “prove this missing lemma” to the user as the completed result.

## Iteration rule

On FAIL, fix only the sketch and reusable prototype layers, then rerun the complete audit. Do not carry a finding as an assumption. Do not merge a partially audited repair. Record countermodels and failed attempts in the defect history so later agents do not repeat them. If the proposed lemma is false, negate it, reopen the resulting structural residual, and return to invariant selection; do not stop at the countermodel. Continue repair--audit iterations until PASS or until the repair skill has proved a genuine methodology-level scope obstruction for the exact branch state.
