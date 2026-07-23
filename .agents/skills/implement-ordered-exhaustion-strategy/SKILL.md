---
name: implement-ordered-exhaustion-strategy
description: Implement a reusable Hypostructure ordered-exhaustion strategy over a residual-owned finite schedule. Use for first failures, first receivers, clean prefixes, structural peeling, exact iteration traces, recurrence, and exhaustive all-active terminals in Graph or PDE proofs.
---

# Implement an Ordered Exhaustion Strategy

Take the schedule from a query on the literal predecessor. The framework owns traversal order, first-hit selection, prefix/suffix evidence, ledger growth, and termination.

Define only the local predicate, its decision procedure, and the semantic meaning of each terminal. For recursive peeling, require a proof-carrying strict decrease on every continuation.

Return one registered DAG vertex with exhaustive terminals: first exceptional item with clean-prefix evidence, completed ledger, or exact remaining residual. Include the composed work bound.

Use Graph or PDE adapters only for domain semantics. If Core cannot express the scan or recursion, invoke `extend-hypostructure-framework` and add a reusable backend constructor before application work continues.

Read only the previous residual and accumulated ledger, and keep every terminal exhaustive.
