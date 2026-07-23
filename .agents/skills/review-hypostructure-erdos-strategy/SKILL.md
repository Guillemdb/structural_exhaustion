---
name: review-hypostructure-erdos-strategy
description: Audit an existing node-free Erdős--Gyárfás Hypostructure strategy DAG. Use to verify paper parity, literal residual and ledger provenance, registered vertices, exhaustive branch terminals, `problemDefinition` reports, work bounds, imports, and kernel trust without advancing the proof.
---

# Review an Erdős--Gyárfás Strategy

Reconstruct the reviewed paper block from the frozen source, then inspect the strategy DAG independently.

Reject node imports, detached payloads, manual routing, hardcoded outcomes, application-side ledger reconstruction, EG-specific Core declarations, and claims of unconditional closure based only on compilation.

For each composed strategy, verify the literal predecessor, residual queries, exhaustive terminal family, branch join, target certificate, remaining residual, and composed work evidence. Confirm the output matches the paper's mathematical alternatives.

Run the focused build and inspect `problemDefinition.result` and `problemDefinition.report`. Report findings by severity and do not extend the strategy frontier during review.
