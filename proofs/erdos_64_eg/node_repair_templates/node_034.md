# Node [34] repair template

Incoming `[32] no`; outgoing `[47]`. Sole responsibility: name Residual B and
record the displayed full-rank inequality `W₂ ≤ rΩ` from the literal no
constructor already produced at node [32]. The current certified finite error
is zero. Core appends this mathematical fact to the one accumulated ledger.
Forbidden: curvature cost [48], entropy, or any Branch-D work.

- `N34-FULL`: `Node34Output.fullRank`; `node34P13FullRankResidual` converts the
  exact node-[32] equality to `W₂ ≤ rΩ` using the inherited exact coordinate
  count.
- `N34-LEDGER`: `Node34FullRankBound` and
  `node34StageEntailsFullRankBound` register the conclusion for later queries
  without a caller-supplied certificate.
- `N34-ROUTE`: `Node34Stage` is the independent framework-owned no
  continuation of node [32]. It is appended after node [33] from the same
  accumulated state without consuming or rebuilding node [33].
- `N34-WORK`: `node34LocalChecks = 0`.
- `N34-RUN`: `runInitialThroughNode34` extends the literal node-[33] runner,
  while the node-[34] executor retrieves node [32] from that ledger.

The listed node-local obligations are kernel-checked. Node [34] owns no
curvature-cost, entropy, support, or Branch-D closure theorem.
