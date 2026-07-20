# Node [33] repair template

Incoming `[32] yes`; outgoing `[35]`. Sole responsibility: name Branch D by
selecting the literal yes constructor already produced at node [32]. The local
output is `PUnit`; the strict admitted-rank-loss proof remains only in node
[32]'s framework decision carrier and is not copied into node [33]. **Do not
reuse** `VerifiedP13Node32RankDecision.node33`: it uses `False.elim
(no_p13CanonicalCurvature_rankDrop ...)` and illegally closes the live branch.
Forbidden: circuit extraction (node [35]), context validity, or contradiction.

- `N33-BRANCH`: `Node33Output := PUnit`; `node33P13RankReducingBranch`
  selects and names the existing node-[32] yes constructor without proving or
  copying any new mathematics.
- `N33-ROUTE`: `Node33Stage` is the framework-owned active-cursor yes
  continuation; the outer bypass and node-[32] no constructor are unchanged.
- `N33-WORK`: `node33LocalChecks = 0`.
- `N33-RUN`: `runInitialThroughNode33` runs from the literal
  `runInitialThroughNode32` accumulated state.

Every listed obligation is kernel-checked, conditional. Node [33] remains
yellow solely because its incoming ledger depends on
the accumulated node-[21] framework ledger and `Node23DenseWindowQuietBlockInput`. Its local
producer showed no `sorryAx`. Node [33] has no support-localization or closure
obligation.
