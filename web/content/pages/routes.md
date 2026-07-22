# Routes

A route is a typed transition between CT stages. Its stable identity names the mathematical edge; executable behavior exists only after a `Core.Routing.Profile` supplies discovery, target input, and a real target executor.

## Execution protocol

Registration binds an edge to a typed profile. Discovery computes an enabled seed or disabled residual from the full source stage. The enabled branch builds target input and calls the target capability; `advance` records exact provenance and preserves the complete predecessor ledger.

## Reading route evidence

The route list distinguishes identities from concrete executions. Execution evidence links the transition, public advance, predecessor and root-residual preservation, provenance, and a focused target result.
