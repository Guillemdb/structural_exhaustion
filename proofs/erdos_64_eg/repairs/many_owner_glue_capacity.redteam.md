# Many-owner glue/capacity contract

`Core.DependentOwnerGlueCapacity.Profile` takes an exact finite owner schedule,
dependent local finite types, total glue, component restriction/recovery, and
an injective code on glued objects.  Recovery proves glue injective by
function extensionality; composing with code injectivity proves the dependent
choice-to-code map injective.  Finite cardinality transport then proves
`Nat.card (forall owner, Local owner) <= codes.card`.

The proof never constructs or scans a Cartesian list.  The dependent function
type occurs only in a cardinality theorem.  No Erdős graph interpretation,
commutation, target semantics, or skeleton producer is inferred.

Verdict: **PASS for the reusable capacity layer; no claim about the missing
Erdős producer.**  Focused Lean compilation passes.
