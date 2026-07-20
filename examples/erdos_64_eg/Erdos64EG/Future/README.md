# Unreviewed future proof material

This directory preserves proof code that is not yet in the canonical verified
node prefix. It is not imported by the package root.

Before a module is used by a canonical node, its paper responsibility and
dependencies must be reviewed. Reusable mathematics then moves to `Shared/`
or `FiniteChecks/`; routing and ledger plumbing move to the framework rather
than into an Erdős module.
