---
name: implement-hypostructure-ct1
description: Implement Hypostructure CT1 target realization or exact target avoidance. Use for residual-owned finite candidate scans, proof-carrying target certificates, focused-branch certificates, graph cycle or rooted-return witnesses, C1 terminals, and target-avoidance residuals.
---

# Implement Hypostructure CT1

Use CT1 to validate an explicit target witness or exhaust an exact finite candidate schedule already owned by the incoming residual. Never turn CT1 into a search over ambient objects.

## Gate the live contract

1. Read row `ct.ct1` in `migration/hypostructure/api-feature-matrix.csv`.
2. Read `hypostructure/Hypostructure/CT1/{Spec,Capability,State,Search,Execution,Theorems,Automation}.lean`. Read `Certificate.lean` or `FocusedCertificate.lean` when using those modes.
3. Inspect `hypostructure/Hypostructure/Graph/CT1.lean` and `hypostructure/Hypostructure/Fixtures/CT1.lean` when relevant.
4. Confirm the declarations elaborate and their `.olean` files are fresh, for example with `cd hypostructure && lake env lean Hypostructure/Fixtures/CT1.lean`. Treat the matrix as reviewed status, not a substitute for live source and kernel evidence.

The finite, certificate, focused-certificate, and Graph surfaces are currently implemented. No `Hypostructure/PDE/CT1.lean` adapter currently exists. Recheck the live tree before relying on that statement.

If the required surface is absent, stale, not kernel-checked, or missing a complementary branch, do not emulate it in an application. Route the framework work to `$extend-hypostructure-framework` and resume only after the vertical slice and fixtures exist.

## Choose the smallest execution surface

- Use `CT1.Spec` and `CT1.Capability` for genuine finite discovery. Supply `Candidate`, `Realizes`, a `Core.Residual.Query` returning the exact candidate schedule, a primitive realization decider, and a polynomial work proof.
- Use `CT1.CertificateEncoding` when the proof already yields one proof-carrying code. Supply `Code`, `Accepts`, `encode`, `decode`, and `acceptsDecidable`; do not invent a code enumeration. `executePublicTarget` validates one code on the C1 arm and performs zero code checks on the avoiding arm.
- Use `CT1.FocusedCertificateEncoding.Encoding` when code and target are meaningful only under a `Core.Residual.Focus.Profile`. Let CT1 totalize and run the dependent family; do not add payloads to inactive siblings.
- Use `CT1.TargetBridge` only to identify the exact queried schedule target with an independently named public target.
- For graphs, prefer `Graph.CT1.cycleSpec`, `cycleCapability`, `cycleTargetBridge`, or `rootedReturnEncoding`. Use `focusedRootedReturnEncoding` only on an existing Core focus.

## Respect the author boundary

Treat target semantics, certificate encoding/decoding, primitive deciders, the exact schedule query, and its work bound as author primitives. Obtain the schedule from the literal predecessor with `Core.Residual.Query.residual`, `latest`, `preserve`, `map`, or a composed typed query.

Let CT1 generate the first hit or exhaustive avoidance, terminal, route, accumulated stage, typed trace, exact check count, semantic claim, and successor. In `Core.Provision` metadata, classify primitive definitions and laws as author inputs, query reads as inferred predecessor dependencies, and the search result, outcome, trace, and residual stage as framework outputs.

Never define a node-local subtype, image, chosen representative family, or replacement candidate carrier. If the incoming ledger cannot expose the intended candidates, add a general Core query/profile rather than manufacturing application data.

## Execute and discharge every obligation

1. Run `CT1.execute`, `executePublicTarget`, or the focused executor on the literal predecessor.
2. Retain the complete `stage`; prove `stage.previous` is the exact input.
3. Pin the generated terminal: `.c1` or `.avoiding`. For certificate mode, use `closeC1ContinueAvoiding` only to discharge an impossible C1 arm while retaining its decision stage.
4. Prove semantic soundness with `ExecutionResult.verified` or the certificate-mode equivalent, exact tracing with `trace_exact`, totality with `run_total` or `runPublicTarget_total`, terminal exhaustiveness, determinism, and the applicable schedule/polynomial work theorem.
5. Decode the public target only from generated accepted evidence; consume exact avoidance from the generated avoiding evidence.

Use `Fixtures/CT1.lean` as the minimum standard: exercise finite hit and miss, proof-carrying hit and avoidance, exact checks and traces, predecessor retention, K4 cycle validation, and rooted-return decoding. Add an application fixture without weakening these neutral and Graph fixtures.

## Practicality gate

Scan only a proof-specified local schedule whose cardinality has a declared polynomial envelope. Reject schedules of all graphs, subgraphs, colorings, walks, or ambient completions. Prefer a proof-carrying certificate whenever discovery is not part of the mathematics.
