# HYP-0007: Registered atom response coordinates

Status: implemented

Date: 2026-07-21

Matrix rows: `graph.atom-response-coordinates`, EG node 12

## Missing Use Case

The original Node 12 theorem quantifies over a proper boundaried atom, an
arbitrary collection of its local target-response coordinates, and two
coordinates identified in a target-complete quotient. Graph previously had
literal boundary pieces and target completeness, but no typed bridge attaching
arbitrary response coordinates to the exact atom profile registered at Node
11.

The first draft restricted every coordinate to a represented boundary piece.
That did not cover the original examples of trace lengths, rooted-return tests,
curvature tests, and other marked data. The implemented contract therefore
uses an arbitrary carrier with literal all-context target semantics.

## Ownership

The bridge belongs to Graph. Its semantics are a proper boundaried atom, the
immutable boundary-degree fibre, finite outside contexts, and graph target
response. Core owns only the later proof projection, counted focus selection,
and ledger extension.

## Public Author Inputs

- The exact `BoundariedAtomProfileCertificate` read from the predecessor
  registration.
- An arbitrary coordinate type.
- A boundary profile and all-context target realization for each coordinate.
- One proof per coordinate that its profile lies in the exact registered
  fibre.
- The graph target already registered by the problem.

Node 12 quantifies over any quotient and its target-completeness certificate,
exactly as the original lemma does. The application does not implement a
particular quotient, copy profile data, route a branch, or prove the
context-universality conclusion.

## Framework Outputs

- Profile preservation for every identification, derived from the registered
  fibre laws.
- Context-universality for every identification in any certified
  target-complete quotient.
- The exact-response setoid and canonical maximal target-complete quotient.
- A represented-boundary-piece specialization when that stronger model is
  appropriate.

## Residual Branches

This is a representation and theorem layer, not a decision. A valid
target-complete identification projects to context universality. Cross-profile
states cannot inhabit the same registered coordinate system; Node 11's
separate generic theorem rejects attempts to identify such supports.

## Both-Sides Test

The Graph fixture attaches terminal-trace, rooted-return, and curvature-test
coordinates to one registered proper atom without making the coordinate type a
graph-piece type. All three carry their exact registered profile and literal
all-context semantics. The framework constructs the canonical quotient and
projects one nontrivial identification.

There is no PDE interpretation of a graph boundary piece. Core's generic
proof-projection executor supplies cross-domain reuse of the downstream node
shape without moving graph vocabulary into Core.

## Fixtures

- An arbitrary heterogeneous coordinate carrier tied to the registered
  profile certificate.
- Distinct identified coordinates with universal context response.
- Profile equality derived from the registration rather than copied data.
- Canonical quotient construction with no caller-authored setoid.
- Public axiom audits within the standard Mathlib trust footprint.

## Compatibility Impact

This is an additive Graph API. EG Node 12 can now state the exact original
coordinate theorem while consuming only the literal Node 11 registration.
Legacy response-coordinate structures remain parity evidence and are not
imported or adapted into production.
