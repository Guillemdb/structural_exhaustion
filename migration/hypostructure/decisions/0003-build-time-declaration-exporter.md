# HYP-0003: Build-time declaration exporter boundary

Status: implemented

Date: 2026-07-21

Checker surface: `Hypostructure.Canonical.WebExport`

## Context

The web declaration exporter must inspect one compiled environment containing
Core, CT1--CT17, Routes, Graph, PDE, and the Navier--Stokes specialization. It
also needs Lean's metaprogramming API to inspect declarations and emit JSON.
Those dependencies would be domain inversions in mathematical production
modules, but the exporter is a build-time top-level consumer rather than a
producer in any mathematical layer.

## Decision

The import firewall recognizes exactly
`hypostructure/Hypostructure/Canonical/WebExport.lean` as a build-time
exporter. Only that path may import the `Hypostructure` umbrella and modules
under `Lean`. The exception is based on the complete repository-relative path;
it does not apply to the `Canonical` directory, the `WebExport` filename, or
any framework layer generally.

The exporter remains in the production scan. Admission checks and prohibitions
on legacy, generated, parity, application, and unrelated external imports run
unchanged. The exception therefore grants environment inspection, not a new
mathematical trust boundary.

## Verification

Focused tests establish that the exact exporter can load the compiled
environment, while an adjacent Canonical module and a same-named Graph module
cannot import either the umbrella or `Lean`. Further negative coverage proves
that generated sources, application modules, unrelated external modules, and
authored axioms remain forbidden inside the exporter itself.

## Consequences

No Core, CT, Routes, Graph, PDE, Canonical, fixture, or application import rule
is weakened. Any future build-time consumer requires a separate explicit path
and review rather than inheriting this exception by directory or naming
convention.
