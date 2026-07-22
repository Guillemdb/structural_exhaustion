# PDE

The PDE layer represents local analytic arguments through the same Core execution model. It owns atlases, equations, observables, representation semantics, coordinates, local-tail assembly, quotients, and fast-track registration.

## Models and atlases

A `LocalModel` combines a Core problem, local atlas, and represented equation. Targets and optional analytic capabilities are registered independently.

## Representations and observables

Representation semantics make equality, gauge equivalence, or another quotient explicit. Observable interfaces expose exactly the finite or represented data that a CT may inspect.

## Coordinates and assembly

Recentring, rescaling, restriction, normalization, and gauge changes are primitive actions. Local-tail laws let Core reconstruct global statements without application-owned gluing.

## Fast-track execution

A minimal `FastTrack.Signature` registers only representation semantics, observables, observable invariance, and the target interface. Generator/form data, represented quotients, framework-computed defects, compact extraction, resources, carriers, and budgets are independent optional capabilities. Register a capability only when the next row or CT consumes it. CT adapters compute finite classifications and typed residuals; every analytic estimate remains an explicit named theorem input.
