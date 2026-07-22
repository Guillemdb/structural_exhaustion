# Hypostructure NS2D Row 1-12 Automation Design

Status: design target for the represented 2D Navier-Stokes global regularity
automation. This document stops at fast-track row 12. Rows 13 and later are
out of scope for this automation pass.

## Objective

Build one public-facing 2D Navier-Stokes contract from which Hypostructure can
automatically run rows 1 through 12 over a single accumulated residual and
ledger. The application supplies only primitive PDE data and row-local analytic
contracts. The framework derives coordinate changes, recentering, gauge
updates, local/tail gluing, CT execution, routing, ledger extension, and work
budgets.

The target theorem exposed by the application is pointwise local regularity on
the registered 2D Navier-Stokes atlas, followed by framework-owned
local-to-global assembly over the atlas cover. The row-1-to-row-12 automation
does not enumerate spacetime points or continuum objects.

## Non-Negotiable API Rule

The public implementation may contain hardcoded mathematical constants only in
the problem contract. Every row executor must read constants through that
contract or derive them from earlier ledger entries. No row module, packet, or
example may manually compose CTs, copy predecessor outputs, construct a route,
or install a detached ledger extension.

Allowed public inputs:

- the 2D Navier-Stokes represented model;
- the local atlas and target predicate;
- primitive observables and budgets;
- finite residual-owned schedules where a CT requires a finite scan;
- analytic contracts, named exactly, with trust status;
- numeric thresholds, exponents, capacities, and constants, only as fields of
  the problem contract.

Forbidden public inputs:

- CT execution results;
- selected branches;
- copied row outputs;
- route enums or custom handoffs;
- manually built local pressure tails, gauge quotients, or compact descendants;
- work coefficients or degrees not derived by the framework.

## Public Contract Shape

The public 2D contract should be a single record with small subcontracts. This
keeps all theorem-specific constants in one public object while preserving
minimal row APIs.

```lean
structure NS2DGlobalRegularityContract where
  model : PDE.LocalModel
  target : model.problem.Ambient -> Prop
  representation : PDE.RepresentationSemantics model
  targetInvariant : Core.TargetInvariant representation target
  atlasCover : PDE.LocalClosureAssembly.Cover model target
  observables : PDE.ObservableInterface model
  coordinates : PDE.CoordinateModel model
  localTail : PDE.LocalTailAssembly.Contract model
  generatorForm : PDE.GeneratorForm.Contract model
  resourceBudget : PDE.ResourceBudget.Contract model
  quotientDefect : PDE.RepresentedQuotient.Contract model
  structuralGradient : PDE.StructuralGradient.Contract model
  defectGeometry : PDE.DefectGeometry.Contract model
  capacity : PDE.CapacityProfile.Contract model
  exactResponse : PDE.ExactResponseCoverage.Contract model
  profileFamily : PDE.ProfileFamily.Contract model
  boundaryRepair : PDE.BoundaryRepair.Contract model
  conservativeCarrier : PDE.ConservativeCarrier.Contract model
  ellipticConstraintTail : PDE.EllipticConstraintTail.Contract model
```

The concrete names may differ from the current Lean files, but the ownership
must not: applications instantiate the contract; `Hypostructure.PDE.Contract`
and `Hypostructure.PDE.FastTrack` execute it.

## Framework Driver

The desired public call is one driver, not twelve manually nested calls.

```lean
def runRows1To12
    (contract : NS2DGlobalRegularityContract)
    (root : contract.model.problem.RootResidual) :
    PDE.FastTrack.Rows1To12.Output contract root :=
  PDE.FastTrack.Rows1To12.run contract root
```

The driver owns the linear predecessor threading:

```text
root
  -> row1 stage
  -> row2 stage
  -> row3 stage
  -> row4 stage
  -> row5 stage
  -> row6 stage
  -> row7 stage
  -> row8 stage
  -> row9 stage
  -> row10 stage
  -> row11 stage
  -> row12 stage
```

Every row receives only the literal predecessor stage. Any inherited datum is
read through `Core.Residual.Query` from the accumulated ledger. The driver
exposes named accessors such as `stageAt RowId.row8 output`, so theorem code
never writes nested `row8 (row7 (row6 ...))` terms.

## Row Automation Map

| Row | Framework executor | Public NS2D contract fields | Framework-derived output | Residual if not closed |
|---|---|---|---|---|
| 1 | Core certification | `model`, `target`, `representation`, `targetInvariant`, `atlasCover`, `observables`, `coordinates` | legal represented signature and local-tail registration root | missing primitive contract |
| 2 | Core certification | `generatorForm` | equation-attached generator/form stage | missing closability or sector evidence |
| 3 | Core certification | `resourceBudget` | B1-B4 transcript in the ledger | nontransportable affordability |
| 4 | PDE quotient executor | `quotientDefect`, read row-2 form through query | computed represented defect and defect-geometry input | defect outside declared geometry |
| 5 | DirectedExhaustiveness | `structuralGradient`, target-complete boundary audit | CT15/CT16/class-closure output | target-visible boundary defect |
| 6 | DefectRouting | `defectGeometry` | CT13/CT7 resistance and harmonic routing | nonroutable harmonic residual |
| 7 | CapacityTarget | `capacity` | CT14/CT1 zero-capacity or target exclusion | positive-capacity target witness |
| 8 | ExactResponseCoverage | `exactResponse` | CT3/CT7 response-complete quotient | projection or response residual |
| 9 | ProfileFamily | `profileFamily` | CT17/CT12/CT11 scale/profile budget result | zero-cost, moving-scale, or survivor residual |
| 10 | BoundaryRepair | `boundaryRepair` | CT10/CT11/CT14/CT1 boundary quotient repair | in-window rigid/cost residual |
| 11 | ConservativeCarrier | `conservativeCarrier` | CT5/CT14/CT11 carrier ledger and reduced sign input | target-visible carrier remainder |
| 12 | EllipticConstraintTail | `ellipticConstraintTail` | CT3/CT14/CT15/CT13 pressure-tail quotient closure | dyadic, gauge-cokernel, or tail residual |

Rows 1-4 are registration stages. Rows 5-12 are executable fast-track rows.
The application never calls `CTN.run`; the row executor does.

## 2D Navier-Stokes Analytic Boundary

For 2D global regularity, the analytic contracts should be narrower than the
3D singularity architecture. The public contract should register:

- suitable weak or Leray-Hopf solution data on the selected 2D domain;
- local energy inequality and distributional equation;
- pressure representation modulo time functions;
- 2D energy/enstrophy control sufficient for the target local regularity
  predicate;
- Calderon-Zygmund pressure decomposition on registered local windows;
- harmonic pressure tail estimates and gauge neutrality;
- local-to-global cover compatibility.

These are analytic inputs, not framework outputs. Hypostructure can audit their
use, route failures, and assemble local conclusions, but it cannot manufacture
unregistered PDE estimates.

## Global Regularity Closure Shape

The driver should expose two endpoint predicates:

```lean
def rows1To12Closed
    (out : PDE.FastTrack.Rows1To12.Output contract root) : Prop

def localRegularityAtEveryPoint
    (out : PDE.FastTrack.Rows1To12.Output contract root) : Prop
```

For the 2D instance, `rows1To12Closed` is proved by the registered 2D analytic
contracts plus the framework row executors. Then
`PDE.LocalClosureAssembly.run` converts pointwise local regularity into the
global regularity statement.

The final theorem should have this shape:

```lean
theorem ns2d_global_regular
    (contract : NS2DGlobalRegularityContract)
    (root : contract.model.problem.RootResidual)
    (hAnalytic : contract.AnalyticContractsSatisfied root) :
    contract.GlobalRegularityTarget root :=
by
  let out := PDE.FastTrack.Rows1To12.run contract root
  exact PDE.LocalClosureAssembly.global_of_rows1To12_closed
    contract root out hAnalytic
```

The proof term above is schematic. The implementation task is to make
`Rows1To12.run` and the local-to-global assembly consume only contract fields
and ledger queries.

## Required Framework Additions

1. `PDE.FastTrack.Rows1To12.Contract`

   A framework-level aggregate contract whose fields are the row-1-to-row-12
   subcontracts. It must derive every row profile using existing
   `PDE.Contract.*.toProfile` functions.

2. `PDE.FastTrack.Rows1To12.Output`

   A typed stage bundle with opaque row accessors. The bundle owns predecessor
   threading and prevents public nested row expressions.

3. `PDE.FastTrack.Rows1To12.run`

   The only public executor for full row-1-to-row-12 automation. It calls the
   existing row executors internally, preserves the literal predecessor at each
   step, and extends the accumulated ledger only through framework mechanisms.

4. `PDE.FastTrack.Rows1To12.stageAt`

   A typed accessor for row stages. This replaces nested `node5 (node4 ...)`
   style terms.

5. `PDE.FastTrack.Rows1To12.workBound`

   A framework-derived polynomial budget assembled from row-level canonical
   payload budgets. The public contract may expose semantic PDE constants, but
   not per-row work coefficients.

6. `PDE.NavierStokes2D.GlobalRegularityContract`

   A problem-specific contract containing exactly the mathematical constants
   and analytic theorems needed by the 2D instance.

7. `PDE.NavierStokes2D.runRows1To12`

   A thin instantiation of the generic driver. It must not mention CT names,
   routes, or ledger constructors.

## Acceptance Checks

The automation is acceptable only if all checks below pass:

- `lake build Hypostructure.PDE.Contract`
- `lake build Hypostructure.PDE.FastTrack.Rows1To12`
- `lake build Hypostructure.Fixtures.PDERows1To12`
- `lake build HypostructurePDEExamples.RepresentedNS2DRows1To12Packet`
- import firewall over the repository
- `#print axioms` for the row-1-to-row-12 driver endpoint
- grep check showing no public-facing `CTN.run`
- grep check showing no public-facing `Ledger.Extension`
- grep check showing no public-facing hardcoded work constants
- grep check showing numeric theorem constants only in the NS2D problem
  contract or finite fixture problem contract

## Implementation Order

1. Freeze rows 1-12 only in the migration matrix.
2. Add the generic `Rows1To12` aggregate contract and output bundle in the PDE
   layer.
3. Port the existing row-1-to-row-12 represented NS2D packets into one
   `RepresentedNS2DRows1To12Packet` that calls only the driver.
4. Add a finite fixture that exercises active and inactive row outcomes through
   the aggregate driver.
5. Move all public semantic numeric literals into fixture or NS2D problem
   contracts.
6. Add the local-to-global assembly hook for the 2D target.
7. Kernel-check the driver, finite fixture, and represented NS2D packet.
8. Only after this passes, decide whether rows 13+ are needed for other PDE
   applications. They are not part of this row-1-to-row-12 2D automation pass.

