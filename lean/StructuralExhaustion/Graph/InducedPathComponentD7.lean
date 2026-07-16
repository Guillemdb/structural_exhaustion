import StructuralExhaustion.Graph.InducedPathComponentD4
import StructuralExhaustion.Graph.SurplusPairResponse

namespace StructuralExhaustion.Graph.InducedPathComponentD7

open StructuralExhaustion

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
variable (componentInput :
  InducedPathComponentBoundarySchedule.Input ctx.G.object)

/-!
# Component-local D7 sparse-pair support schedule

Clause D7 contains the sparse-surplus port, return, suppression, triangle, and
pair-response data already produced by `SurplusPairResponse`.  This module
selects exactly those graph-owned free-pair supports contained in the active
interface of one stored component corridor.

It deliberately stops at the support schedule.  The existing
`FiniteSupportResponse.Profile` is context-indexed, whereas the cold cut-state
currently accepts one Boolean per local coordinate.  No Boolean response or
all-context equivalence is inferred here.
-/

def SupportContained (pair : SurplusPairResponse.FreePair stage) : Prop :=
  pair.support stage ⊆ InducedPathComponentD4.activeSupport componentInput

noncomputable def supportContainedDecidable
    (pair : SurplusPairResponse.FreePair stage) :
    Decidable (SupportContained stage componentInput pair) := by
  classical
  unfold SupportContained
  infer_instance

/-- A genuine D7 pair coordinate whose complete declared support lies in the
one component interface. -/
abbrev Coordinate :=
  {pair : SurplusPairResponse.FreePair stage //
    SupportContained stage componentInput pair}

@[implicit_reducible]
noncomputable def coordinates : FinEnum (Coordinate stage componentInput) :=
  Core.Enumeration.subtype
    (SurplusPairResponse.freePairEnumeration stage)
    (SupportContained stage componentInput)
    (supportContainedDecidable stage componentInput)

namespace Coordinate

noncomputable def pair
    (coordinate : Coordinate stage componentInput) :
    SurplusPairResponse.FreePair stage := coordinate.1

noncomputable def support
    (coordinate : Coordinate stage componentInput) : Finset ctx.G.Vertex :=
  (coordinate.pair stage componentInput).support stage

theorem support_subset_active
    (coordinate : Coordinate stage componentInput) :
    coordinate.support stage componentInput ⊆
      InducedPathComponentD4.activeSupport componentInput :=
  coordinate.2

theorem firstGamma_subset_support
    (coordinate : Coordinate stage componentInput) :
    (stage.demand
      (coordinate.pair stage componentInput).1.first).GammaVertices ⊆
      coordinate.support stage componentInput :=
  (coordinate.pair stage componentInput).firstGamma_subset_support stage

theorem secondGamma_subset_support
    (coordinate : Coordinate stage componentInput) :
    (stage.demand
      (coordinate.pair stage componentInput).1.second).GammaVertices ⊆
      coordinate.support stage componentInput :=
  (coordinate.pair stage componentInput).secondGamma_subset_support stage

end Coordinate

/-- Filtering can only reduce the already verified free-pair schedule. -/
theorem coordinates_card_le_freePairs :
    (coordinates stage componentInput).card ≤
      (SurplusPairResponse.freePairEnumeration stage).card :=
  Core.Enumeration.subtype_card_le
    (SurplusPairResponse.freePairEnumeration stage)
    (SupportContained stage componentInput)
    (supportContainedDecidable stage componentInput)

end StructuralExhaustion.Graph.InducedPathComponentD7
