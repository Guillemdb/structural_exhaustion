import StructuralExhaustion.Graph.SurplusPatternRoutingObservations

namespace StructuralExhaustion.Graph.SurplusPatternRoutingObservationsTests

open StructuralExhaustion
open SurplusPatternCoarseRouting
open SurplusPatternRoutingObservations

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}

example (pair : SurplusPairResponse.ScheduledPair (setup := setup))
    (first : Bool) (role : SurplusPortActivation.PortRole) :
    (boundaryDegreeProfile (ctx := ctx) pair first role).val =
      portSupportDegree (ctx := ctx) pair first role :=
  boundaryDegreeProfile_apply pair first role

example : boundedDegreeProfiles.card = 4096 :=
  boundedDegreeProfiles_card

example (pair : SurplusPairResponse.ScheduledPair (setup := setup))
    (window : InducedPathWindowLedger.WindowIndex ctx.G.object)
    (position : Fin 13) (first : Bool)
    (role : SurplusPortActivation.PortRole) :
    position ∈ windowAttachmentLabel (ctx := ctx) pair window first role ↔
      windowPortAttached (ctx := ctx) (setup := setup)
        pair window position first role :=
  mem_windowAttachmentLabel_iff pair window position first role

end StructuralExhaustion.Graph.SurplusPatternRoutingObservationsTests
