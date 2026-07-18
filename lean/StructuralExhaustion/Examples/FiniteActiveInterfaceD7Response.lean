import StructuralExhaustion.Graph.FiniteActiveInterfaceD7Signature

/-!
This parameterized transfer fixture checks the complete six-summand D7
signature independently of the Erdős constants.  It uses the same public
active-interface profile and scans only its supplied declared coordinates.
-/

namespace StructuralExhaustion.Examples.FiniteActiveInterfaceD7Response

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
variable (interface : FiniteActiveInterfaceD7Response.Interface (ctx := ctx))

theorem all_declared_families_are_locally_filtered
    (coordinate :
      FiniteActiveInterfaceD7Signature.Coordinate stage interface) :
    FiniteActiveInterfaceD7Signature.support stage coordinate.1 ⊆
      interface.support :=
  FiniteActiveInterfaceD7Signature.coordinate_support_subset
    stage interface coordinate

theorem complete_local_scan
    (coordinate : FiniteActiveInterfaceD7Signature.RawCoordinate stage)
    (contained : FiniteActiveInterfaceD7Signature.support stage coordinate ⊆
      interface.support) :
    ∃ proof, (⟨coordinate, proof⟩ :
      FiniteActiveInterfaceD7Signature.Coordinate stage interface) ∈
      (FiniteActiveInterfaceD7Signature.coordinates stage interface).orderedValues :=
  (FiniteActiveInterfaceD7Signature.mem_coordinates_iff
    stage interface coordinate).2 contained

theorem local_scan_work_bound :
    (FiniteActiveInterfaceD7Signature.coordinates stage interface).card ≤
      FiniteActiveInterfaceD7Signature.checks stage :=
  FiniteActiveInterfaceD7Signature.coordinates_card_le_checks stage interface

end StructuralExhaustion.Examples.FiniteActiveInterfaceD7Response
