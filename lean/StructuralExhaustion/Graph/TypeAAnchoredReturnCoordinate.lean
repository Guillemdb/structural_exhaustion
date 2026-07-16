import StructuralExhaustion.Graph.TypeACompletionPortCoordinate
import StructuralExhaustion.Graph.EdgeRootedReturn

namespace StructuralExhaustion.Graph.TypeAAnchoredReturnCoordinate

open StructuralExhaustion
open TypeACanonicalReceiverTrace

universe u

variable {V : Type u} (object : FiniteObject V)
variable (profile : SupportProfile object)

abbrev Port := TypeACompletionPortCoordinate.Coordinate object profile

/-- The literal oriented ambient edge underlying one completion port. -/
def dart (port : Port object profile) : object.graph.Dart :=
  ⟨((port.receiver object profile).1,
    port.outside object profile),
    port.adjacent object profile⟩

/-- One manuscript anchored return through a fixed completion port: a simple
path from the outside endpoint back to the receiver after deleting the port
edge. -/
structure AnchoredReturn (port : Port object profile) where
  returnPath : DartReturn object.graph (dart object profile port)

namespace AnchoredReturn

def path {port : Port object profile}
    (anchored : AnchoredReturn object profile port) :
    (object.graph.deleteEdges
      {s((port.receiver object profile).1,
        port.outside object profile)}).Walk
      (port.outside object profile)
      (port.receiver object profile).1 :=
  anchored.returnPath.path

theorem isPath {port : Port object profile}
    (anchored : AnchoredReturn object profile port) :
    anchored.path object profile |>.IsPath :=
  anchored.returnPath.isPath

theorem avoids_port_edge {port : Port object profile}
    (anchored : AnchoredReturn object profile port) :
    s((port.receiver object profile).1, port.outside object profile) ∉
      (anchored.returnPath.toEdgeRootedReturn).ambientPath.edges :=
  by
    change (dart object profile port).edge ∉
      (anchored.returnPath.toEdgeRootedReturn).ambientPath.edges
    exact anchored.returnPath.toEdgeRootedReturn.root_not_mem_path

end AnchoredReturn

/-- Exact local premise from the earlier bridgelessness node.  It is indexed
only by the already selected completion-port schedule. -/
structure Producer where
  notBridge : ∀ port : Port object profile,
    ¬object.graph.IsBridge (dart object profile port).edge

/-- Construct one proof-selected anchored return for every actual completion
port. Mathlib choice consumes proved reachability; it does not enumerate
walks. -/
noncomputable def Producer.produce (producer : Producer object profile)
    (port : Port object profile) : AnchoredReturn object profile port where
  returnPath := DartReturn.ofNotBridge (producer.notBridge port)

/-- The return producer performs no finite search beyond the already verified
completion-port schedule. -/
def additionalChecks : Nat := 0

theorem additionalChecks_eq_zero : additionalChecks = 0 := rfl

end StructuralExhaustion.Graph.TypeAAnchoredReturnCoordinate
