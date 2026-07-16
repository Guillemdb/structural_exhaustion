import StructuralExhaustion.Graph.HighCenterPort
import StructuralExhaustion.Graph.RootIncidence

namespace StructuralExhaustion.Graph.HighSeparatorPort

open StructuralExhaustion

universe u v

variable {V : Type u} (object : FiniteObject V) (center neighbor : V)

/-- The declared-neighbour index of one already certified incident vertex.
This is proof-level recovery through the public neighbour equivalence; it does
not scan a graph or classify the resulting port. -/
noncomputable def portOfAdjacent (adjacent : object.graph.Adj center neighbor) :
    HighCenterPort.Port object center :=
  (HighCenterPort.neighborEquiv object center).symm ⟨neighbor, adjacent⟩

@[simp] theorem endpoint_portOfAdjacent
    (adjacent : object.graph.Adj center neighbor) :
    HighCenterPort.endpoint object center
        (portOfAdjacent object center neighbor adjacent) = neighbor := by
  have recovered := (HighCenterPort.neighborEquiv object center).apply_symm_apply
    ⟨neighbor, adjacent⟩
  exact congrArg Subtype.val recovered

theorem portOfAdjacent_ne {left right : V}
    (leftAdjacent : object.graph.Adj center left)
    (rightAdjacent : object.graph.Adj center right)
    (different : left ≠ right) :
    portOfAdjacent object center left leftAdjacent ≠
      portOfAdjacent object center right rightAdjacent := by
  intro equal
  apply different
  have endpoints := congrArg (HighCenterPort.endpoint object center) equal
  simpa using endpoints

/-- High-separator port recovery for root divergence.  `Provenance` is an
opaque caller payload (for example tails and exact decompositions) transported
unchanged; this layer interprets none of it. -/
structure RootHigh {root : V}
    (divergence : RootIncidence.Divergence object root)
    (third : RootIncidence.Third object root divergence)
    (Provenance : Type v) where
  centerHigh : 4 ≤ object.degree root
  provenance : Provenance

namespace RootHigh

variable {object center}
variable {divergence : RootIncidence.Divergence object center}
variable {third : RootIncidence.Third object center divergence}
variable {Provenance : Type v}

noncomputable def leftPort (_output : RootHigh object divergence third Provenance) :
    HighCenterPort.Port object center :=
  portOfAdjacent object center divergence.leftNext divergence.leftAdjacent

noncomputable def rightPort (_output : RootHigh object divergence third Provenance) :
    HighCenterPort.Port object center :=
  portOfAdjacent object center divergence.rightNext divergence.rightAdjacent

noncomputable def thirdPort (_output : RootHigh object divergence third Provenance) :
    HighCenterPort.Port object center :=
  portOfAdjacent object center third.hit.value (third.adjacent object center)

@[simp] theorem left_endpoint (output : RootHigh object divergence third Provenance) :
    HighCenterPort.endpoint object center output.leftPort = divergence.leftNext :=
  endpoint_portOfAdjacent object center _ _

@[simp] theorem right_endpoint (output : RootHigh object divergence third Provenance) :
    HighCenterPort.endpoint object center output.rightPort = divergence.rightNext :=
  endpoint_portOfAdjacent object center _ _

@[simp] theorem third_endpoint (output : RootHigh object divergence third Provenance) :
    HighCenterPort.endpoint object center output.thirdPort = third.hit.value :=
  endpoint_portOfAdjacent object center _ _

theorem left_ne_right (output : RootHigh object divergence third Provenance) :
    output.leftPort ≠ output.rightPort :=
  portOfAdjacent_ne object center divergence.leftAdjacent divergence.rightAdjacent
    divergence.distinct

theorem third_ne_left (output : RootHigh object divergence third Provenance) :
    output.thirdPort ≠ output.leftPort :=
  portOfAdjacent_ne object center (third.adjacent object center)
    divergence.leftAdjacent (third.ne_left object center)

theorem third_ne_right (output : RootHigh object divergence third Provenance) :
    output.thirdPort ≠ output.rightPort :=
  portOfAdjacent_ne object center (third.adjacent object center)
    divergence.rightAdjacent (third.ne_right object center)

end RootHigh

/-- High-separator port recovery after a common incoming edge. -/
structure AfterEdgeHigh {separator : V}
    (incidence : RootIncidence.AfterEdge object separator)
    (Provenance : Type v) where
  centerHigh : 4 ≤ object.degree separator
  provenance : Provenance

namespace AfterEdgeHigh

variable {object center}
variable {incidence : RootIncidence.AfterEdge object center}
variable {Provenance : Type v}

noncomputable def predecessorPort
    (_output : AfterEdgeHigh object incidence Provenance) :
    HighCenterPort.Port object center :=
  portOfAdjacent object center incidence.predecessor incidence.predecessorAdjacent

noncomputable def leftPort (_output : AfterEdgeHigh object incidence Provenance) :
    HighCenterPort.Port object center :=
  portOfAdjacent object center incidence.leftNext incidence.leftAdjacent

noncomputable def rightPort (_output : AfterEdgeHigh object incidence Provenance) :
    HighCenterPort.Port object center :=
  portOfAdjacent object center incidence.rightNext incidence.rightAdjacent

@[simp] theorem predecessor_endpoint
    (output : AfterEdgeHigh object incidence Provenance) :
    HighCenterPort.endpoint object center output.predecessorPort =
      incidence.predecessor :=
  endpoint_portOfAdjacent object center _ _

@[simp] theorem left_endpoint (output : AfterEdgeHigh object incidence Provenance) :
    HighCenterPort.endpoint object center output.leftPort = incidence.leftNext :=
  endpoint_portOfAdjacent object center _ _

@[simp] theorem right_endpoint (output : AfterEdgeHigh object incidence Provenance) :
    HighCenterPort.endpoint object center output.rightPort = incidence.rightNext :=
  endpoint_portOfAdjacent object center _ _

theorem predecessor_ne_left
    (output : AfterEdgeHigh object incidence Provenance) :
    output.predecessorPort ≠ output.leftPort :=
  portOfAdjacent_ne object center incidence.predecessorAdjacent
    incidence.leftAdjacent incidence.predecessor_ne_left

theorem predecessor_ne_right
    (output : AfterEdgeHigh object incidence Provenance) :
    output.predecessorPort ≠ output.rightPort :=
  portOfAdjacent_ne object center incidence.predecessorAdjacent
    incidence.rightAdjacent incidence.predecessor_ne_right

theorem left_ne_right (output : AfterEdgeHigh object incidence Provenance) :
    output.leftPort ≠ output.rightPort :=
  portOfAdjacent_ne object center incidence.leftAdjacent incidence.rightAdjacent
    incidence.left_ne_right

end AfterEdgeHigh

/-- Consume exactly the high constructor of the root-incidence split. -/
noncomputable def ofRootBranch? {root : V}
    (divergence : RootIncidence.Divergence object root)
    (Provenance : Type v) (provenance : Provenance) :
    RootIncidence.Branch object root divergence →
      Option (Sigma fun third => RootHigh object divergence third Provenance)
  | .cubic _degreeEq _third => none
  | .high centerHigh third => some ⟨third, ⟨centerHigh, provenance⟩⟩

def rootBranchIsHigh {root : V}
    {divergence : RootIncidence.Divergence object root} :
    RootIncidence.Branch object root divergence → Bool
  | .cubic .. => false
  | .high .. => true

theorem ofRootBranch?_isSome {root : V}
    (divergence : RootIncidence.Divergence object root)
    (Provenance : Type v) (provenance : Provenance)
    (branch : RootIncidence.Branch object root divergence) :
    (ofRootBranch? object divergence Provenance provenance branch).isSome =
      rootBranchIsHigh object branch := by
  cases branch <;> rfl

/-- Consume exactly the high constructor of the after-edge split. -/
noncomputable def ofAfterEdgeBranch? {separator : V}
    (incidence : RootIncidence.AfterEdge object separator)
    (Provenance : Type v) (provenance : Provenance) :
    RootIncidence.AfterEdgeBranch object separator incidence →
      Option (AfterEdgeHigh object incidence Provenance)
  | .cubic _degreeEq => none
  | .high centerHigh => some ⟨centerHigh, provenance⟩

def afterEdgeBranchIsHigh {separator : V}
    {incidence : RootIncidence.AfterEdge object separator} :
    RootIncidence.AfterEdgeBranch object separator incidence → Bool
  | .cubic .. => false
  | .high .. => true

theorem ofAfterEdgeBranch?_isSome {separator : V}
    (incidence : RootIncidence.AfterEdge object separator)
    (Provenance : Type v) (provenance : Provenance)
    (branch : RootIncidence.AfterEdgeBranch object separator incidence) :
    (ofAfterEdgeBranch? object incidence Provenance provenance branch).isSome =
      afterEdgeBranchIsHigh object branch := by
  cases branch <;> rfl

/-- Port recovery uses certified adjacency and performs no primitive scan. -/
def checks : Nat := 0

end StructuralExhaustion.Graph.HighSeparatorPort
