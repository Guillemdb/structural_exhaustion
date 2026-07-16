import StructuralExhaustion.Graph.TypeAFirstEntryCoordinate

namespace StructuralExhaustion.Graph.TypeAReceiverEntryChannel

open StructuralExhaustion
open TypeACanonicalReceiverTrace

universe u

variable {V : Type u} (object : FiniteObject V)
variable (profile : SupportProfile object)
variable (port : TypeAAnchoredReturnCoordinate.Port object profile)
variable (anchored : TypeAAnchoredReturnCoordinate.AnchoredReturn object profile port)
variable (first : TypeAFirstEntryCoordinate.FirstEntry object profile port anchored)

abbrev DeletedGraph := object.graph.deleteEdges
  {s((port.receiver object profile).1, port.outside object profile)}

/-- The exact outside prefix of the stored anchored return, ending at its
first support hit.  This is the manuscript connector `Gamma`. -/
structure Connector where
  path : DeletedGraph object profile port |>.Walk
    (port.outside object profile) (first.entry object profile port anchored)
  isPath : path.IsPath
  support_eq : path.support = first.hit.before ++
    [first.entry object profile port anchored]

namespace Connector

/-- Extract the connector from the already scanned first-entry coordinate.
No path search is performed: this is `takeUntil` on the stored return. -/
noncomputable def extract : Connector object profile port anchored first := by
  letI : DecidableEq V := object.input.vertices.decEq
  let entry := first.entry object profile port anchored
  have entryMem : entry ∈
      (TypeAAnchoredReturnCoordinate.AnchoredReturn.path
        object profile anchored).support := by
    exact first.hit.member
  let connector :=
    (TypeAAnchoredReturnCoordinate.AnchoredReturn.path
      object profile anchored).takeUntil entry entryMem
  refine ⟨connector, ?_, ?_⟩
  · exact (TypeAAnchoredReturnCoordinate.AnchoredReturn.isPath
      object profile anchored).takeUntil entryMem
  · dsimp [connector]
    rw [SimpleGraph.Walk.takeUntil_eq_take,
      SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_take]
    have entryNotBefore : entry ∉ first.hit.before := by
      intro member
      exact first.hit.beforeAbsent entry member
        (first.entry_mem_support object profile port anchored)
    have indexEq :
        (TypeAAnchoredReturnCoordinate.AnchoredReturn.path
          object profile anchored).support.idxOf entry =
          first.hit.before.length := by
      calc
        (TypeAAnchoredReturnCoordinate.AnchoredReturn.path
            object profile anchored).support.idxOf entry =
            (first.hit.before ++ first.hit.value :: first.hit.after).idxOf entry :=
          congrArg (List.idxOf entry) first.hit.split
        _ = first.hit.before.length := by
          rw [List.idxOf_append_of_notMem entryNotBefore]
          have tailIndex : List.idxOf entry
              (first.hit.value :: first.hit.after) = 0 := by
            change List.idxOf first.hit.value
              (first.hit.value :: first.hit.after) = 0
            exact List.idxOf_cons_self
          rw [tailIndex, Nat.add_zero]
    rw [indexEq]
    calc
      (TypeAAnchoredReturnCoordinate.AnchoredReturn.path
          object profile anchored).support.take
          (first.hit.before.length + 1) =
          (first.hit.before ++ first.hit.value :: first.hit.after).take
            (first.hit.before.length + 1) :=
        congrArg (fun values : List V =>
          values.take (first.hit.before.length + 1)) first.hit.split
      _ = first.hit.before ++
          [first.entry object profile port anchored] := by
        rw [List.take_append]
        simp [TypeAFirstEntryCoordinate.FirstEntry.entry]

def length (connector : Connector object profile port anchored first) : Nat :=
  connector.path.length

theorem support_before_outside
    (connector : Connector object profile port anchored first) :
    ∀ vertex ∈ connector.path.support,
      vertex ≠ first.entry object profile port anchored →
        vertex ∉ profile.support := by
  intro vertex member notEntry
  rw [connector.support_eq] at member
  have before : vertex ∈ first.hit.before := by
    simpa [notEntry] using member
  exact first.before_outside object profile port anchored vertex before

theorem length_pos
    (connector : Connector object profile port anchored first) :
    0 < connector.length object profile port anchored first := by
  have endpointsNe : port.outside object profile ≠
      first.entry object profile port anchored := by
    intro equal
    exact port.outside_not_mem_support object profile
      (equal ▸ first.entry_mem_support object profile port anchored)
  exact SimpleGraph.Walk.not_nil_iff_lt_length.mp
    (SimpleGraph.Walk.not_nil_of_ne endpointsNe)

end Connector

/-- One proof-carrying receiver-entry channel inside the induced support.
The construction never enumerates paths: callers supply the channel certified
by the local connectivity argument that needs it. -/
structure Channel where
  path : (profile.supportObject object).graph.Walk
    ⟨first.entry object profile port anchored,
      first.entry_mem_support object profile port anchored⟩
    (port.receiver object profile)
  isPath : path.IsPath

namespace Channel

noncomputable def length (channel : Channel object profile port anchored first) : Nat :=
  channel.path.length

/-- View an internal channel in the ambient graph. -/
noncomputable def ambientPath (channel : Channel object profile port anchored first) :
    object.graph.Walk
      (first.entry object profile port anchored)
      (port.receiver object profile).1 :=
  channel.path.map
    (object.induceFinsetEmbedding profile.support).toHom

theorem ambientPath_isPath
    (channel : Channel object profile port anchored first) :
    (channel.ambientPath object profile port anchored first).IsPath :=
  SimpleGraph.Walk.map_isPath_of_injective
    (object.induceFinsetEmbedding profile.support).injective channel.isPath

theorem ambientPath_support_inside
    (channel : Channel object profile port anchored first) :
    ∀ vertex ∈ (channel.ambientPath object profile port anchored first).support,
      vertex ∈ profile.support := by
  intro vertex member
  have supportEq := SimpleGraph.Walk.support_map
    (object.induceFinsetEmbedding profile.support).toHom channel.path
  change vertex ∈ (channel.path.map
    (object.induceFinsetEmbedding profile.support).toHom).support at member
  rw [supportEq] at member
  obtain ⟨internal, _member, equal⟩ := List.mem_map.mp member
  simpa [← equal] using internal.2

theorem ambientPath_avoids_port_edge
    (channel : Channel object profile port anchored first) :
    s((port.receiver object profile).1, port.outside object profile) ∉
      (channel.ambientPath object profile port anchored first).edges := by
  intro edgeMember
  have outsideMember :=
    (channel.ambientPath object profile port anchored first).snd_mem_support_of_mem_edges
      edgeMember
  have outsideInside := channel.ambientPath_support_inside object profile port anchored
    first (port.outside object profile) outsideMember
  exact port.outside_not_mem_support object profile outsideInside

/-- The same internal channel in the literal port-edge-deleted graph. -/
noncomputable def deletedPath (channel : Channel object profile port anchored first) :
    DeletedGraph object profile port |>.Walk
      (first.entry object profile port anchored)
      (port.receiver object profile).1 :=
  (channel.ambientPath object profile port anchored first).toDeleteEdge
    s((port.receiver object profile).1, port.outside object profile)
    (channel.ambientPath_avoids_port_edge object profile port anchored first)

theorem deletedPath_isPath
    (channel : Channel object profile port anchored first) :
    (channel.deletedPath object profile port anchored first).IsPath := by
  apply channel.ambientPath_isPath object profile port anchored first |>.toDeleteEdges
  intro edge edgeMember edgeInDeleted
  have edgeEq : edge =
      s((port.receiver object profile).1, port.outside object profile) := by
    simpa using edgeInDeleted
  apply channel.ambientPath_avoids_port_edge object profile port anchored first
  simpa [edgeEq] using edgeMember

@[simp] theorem deletedPath_length
    (channel : Channel object profile port anchored first) :
  (channel.deletedPath object profile port anchored first).length =
      channel.length object profile port anchored first := by
  rw [deletedPath, SimpleGraph.Walk.length_transfer]
  simpa [ambientPath, length] using
    (SimpleGraph.Walk.length_map
      (object.induceFinsetEmbedding profile.support).toHom channel.path)

theorem deletedPath_support_inside
    (channel : Channel object profile port anchored first) :
    ∀ vertex ∈ (channel.deletedPath object profile port anchored first).support,
      vertex ∈ profile.support := by
  intro vertex member
  apply channel.ambientPath_support_inside object profile port anchored first vertex
  simpa [deletedPath] using member

end Channel

/-- Concatenate the exact outside connector with any supplied internal
receiver-entry channel. -/
noncomputable def returnPath
    (connector : Connector object profile port anchored first)
    (channel : Channel object profile port anchored first) :
    DeletedGraph object profile port |>.Walk
      (port.outside object profile) (port.receiver object profile).1 :=
  connector.path.append
    (channel.deletedPath object profile port anchored first)

theorem returnPath_isPath
    (connector : Connector object profile port anchored first)
    (channel : Channel object profile port anchored first) :
    (returnPath object profile port anchored first connector channel).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, returnPath,
    SimpleGraph.Walk.support_append, List.nodup_append']
  refine ⟨connector.isPath.support_nodup,
    channel.deletedPath_isPath object profile port anchored first |>.support_nodup.tail,
    ?_⟩
  rw [List.disjoint_left]
  intro vertex inConnector inChannelTail
  have inChannel : vertex ∈
      (channel.deletedPath object profile port anchored first).support :=
    List.mem_of_mem_tail inChannelTail
  have inside := channel.deletedPath_support_inside object profile port anchored
    first vertex inChannel
  by_cases atEntry : vertex = first.entry object profile port anchored
  · subst vertex
    have channelNodup :=
      channel.deletedPath_isPath object profile port anchored first |>.support_nodup
    rw [← SimpleGraph.Walk.cons_tail_support] at channelNodup
    exact (List.nodup_cons.mp channelNodup).1 inChannelTail
  · exact connector.support_before_outside object profile port anchored first
      vertex inConnector atEntry inside

@[simp] theorem returnPath_length
    (connector : Connector object profile port anchored first)
    (channel : Channel object profile port anchored first) :
    (returnPath object profile port anchored first connector channel).length =
      connector.length object profile port anchored first +
        channel.length object profile port anchored first := by
  rw [returnPath, SimpleGraph.Walk.length_append,
    channel.deletedPath_length object profile port anchored first]
  rfl

/-- The semantic channel spectrum: exactly the lengths of supplied
proof-carrying simple channels in the induced support. -/
def spectrum : Set Nat :=
  {length | ∃ channel : Channel object profile port anchored first,
    channel.length object profile port anchored first = length}

theorem mem_spectrum
    (channel : Channel object profile port anchored first) :
    channel.length object profile port anchored first ∈
      spectrum object profile port anchored first :=
  ⟨channel, rfl⟩

/-- Connector extraction and every downstream assembly operation reuse stored
certificates and perform no additional graph or target-predicate checks. -/
def additionalChecks : Nat := 0

theorem additionalChecks_eq_zero : additionalChecks = 0 := rfl

/-- Structural work used by `Connector.extract`: traverse the retained clean
prefix and its first support entry once.  This is distinct from graph or
target-predicate checks. -/
def connectorTraversalChecks : Nat := first.hit.before.length + 1

theorem connectorTraversalChecks_le_storedSupport :
    connectorTraversalChecks object profile port anchored first ≤
      (TypeAAnchoredReturnCoordinate.AnchoredReturn.path
        object profile anchored).support.length := by
  have supportLength :
      (TypeAAnchoredReturnCoordinate.AnchoredReturn.path
          object profile anchored).support.length =
        (first.hit.before ++ first.hit.value :: first.hit.after).length :=
    congrArg List.length first.hit.split
  unfold connectorTraversalChecks
  rw [supportLength]
  simp

theorem connectorTraversalChecks_le_vertexCount :
    connectorTraversalChecks object profile port anchored first ≤
      object.input.vertices.card := by
  calc
    connectorTraversalChecks object profile port anchored first ≤
        (TypeAAnchoredReturnCoordinate.AnchoredReturn.path
          object profile anchored).support.length :=
      connectorTraversalChecks_le_storedSupport object profile port anchored first
    _ ≤ object.input.vertices.card := by
      letI : FinEnum V := object.input.vertices
      simpa [FinEnum.card_eq_fintypeCard] using
        (TypeAAnchoredReturnCoordinate.AnchoredReturn.isPath
          object profile anchored).support_nodup.length_le_card

end StructuralExhaustion.Graph.TypeAReceiverEntryChannel
