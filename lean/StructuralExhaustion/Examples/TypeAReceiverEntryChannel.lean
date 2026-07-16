import StructuralExhaustion.Graph.TypeAReceiverEntryChannel

namespace StructuralExhaustion.Examples.TypeAReceiverEntryChannel

open StructuralExhaustion

universe u

variable {V : Type u} (object : Graph.FiniteObject V)
variable (profile : Graph.TypeACanonicalReceiverTrace.SupportProfile object)
variable (port : Graph.TypeAAnchoredReturnCoordinate.Port object profile)
variable (anchored : Graph.TypeAAnchoredReturnCoordinate.AnchoredReturn
  object profile port)

abbrev First := Graph.TypeAFirstEntryCoordinate.FirstEntry
  object profile port anchored

/-- A non-Erdős transfer of the connector/channel assembly theorem.  The
fixture is fully parametric in the target predicate and demonstrates that the
graph API is independent of Mersenne arithmetic. -/
theorem supplied_channel_return
    (first : First object profile port anchored)
    (channel : Graph.TypeAReceiverEntryChannel.Channel
      object profile port anchored first) :
    let connector := Graph.TypeAReceiverEntryChannel.Connector.extract
      object profile port anchored first
    (Graph.TypeAReceiverEntryChannel.returnPath
      object profile port anchored first connector channel).IsPath ∧
    (Graph.TypeAReceiverEntryChannel.returnPath
      object profile port anchored first connector channel).length =
      connector.length object profile port anchored first +
        channel.length object profile port anchored first := by
  dsimp
  exact ⟨Graph.TypeAReceiverEntryChannel.returnPath_isPath
      object profile port anchored first _ channel,
    Graph.TypeAReceiverEntryChannel.returnPath_length
      object profile port anchored first _ channel⟩

example : Graph.TypeAReceiverEntryChannel.additionalChecks = 0 := rfl

example (first : First object profile port anchored) :
    Graph.TypeAReceiverEntryChannel.connectorTraversalChecks
        object profile port anchored first ≤ object.input.vertices.card :=
  Graph.TypeAReceiverEntryChannel.connectorTraversalChecks_le_vertexCount
    object profile port anchored first

end StructuralExhaustion.Examples.TypeAReceiverEntryChannel
