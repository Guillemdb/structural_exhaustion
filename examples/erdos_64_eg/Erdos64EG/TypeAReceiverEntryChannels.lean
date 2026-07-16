import Erdos64EG.TargetAlgebra
import Erdos64EG.TypeAFirstEntryCoordinates
import StructuralExhaustion.Graph.TypeAReceiverEntryChannel

namespace Erdos64EG.Internal.TypeAReceiverEntryChannels

open StructuralExhaustion

universe u

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

abbrev Node61 := TypeBEntryRouting.VerifiedNode61Residual ctx
abbrev Node63 (node61 : Node61 (ctx := ctx)) :=
  TypeANode63Support.VerifiedNode63Residual (ctx := ctx) node61
abbrev Port (node61 : Node61 (ctx := ctx)) (node63 : Node63 node61) :=
  TypeACompletionPortCoordinates.Coordinate (ctx := ctx) node61 node63

abbrev First (node61 : Node61 (ctx := ctx)) (node63 : Node63 node61)
    (port : Port node61 node63) :=
  Graph.TypeAFirstEntryCoordinate.FirstEntry ctx.G.object
    node63.typeAProfile port
    (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)

abbrev Channel (node61 : Node61 (ctx := ctx)) (node63 : Node63 node61)
    (port : Port node61 node63) :=
  Graph.TypeAReceiverEntryChannel.Channel ctx.G.object node63.typeAProfile port
    (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)
    (TypeAFirstEntryCoordinates.firstEntry node61 node63 port)

/-- The literal connector `Gamma` extracted from the exact stored anchored
return and exact first-hit scan. -/
noncomputable def connector (node61 : Node61 (ctx := ctx))
    (node63 : Node63 node61) (port : Port node61 node63) :=
  Graph.TypeAReceiverEntryChannel.Connector.extract ctx.G.object
    node63.typeAProfile port
    (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)
    (TypeAFirstEntryCoordinates.firstEntry node61 node63 port)

theorem connector_support_exact (node61 : Node61 (ctx := ctx))
    (node63 : Node63 node61) (port : Port node61 node63) :
    (connector node61 node63 port).path.support =
      (TypeAFirstEntryCoordinates.firstEntry node61 node63 port).hit.before ++
        [(TypeAFirstEntryCoordinates.firstEntry node61 node63 port).entry
          ctx.G.object node63.typeAProfile port
          (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)] :=
  (connector node61 node63 port).support_eq

/-- Every supplied proof-carrying channel in the induced Type A support
assembles with the stored connector to the literal simple deleted-edge return.
No channel family is enumerated. -/
theorem connector_append_channel_isPath (node61 : Node61 (ctx := ctx))
    (node63 : Node63 node61) (port : Port node61 node63)
    (channel : Channel node61 node63 port) :
    (Graph.TypeAReceiverEntryChannel.returnPath ctx.G.object
      node63.typeAProfile port
      (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)
      (TypeAFirstEntryCoordinates.firstEntry node61 node63 port)
      (connector node61 node63 port) channel).IsPath :=
  Graph.TypeAReceiverEntryChannel.returnPath_isPath ctx.G.object
    node63.typeAProfile port
    (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)
    (TypeAFirstEntryCoordinates.firstEntry node61 node63 port)
    (connector node61 node63 port) channel

theorem connector_append_channel_length (node61 : Node61 (ctx := ctx))
    (node63 : Node63 node61) (port : Port node61 node63)
    (channel : Channel node61 node63 port) :
    (Graph.TypeAReceiverEntryChannel.returnPath ctx.G.object
      node63.typeAProfile port
      (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)
      (TypeAFirstEntryCoordinates.firstEntry node61 node63 port)
      (connector node61 node63 port) channel).length =
      (connector node61 node63 port).length ctx.G.object
          node63.typeAProfile port
          (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)
          (TypeAFirstEntryCoordinates.firstEntry node61 node63 port) +
        channel.length ctx.G.object node63.typeAProfile port
          (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)
          (TypeAFirstEntryCoordinates.firstEntry node61 node63 port) :=
  Graph.TypeAReceiverEntryChannel.returnPath_length ctx.G.object
    node63.typeAProfile port
    (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)
    (TypeAFirstEntryCoordinates.firstEntry node61 node63 port)
    (connector node61 node63 port) channel

/-- `lem:typeA-spectral-pressure`, first assertion.  The contradiction uses
the target-avoidance field of the identical minimal-counterexample context. -/
theorem spectral_pressure (node61 : Node61 (ctx := ctx))
    (node63 : Node63 node61) (port : Port node61 node63)
    (channel : Channel node61 node63 port) :
    ¬MersenneLength
      ((connector node61 node63 port).length ctx.G.object
          node63.typeAProfile port
          (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)
          (TypeAFirstEntryCoordinates.firstEntry node61 node63 port) +
        channel.length ctx.G.object node63.typeAProfile port
          (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)
          (TypeAFirstEntryCoordinates.firstEntry node61 node63 port)) := by
  intro mersenne
  let path := Graph.TypeAReceiverEntryChannel.returnPath ctx.G.object
    node63.typeAProfile port
    (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)
    (TypeAFirstEntryCoordinates.firstEntry node61 node63 port)
    (connector node61 node63 port) channel
  have pathMersenne : MersenneLength path.length := by
    rw [connector_append_channel_length node61 node63 port channel]
    exact mersenne
  have hasReturn : HasMersenneReturn ctx.G.object.graph := ⟨{
    dart := Graph.TypeAAnchoredReturnCoordinate.dart ctx.G.object
      node63.typeAProfile port
    path := path
    isPath := connector_append_channel_isPath node61 node63 port channel
    length_ok := pathMersenne
  }⟩
  exact ctx.avoids ((target_iff_hasMersenneReturn ctx.G.object).2 hasReturn)

/-- Semantic spectrum form: every length represented by a supplied simple
induced-support channel obeys the same connector pressure. -/
theorem spectral_pressure_of_mem (node61 : Node61 (ctx := ctx))
    (node63 : Node63 node61) (port : Port node61 node63)
    {lambda : Nat}
    (member : lambda ∈ Graph.TypeAReceiverEntryChannel.spectrum ctx.G.object
      node63.typeAProfile port
      (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)
      (TypeAFirstEntryCoordinates.firstEntry node61 node63 port)) :
    ¬MersenneLength
      ((connector node61 node63 port).length ctx.G.object
          node63.typeAProfile port
          (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)
          (TypeAFirstEntryCoordinates.firstEntry node61 node63 port) + lambda) := by
  obtain ⟨channel, rfl⟩ := member
  exact spectral_pressure node61 node63 port channel

/-- Integer form of the manuscript band exclusion.  Integer inequalities are
used deliberately, so no truncated natural subtraction is hidden in the
translation of `[mu-b, mu-a]`. -/
theorem spectral_band_exclusion (node61 : Node61 (ctx := ctx))
    (node63 : Node63 node61) (port : Port node61 node63)
    (a b mersenne : Nat)
    (interval : ∀ z : Int, (a : Int) ≤ z → z ≤ (b : Int) →
      ∃ channel : Channel node61 node63 port,
        (channel.length ctx.G.object node63.typeAProfile port
          (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)
          (TypeAFirstEntryCoordinates.firstEntry node61 node63 port) : Int) = z)
    (mersenneLength : MersenneLength mersenne) :
    ¬((mersenne : Int) - (b : Int) ≤
        ((connector node61 node63 port).length ctx.G.object
          node63.typeAProfile port
          (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)
          (TypeAFirstEntryCoordinates.firstEntry node61 node63 port) : Int) ∧
      ((connector node61 node63 port).length ctx.G.object
          node63.typeAProfile port
          (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)
          (TypeAFirstEntryCoordinates.firstEntry node61 node63 port) : Int) ≤
        (mersenne : Int) - (a : Int)) := by
  rintro ⟨lower, upper⟩
  let g := (connector node61 node63 port).length ctx.G.object
    node63.typeAProfile port
    (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)
    (TypeAFirstEntryCoordinates.firstEntry node61 node63 port)
  let z : Int := (mersenne : Int) - (g : Int)
  have aLe : (a : Int) ≤ z := by dsimp [z, g] at *; omega
  have leB : z ≤ (b : Int) := by dsimp [z, g] at *; omega
  obtain ⟨channel, channelLength⟩ := interval z aLe leB
  have totalInt :
      ((g + channel.length ctx.G.object node63.typeAProfile port
        (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)
        (TypeAFirstEntryCoordinates.firstEntry node61 node63 port) : Nat) : Int) =
        (mersenne : Int) := by
    push_cast
    dsimp [z] at channelLength
    omega
  have totalNat :
      g + channel.length ctx.G.object node63.typeAProfile port
        (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)
        (TypeAFirstEntryCoordinates.firstEntry node61 node63 port) = mersenne := by
    exact_mod_cast totalInt
  apply spectral_pressure node61 node63 port channel
  rw [totalNat]
  exact mersenneLength

theorem additionalChecks_eq_zero :
    Graph.TypeAReceiverEntryChannel.additionalChecks = 0 := rfl

/-- The one structural traversal used to extract the stored connector prefix
is linear in the identical selected graph's finite vertex schedule. -/
theorem connectorTraversalChecks_le_vertexCount
    (node61 : Node61 (ctx := ctx)) (node63 : Node63 node61)
    (port : Port node61 node63) :
    Graph.TypeAReceiverEntryChannel.connectorTraversalChecks ctx.G.object
      node63.typeAProfile port
      (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)
      (TypeAFirstEntryCoordinates.firstEntry node61 node63 port) ≤
        ctx.G.object.input.vertices.card :=
  Graph.TypeAReceiverEntryChannel.connectorTraversalChecks_le_vertexCount
    ctx.G.object node63.typeAProfile port
    (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)
    (TypeAFirstEntryCoordinates.firstEntry node61 node63 port)

end Erdos64EG.Internal.TypeAReceiverEntryChannels
