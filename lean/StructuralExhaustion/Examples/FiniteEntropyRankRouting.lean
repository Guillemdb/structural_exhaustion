import StructuralExhaustion.Core.FiniteEntropyRankRouting
import StructuralExhaustion.Graph.LocalBooleanWindowLedger

namespace StructuralExhaustion.Examples.FiniteEntropyRankRouting

open StructuralExhaustion

def hotProfile : Core.FiniteEntropyRankRouting.Profile where
  system := Graph.LocalBooleanWindowLedger.Fixture.hotSystem
  Repetitive := False
  repetitiveDecidable := inferInstance
  RankPayload := Unit
  rankOfRepetitive := False.elim

def repetitiveSystem : Core.LocalBooleanRealization.System where
  Coordinate := Bool
  State := Bool
  coordinates := Core.Enumeration.bool
  states := Core.Enumeration.bool
  value := fun _state _coordinate => false

def repetitiveProfile : Core.FiniteEntropyRankRouting.Profile where
  system := repetitiveSystem
  Repetitive := True
  repetitiveDecidable := inferInstance
  RankPayload := Unit
  rankOfRepetitive := fun _ => ()

def largeProfile : Core.FiniteEntropyRankRouting.Profile where
  system := Graph.LocalBooleanWindowLedger.Fixture.coldSystem
  Repetitive := False
  repetitiveDecidable := inferInstance
  RankPayload := Unit
  rankOfRepetitive := False.elim

example : ∃ route, hotProfile.run = .entropy route := by
  exact ⟨_, rfl⟩

example : ∃ route, repetitiveProfile.run = .repetitiveRank route := by
  exact ⟨_, rfl⟩

example : ∃ residual, largeProfile.run = .largeBudget residual := by
  exact ⟨_, rfl⟩

end StructuralExhaustion.Examples.FiniteEntropyRankRouting
