import StructuralExhaustion.Core.LocalBooleanRealization

namespace Erdos64EG.Internal

open StructuralExhaustion

/-!
# Boolean full realization does not imply the curvature table product

This finite audit isolates the precise invalid bridge that must not be added
between nodes `[32]` and `[48]`.  One Boolean coordinate with the two literal
Boolean states is completely realized, but its two states cannot pay the
`543958 / 111286` curvature-table factor.  Consequently any sound node-[48]
producer must carry the stronger graph-owned safe/flat fibre ledger; Core
cannot infer it from Boolean full realization or quotient full rank.
-/

noncomputable def p13OneCoordinateBooleanSystem :
    Core.LocalBooleanRealization.System where
  Coordinate := Unit
  State := Bool
  coordinates := inferInstance
  states := Core.Enumeration.bool
  value := fun state _coordinate => state

theorem p13OneCoordinateBooleanSystem_hot :
    p13OneCoordinateBooleanSystem.HotCertificate := by
  constructor
  intro assignment
  refine ⟨assignment (), ?_⟩
  funext coordinate
  cases coordinate
  rfl

theorem p13OneCoordinateBooleanSystem_coordinateCard :
    p13OneCoordinateBooleanSystem.coordinates.card = 1 := by
  rfl

theorem p13OneCoordinateBooleanSystem_stateCard :
    p13OneCoordinateBooleanSystem.states.card = 2 := by
  rfl

/-- The exact node-[48] table factor already fails on a completely realized
one-coordinate Boolean system. -/
theorem p13BooleanFullRealization_not_curvatureTableProduct :
    ¬(543958 ^ p13OneCoordinateBooleanSystem.coordinates.card ≤
      111286 ^ p13OneCoordinateBooleanSystem.coordinates.card *
        p13OneCoordinateBooleanSystem.states.card) := by
  rw [p13OneCoordinateBooleanSystem_coordinateCard,
    p13OneCoordinateBooleanSystem_stateCard]
  omega

#print axioms p13OneCoordinateBooleanSystem_hot
#print axioms p13BooleanFullRealization_not_curvatureTableProduct

end Erdos64EG.Internal
