import StructuralExhaustion.Graph.SupportIndexedFanMass

namespace StructuralExhaustion.Examples.SupportIndexedFanMass

open StructuralExhaustion

namespace FanMass

inductive Support
  | ordinaryShared
  | groupedShared
  | ordinarySeparate
  deriving DecidableEq

inductive Center
  | shared
  | separate
  deriving DecidableEq

inductive Occurrence
  | ordinaryShared
  | groupedShared
  | ordinarySeparate
  deriving DecidableEq

@[implicit_reducible] def supports : FinEnum Support :=
  @FinEnum.ofNodupList Support inferInstance
    [.ordinaryShared, .groupedShared, .ordinarySeparate]
    (by intro support; cases support <;> simp)
    (by simp)

@[implicit_reducible] def centers : FinEnum Center :=
  @FinEnum.ofNodupList Center inferInstance [.shared, .separate]
    (by intro center; cases center <;> simp)
    (by simp)

@[implicit_reducible] def occurrences : FinEnum Occurrence :=
  @FinEnum.ofNodupList Occurrence inferInstance
    [.ordinaryShared, .groupedShared, .ordinarySeparate]
    (by intro occurrence; cases occurrence <;> simp)
    (by simp)

def role : Support → Graph.SupportIndexedFanMass.Role
  | .ordinaryShared | .ordinarySeparate => .ordinary
  | .groupedShared => .grouped

def occurrenceSupport : Occurrence → Support
  | .ordinaryShared => .ordinaryShared
  | .groupedShared => .groupedShared
  | .ordinarySeparate => .ordinarySeparate

def occurrenceCenter : Occurrence → Center
  | .ordinaryShared | .groupedShared => .shared
  | .ordinarySeparate => .separate

def centerSurplus : Center → Nat
  | .shared => 3
  | .separate => 2

def deficit : Support → Nat
  | .ordinaryShared | .groupedShared => 6
  | .ordinarySeparate => 4

/-- A non-Erdős transfer fixture.  The shared center is deliberately reused
once in each role.  The two ordinary supports use different centers, so the
tagged `(role, center)` incidence remains injective. -/
def profile : Graph.SupportIndexedFanMass.Profile Support Center Occurrence where
  supports := supports
  centers := centers
  occurrences := occurrences
  role := role
  occurrenceSupport := occurrenceSupport
  occurrenceCenter := occurrenceCenter
  supportDecidableEq := inferInstance
  centerSurplus := centerSurplus
  deficit := deficit
  extracted := fun _ ↦ False
  extractedDecidable := fun _ ↦ inferInstance
  coefficient := 2
  localBound := by
    intro support _notExtracted
    cases support <;> native_decide
  withinRoleDisjoint := by
    intro left right equal
    cases left <;> cases right <;> simp [role, occurrenceSupport,
      occurrenceCenter] at equal ⊢

def problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ ↦ True
  rank := fun _ ↦ 0
  BranchState := fun _ ↦ Unit

def context : Core.BranchContext problem := ⟨(), trivial, ()⟩

example : profile.globalSurplus = 5 := by native_decide
example : profile.carriedTokenMass = 8 := by native_decide
example : profile.residualMass = 16 := by native_decide

/-- The repeated shared center contributes twice, but not three times. -/
example : profile.carriedTokenMass ≤ 2 * profile.globalSurplus :=
  profile.carriedTokenMass_le_two_mul_globalSurplus

example : profile.residualMass ≤
    (2 * profile.coefficient) * profile.globalSurplus :=
  profile.residualMass_le_two_mul_coefficient_mul_globalSurplus

example : (profile.run context).terminal = .capacity :=
  profile.run_terminal context

example : (profile.run context).outcome.Valid :=
  (profile.verifiedStage context).verified

example : profile.checks = 25 := by native_decide

example : profile.checks ≤
    3 * (profile.supports.card + 1) * (profile.occurrences.card + 1) :=
  (profile.verifiedStage context).quadraticWorkBound

end FanMass

end StructuralExhaustion.Examples.SupportIndexedFanMass
