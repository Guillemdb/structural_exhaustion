import StructuralExhaustion.CT17.State

namespace StructuralExhaustion.CT17

universe uAmbient uBranch uTarget uOffset uPosition uValue

variable {P : Core.Problem.{uAmbient, uBranch}}
variable (S : Spec.{uAmbient, uBranch, uTarget, uOffset, uPosition, uValue} P)
variable (capability : Capability S)
variable (ctx : Core.BranchContext P)
variable (input : Input S capability ctx)

private def targetOffsetPresentation :
    Core.DependentEnumeration S.Target (fun _ => S.Offset) where
  indices := capability.targets
  fibres := fun _ => capability.offsets

private def incompatibleDecidable (target : S.Target) (offset : S.Offset) :
    Decidable (¬ S.Compatible ctx target offset) :=
  match capability.compatibleDecidable ctx target offset with
  | .isTrue compatible => .isFalse fun incompatible => incompatible compatible
  | .isFalse incompatible => .isTrue incompatible

inductive CompatibilityDecision where
  | incompatible (residual : IncompatibilityResidual S capability ctx input)
  | compatible (state : CompatibleState S capability ctx input)

/-- Exhaustive target-major, offset-minor compatibility search. -/
def analyzeCompatibility : CompatibilityDecision S capability ctx input :=
  match Core.FiniteSearch.dependentSearch
      (targetOffsetPresentation S capability)
      (fun target offset => ¬ S.Compatible ctx target offset)
      (incompatibleDecidable S capability ctx) with
  | .found target offset incompatible =>
      .incompatible ⟨target, offset, incompatible⟩
  | .absent absentProof => .compatible ⟨fun target offset =>
      match capability.compatibleDecidable ctx target offset with
      | .isTrue compatible => compatible
      | .isFalse incompatible =>
          (absentProof target offset incompatible).elim⟩

theorem analyzeCompatibility_sound :
    match analyzeCompatibility S capability ctx input with
    | .incompatible residual =>
        ¬ S.Compatible ctx residual.target residual.offset
    | .compatible _state =>
        ∀ target : S.Target, ∀ offset : S.Offset,
          S.Compatible ctx target offset := by
  cases analyzeCompatibility S capability ctx input with
  | incompatible residual => exact residual.incompatible
  | compatible state => exact state.compatible

inductive ScaleDecision (compatible : CompatibleState S capability ctx input) where
  | finite (state : FiniteScaleState S capability ctx input compatible)
  | orbit (state : OrbitScaleState S capability ctx input compatible)

/-- Literal arithmetic split; no proof-instance classifier selects a scale
branch. -/
def analyzeScale (compatible : CompatibleState S capability ctx input) :
    ScaleDecision S capability ctx input compatible :=
  if finite : input.scale ≤ capability.finiteScaleLimit then
    .finite ⟨finite⟩
  else
    .orbit ⟨Nat.lt_of_not_ge finite⟩

theorem analyzeScale_sound
    (compatible : CompatibleState S capability ctx input) :
    match analyzeScale S capability ctx input compatible with
    | .finite _state => input.scale ≤ capability.finiteScaleLimit
    | .orbit _state => capability.finiteScaleLimit < input.scale := by
  cases analyzeScale S capability ctx input compatible with
  | finite state => exact state.finite
  | orbit state => exact state.large

private def blockHitDecision (position : S.Position input.scale) :=
  Core.FiniteSearch.dependentSearch
    (targetOffsetPresentation S capability)
    (fun target offset =>
      S.blockValue ctx position offset = S.targetValue target)
    (fun target offset => capability.valueDecidableEq
      (S.blockValue ctx position offset) (S.targetValue target))

def survivesDecidable (position : S.Position input.scale) :
    Decidable (Survives S capability ctx input position) :=
  match blockHitDecision S capability ctx input position with
  | .found target offset equal =>
      .isFalse fun survives => survives target offset equal
  | .absent absentProof => .isTrue absentProof

def survivorList : List (S.Position input.scale) :=
  letI : DecidablePred (Survives S capability ctx input) :=
    survivesDecidable S capability ctx input
  (capability.positions input.scale).orderedValues.filter
    (Survives S capability ctx input)

/-- Exact, ordered survivor enumeration derived from the finite position
enumerator. -/
structure SurvivorEnumeration
    {compatible : CompatibleState S capability ctx input}
    (finite : FiniteScaleState S capability ctx input compatible) where
  survivors : List (S.Position input.scale)
  exact : survivors = survivorList S capability ctx input
  nodup : survivors.Nodup
  sound : ∀ position, position ∈ survivors →
    Survives S capability ctx input position
  complete : ∀ position, Survives S capability ctx input position →
    position ∈ survivors

def enumerateSurvivors
    {compatible : CompatibleState S capability ctx input}
    (finite : FiniteScaleState S capability ctx input compatible) :
    SurvivorEnumeration S capability ctx input finite where
  survivors := survivorList S capability ctx input
  exact := rfl
  nodup := by
    unfold survivorList
    exact (capability.positions input.scale).nodup_orderedValues.filter _
  sound := by
    intro position member
    unfold survivorList at member
    simp only [List.mem_filter] at member
    simpa using member.2
  complete := by
    intro position survives
    unfold survivorList
    simp only [List.mem_filter]
    exact ⟨capability.positions input.scale |>.mem_orderedValues position, by
      simp [survives]⟩

structure ExhaustedCertificate
    {compatible : CompatibleState S capability ctx input}
    {finite : FiniteScaleState S capability ctx input compatible} where
  enumeration : SurvivorEnumeration S capability ctx input finite
  exhausted : ∀ position : S.Position input.scale,
    ¬ Survives S capability ctx input position

structure SurvivorResidual
    {compatible : CompatibleState S capability ctx input}
    {finite : FiniteScaleState S capability ctx input compatible} where
  enumeration : SurvivorEnumeration S capability ctx input finite
  first : S.Position input.scale
  remaining : List (S.Position input.scale)
  exact : enumeration.survivors = first :: remaining

inductive SurvivorDecision
    {compatible : CompatibleState S capability ctx input}
    (finite : FiniteScaleState S capability ctx input compatible) where
  | exhausted (certificate : ExhaustedCertificate
      (S := S) (capability := capability) (ctx := ctx) (input := input)
      (compatible := compatible) (finite := finite))
  | survivors (residual : SurvivorResidual
      (S := S) (capability := capability) (ctx := ctx) (input := input)
      (compatible := compatible) (finite := finite))

def analyzeSurvivors
    {compatible : CompatibleState S capability ctx input}
    (finite : FiniteScaleState S capability ctx input compatible) :
    SurvivorDecision S capability ctx input finite :=
  let enumeration := enumerateSurvivors S capability ctx input finite
  match exact : enumeration.survivors with
  | [] => .exhausted {
      enumeration := enumeration
      exhausted := fun position survives => by
        have member := enumeration.complete position survives
        rw [exact] at member
        exact List.not_mem_nil member
    }
  | first :: remaining => .survivors {
      enumeration := enumeration
      first := first
      remaining := remaining
      exact := exact
    }

theorem analyzeSurvivors_sound
    {compatible : CompatibleState S capability ctx input}
    (finite : FiniteScaleState S capability ctx input compatible) :
    match analyzeSurvivors S capability ctx input finite with
    | .exhausted _certificate =>
        ∀ position : S.Position input.scale,
          ¬ Survives S capability ctx input position
    | .survivors residual =>
        residual.enumeration.survivors =
          residual.first :: residual.remaining ∧
        ∀ position, position ∈ residual.enumeration.survivors ↔
          Survives S capability ctx input position := by
  cases analyzeSurvivors S capability ctx input finite with
  | exhausted certificate => exact certificate.exhausted
  | survivors residual =>
      exact ⟨residual.exact, fun position => ⟨
        residual.enumeration.sound position,
        residual.enumeration.complete position⟩⟩

private def orbitHitDecision :=
  Core.FiniteSearch.dependentSearch
    (targetOffsetPresentation S capability)
    (fun target offset =>
      S.orbitValue ctx input.scale offset = S.targetValue target)
    (fun target offset => capability.valueDecidableEq
      (S.orbitValue ctx input.scale offset) (S.targetValue target))

structure TargetHitCertificate
    {compatible : CompatibleState S capability ctx input}
    (orbit : OrbitScaleState S capability ctx input compatible) where
  target : S.Target
  offset : S.Offset
  equal : S.orbitValue ctx input.scale offset = S.targetValue target

structure OrbitResidual
    {compatible : CompatibleState S capability ctx input}
    (orbit : OrbitScaleState S capability ctx input compatible) where
  values : List S.Value
  valuesExact : values = capability.offsets.orderedValues.map
    (S.orbitValue ctx input.scale)
  avoids : OrbitAvoids S capability ctx input

inductive ArithmeticDecision
    {compatible : CompatibleState S capability ctx input}
    (orbit : OrbitScaleState S capability ctx input compatible) where
  | targetHit (certificate : TargetHitCertificate S capability ctx input orbit)
  | residual (residual : OrbitResidual S capability ctx input orbit)

def analyzeArithmetic
    {compatible : CompatibleState S capability ctx input}
    (orbit : OrbitScaleState S capability ctx input compatible) :
    ArithmeticDecision S capability ctx input orbit :=
  match orbitHitDecision S capability ctx input with
  | .found target offset equal => .targetHit ⟨target, offset, equal⟩
  | .absent absentProof => .residual {
      values := capability.offsets.orderedValues.map (S.orbitValue ctx input.scale)
      valuesExact := rfl
      avoids := absentProof
    }

theorem analyzeArithmetic_sound
    {compatible : CompatibleState S capability ctx input}
    (orbit : OrbitScaleState S capability ctx input compatible) :
    match analyzeArithmetic S capability ctx input orbit with
    | .targetHit certificate =>
        S.orbitValue ctx input.scale certificate.offset =
          S.targetValue certificate.target
    | .residual residual =>
        residual.values = capability.offsets.orderedValues.map
          (S.orbitValue ctx input.scale) ∧
        OrbitAvoids S capability ctx input := by
  cases analyzeArithmetic S capability ctx input orbit with
  | targetHit certificate => exact certificate.equal
  | residual residual => exact ⟨residual.valuesExact, residual.avoids⟩

end StructuralExhaustion.CT17
