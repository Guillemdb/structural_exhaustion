import StructuralExhaustion.Graph.TypeACompletionPortCoordinate
import StructuralExhaustion.Core.FiniteSearch
import StructuralExhaustion.Core.EnumerationCombinators
import StructuralExhaustion.Core.WorkBudget

namespace StructuralExhaustion.Graph.TypeAReceiverSaturation

open StructuralExhaustion
open TypeACanonicalReceiverTrace

universe u

variable {V : Type u} (object : FiniteObject V)
variable (profile : SupportProfile object)

abbrev Receiver := TypeACompletionPortCoordinate.Receiver object profile
abbrev Cubic := profile.Cubic object

/-- Exact paper load `L(w)`: the number of stored internal cubic sources whose
canonical receiver is `w`. -/
noncomputable def load (receiver : Receiver object profile) : Nat := by
  letI : DecidableEq profile.Vertex :=
    (profile.supportObject object).input.vertices.decEq
  exact ((profile.cubics object).orderedValues.filter fun cubic =>
    decide ((profile.receiverSelection object cubic).vertex = receiver.1)).length

/-- Exact paper deficiency `q(w)=3-d_X(w)`. -/
noncomputable def missingPorts (receiver : Receiver object profile) : Nat :=
  3 - (profile.supportObject object).degree receiver.1

noncomputable def Saturated (receiver : Receiver object profile) : Prop :=
  4 * missingPorts object profile receiver ≤ load object profile receiver

noncomputable def saturatedDecidable (receiver : Receiver object profile) :
    Decidable (Saturated object profile receiver) := Classical.dec _

abbrev Result := Core.FiniteSearch.FirstResult
  (TypeACompletionPortCoordinate.receivers object profile).orderedValues
  (Saturated object profile)

/-- Node [89]: inspect the actual receiver schedule in support order and
return its first saturated receiver, or an exhaustive unsaturated proof. -/
noncomputable def run : Result object profile :=
  Core.FiniteSearch.first
    (TypeACompletionPortCoordinate.receivers object profile)
    (Saturated object profile)
    (saturatedDecidable object profile)

theorem run_total :
    match run object profile with
    | .found hit =>
        Saturated object profile hit.value
    | .absent _ =>
        ∀ receiver : Receiver object profile,
          ¬Saturated object profile receiver := by
  unfold run
  simpa using Core.FiniteSearch.first_total
    (TypeACompletionPortCoordinate.receivers object profile)
    (Saturated object profile)
    (saturatedDecidable object profile)

theorem unsaturated_bound {receiver : Receiver object profile}
    (notSaturated : ¬Saturated object profile receiver) :
    load object profile receiver ≤ 4 * missingPorts object profile receiver - 1 := by
  unfold Saturated at notSaturated
  omega

/-- One load-membership comparison for every receiver/cubic pair. -/
noncomputable def checks : Nat :=
  (TypeACompletionPortCoordinate.receivers object profile).card *
    (profile.cubics object).card

theorem receivers_card_le_vertices :
    (TypeACompletionPortCoordinate.receivers object profile).card ≤
      object.input.vertices.card :=
  (TypeACompletionPortCoordinate.receivers_card_le_support object profile).trans
    (by
      rw [← object.card_vertexFinset]
      exact Finset.card_le_card fun vertex _ => object.mem_vertexFinset vertex)

theorem cubics_card_le_vertices :
    (profile.cubics object).card ≤ object.input.vertices.card := by
  have subtypeBound : (profile.cubics object).card ≤
      (profile.supportObject object).input.vertices.card := by
    unfold TypeACanonicalReceiverTrace.SupportProfile.cubics
    exact Core.Enumeration.subtype_card_le
      (profile.supportObject object).input.vertices
      (fun vertex => (profile.supportObject object).degree vertex = 3)
      (profile.cubicDecidable object)
  calc
    (profile.cubics object).card ≤
        (profile.supportObject object).input.vertices.card := subtypeBound
    _ = profile.support.card := object.induceFinset_vertexCount profile.support
    _ ≤ object.input.vertices.card := by
      rw [← object.card_vertexFinset]
      exact Finset.card_le_card fun vertex _ => object.mem_vertexFinset vertex

theorem checks_quadratic :
    checks object profile ≤ object.input.vertices.card ^ 2 := by
  unfold checks
  simpa [pow_two] using Nat.mul_le_mul
    (receivers_card_le_vertices object profile)
    (cubics_card_le_vertices object profile)

end StructuralExhaustion.Graph.TypeAReceiverSaturation
