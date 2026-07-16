import StructuralExhaustion.Graph.TypeAEntryBudgetCoordinate

namespace StructuralExhaustion.Examples.TypeAEntryBudgetCoordinate

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {V : Type u} (object : FiniteObject V)
variable (profile : TypeACanonicalReceiverTrace.SupportProfile object)

/-! A non-Erdős transfer of the local entry-budget argument.  It applies to
any finite ambient-cubic graph and any supplied core-free connected support;
no power-of-two target or Erdős-specific constant is used. -/

example
    (terminal candidate : TypeAEntryBudgetCoordinate.Port object profile)
    (degreeTwo : (profile.supportObject object).degree
      (terminal.receiver object profile) = 2)
    (sameReceiver : candidate.receiver object profile =
      terminal.receiver object profile) :
    candidate = terminal :=
  TypeAEntryBudgetCoordinate.port_eq_of_same_degree_two_receiver object profile
    terminal candidate degreeTwo sameReceiver

example
    (terminal : TypeAEntryBudgetCoordinate.Port object profile)
    (degreeTwo : (profile.supportObject object).degree
      (terminal.receiver object profile) = 2)
    (anchored : TypeAAnchoredReturnCoordinate.AnchoredReturn object profile terminal)
    (first : TypeAFirstEntryCoordinate.FirstEntry object profile terminal anchored) :
    (TypeAEntryBudgetCoordinate.firstEntryPort object profile terminal anchored first).receiver
        object profile ≠ terminal.receiver object profile :=
  TypeAEntryBudgetCoordinate.firstEntry_receiver_ne_terminal object profile
    terminal degreeTwo anchored first

example
    (terminal : TypeAEntryBudgetCoordinate.Port object profile)
    (degreeTwo : (profile.supportObject object).degree
      (terminal.receiver object profile) = 2) :
    (TypeAEntryBudgetCoordinate.possibleFirstEntryEdges object profile terminal).ncard ≤
      TypeAEntryBudgetCoordinate.otherReceiverCapacity object profile terminal :=
  TypeAEntryBudgetCoordinate.possibleFirstEntryEdges_ncard_le_otherReceiverCapacity
    object profile terminal degreeTwo

example :
    TypeACompletionPortCoordinate.visibleChecks object profile +
        TypeAEntryBudgetCoordinate.additionalChecks ≤
      4 * object.input.vertices.card :=
  TypeAEntryBudgetCoordinate.totalVisibleChecks_polynomial object profile

end StructuralExhaustion.Examples.TypeAEntryBudgetCoordinate
