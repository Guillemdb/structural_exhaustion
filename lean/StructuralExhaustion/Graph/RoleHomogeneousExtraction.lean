import StructuralExhaustion.CT9.ExactLedger
import StructuralExhaustion.Graph.SurplusTokenRole

namespace StructuralExhaustion.Graph.RoleHomogeneousExtraction

open StructuralExhaustion

universe uAmbient uBranch uItem

/-!
# Local role-homogeneous extraction

The input is one already selected same-token matching or star.  CT9 scans
only that supplied edge list and its 36 exact role labels.  It never builds
the token-fibre graph or searches the ambient pair universe.
-/

abbrev capability (P : Core.Problem.{uAmbient, uBranch}) (Item : Type uItem)
    (role : Item → SurplusTokenRole.Role) : CT9.Capability P :=
  CT9.ExactLedger.capability P Item SurplusTokenRole.Role
    SurplusTokenRole.roleEnum role

abbrev input {P : Core.Problem.{uAmbient, uBranch}} {Item : Type uItem}
    {role : Item → SurplusTokenRole.Role}
    (context : Core.BranchContext P) (items : Core.OrderedCollection Item) :
    CT9.Input (capability P Item role) :=
  CT9.ExactLedger.input (capacity := fun _ => 0) context items

theorem exact_partition {P : Core.Problem.{uAmbient, uBranch}}
    {Item : Type uItem} (role : Item → SurplusTokenRole.Role)
    (context : Core.BranchContext P) (items : Core.OrderedCollection Item) :
    items.values.length =
      (SurplusTokenRole.roleEnum.orderedValues.map fun label =>
        CT9.fibreCount (capability P Item role) (input context items) label).sum :=
  CT9.ExactLedger.noOvercounting SurplusTokenRole.roleEnum role context items

/-- More than `36*(K-1)` edges in one supplied same-token pattern forces at
least `K` edges of one exact role. -/
theorem exists_role_fibre_of_overload
    {P : Core.Problem.{uAmbient, uBranch}} {Item : Type uItem}
    (role : Item → SurplusTokenRole.Role)
    (context : Core.BranchContext P) (items : Core.OrderedCollection Item)
    (K : Nat) (large : 36 * (K - 1) < items.values.length) :
    ∃ label : SurplusTokenRole.Role,
      K ≤ CT9.fibreCount (capability P Item role) (input context items) label := by
  by_contra absent
  push Not at absent
  have bounded : items.values.length ≤ (K - 1) *
      SurplusTokenRole.roleEnum.card :=
    CT9.ExactLedger.bounded_total SurplusTokenRole.roleEnum role
      context items (K - 1) fun label => by
        have strict := absent label
        change CT9.fibreCount
          (CT9.ExactLedger.capability P Item SurplusTokenRole.Role
            SurplusTokenRole.roleEnum role)
          (CT9.ExactLedger.input (capacity := fun _ => 0) context items)
          label < K at strict
        omega
  rw [SurplusTokenRole.role_card] at bounded
  have : items.values.length ≤ 36 * (K - 1) := by omega
  omega

end StructuralExhaustion.Graph.RoleHomogeneousExtraction
