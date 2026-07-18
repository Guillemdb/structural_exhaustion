import StructuralExhaustion.Core.Enumeration

namespace StructuralExhaustion.Core.SequentialCompatibleExtensionLedger

universe u v

/-- Local extension contract for a packing-order aggregate. -/
structure Profile : Type (max (u + 1) (v + 1)) where
  Window : Type u
  windows : Core.OrderedCollection Window
  Aggregate : Type v
  Valid : Aggregate → Prop
  initial : Aggregate
  initialValid : Valid initial
  Extension : Aggregate → Window → Type (max u v)
  extend : ∀ {aggregate window}, Extension aggregate window → Aggregate
  extendValid : ∀ {aggregate window}, Valid aggregate →
    (extension : Extension aggregate window) → Valid (extend extension)

/-- A proof-carrying packing-order run.  Its aggregate index forces the tail
of an accepted step to start at the actual extended aggregate; a rejected
step definitionally retains the old aggregate. -/
inductive Ledger (profile : Profile.{u, v}) : profile.Aggregate →
    List profile.Window → Type (max (u + 1) (v + 1)) where
  | nil {aggregate} (valid : profile.Valid aggregate) : Ledger profile aggregate []
  | accept {aggregate window tail}
      (valid : profile.Valid aggregate)
      (extension : profile.Extension aggregate window)
      (rest : Ledger profile (profile.extend extension) tail) :
      Ledger profile aggregate (window :: tail)
  | reject {aggregate window tail}
      (valid : profile.Valid aggregate)
      (absent : ¬Nonempty (profile.Extension aggregate window))
      (rest : Ledger profile aggregate tail) :
      Ledger profile aggregate (window :: tail)

namespace Ledger

def hot {profile aggregate windows} : Ledger profile aggregate windows →
    List profile.Window
  | .nil _ => []
  | @accept _ _ window _ _ _ rest => window :: rest.hot
  | .reject _ _ rest => rest.hot

def cold {profile aggregate windows} : Ledger profile aggregate windows →
    List profile.Window
  | .nil _ => []
  | .accept _ _ rest => rest.cold
  | @reject _ _ window _ _ _ rest => window :: rest.cold

def finalAggregate {profile aggregate windows} :
    Ledger profile aggregate windows → profile.Aggregate
  | @nil _ aggregate _ => aggregate
  | .accept _ _ rest => rest.finalAggregate
  | .reject _ _ rest => rest.finalAggregate

theorem finalValid {profile aggregate windows}
    (ledger : Ledger profile aggregate windows) :
    profile.Valid ledger.finalAggregate := by
  induction ledger with
  | nil valid => exact valid
  | accept _ _ _ ih => exact ih
  | reject _ _ _ ih => exact ih

theorem length_partition {profile aggregate windows}
    (ledger : Ledger profile aggregate windows) :
    ledger.hot.length + ledger.cold.length = windows.length := by
  induction ledger with
  | nil => simp [hot, cold]
  | accept _ _ _ ih => simp [hot, cold]; omega
  | reject _ _ _ ih => simp [hot, cold]; omega

theorem hot_sublist {profile aggregate windows}
    (ledger : Ledger profile aggregate windows) : ledger.hot.Sublist windows := by
  induction ledger with
  | nil => exact .slnil
  | accept _ _ _ ih => exact .cons_cons _ ih
  | reject _ _ _ ih => exact .cons _ ih

theorem cold_sublist {profile aggregate windows}
    (ledger : Ledger profile aggregate windows) : ledger.cold.Sublist windows := by
  induction ledger with
  | nil => exact .slnil
  | accept _ _ _ ih => exact .cons _ ih
  | reject _ _ _ ih => exact .cons_cons _ ih

theorem hot_nodup {profile aggregate windows}
    (ledger : Ledger profile aggregate windows) (nodup : windows.Nodup) :
    ledger.hot.Nodup := ledger.hot_sublist.nodup nodup

theorem cold_nodup {profile aggregate windows}
    (ledger : Ledger profile aggregate windows) (nodup : windows.Nodup) :
    ledger.cold.Nodup := ledger.cold_sublist.nodup nodup

end Ledger

noncomputable def run (profile : Profile) :
    Ledger profile profile.initial profile.windows.values := by
  let rec go (windows : List profile.Window) (aggregate : profile.Aggregate)
      (valid : profile.Valid aggregate) : Ledger profile aggregate windows :=
    match windows with
    | [] => .nil valid
    | window :: tail => by
        by_cases available : Nonempty (profile.Extension aggregate window)
        · let extension := Classical.choice available
          exact .accept valid extension
            (go tail (profile.extend extension) (profile.extendValid valid extension))
        · exact .reject valid available (go tail aggregate valid)
  exact go profile.windows.values profile.initial profile.initialValid

/-- The runner performs exactly one local extension decision per scheduled
window. -/
def checks (profile : Profile) : Nat := profile.windows.values.length

theorem checks_exact (profile : Profile) :
    checks profile = profile.windows.values.length := rfl

end StructuralExhaustion.Core.SequentialCompatibleExtensionLedger
