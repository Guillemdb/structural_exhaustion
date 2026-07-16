import StructuralExhaustion.Core.EnumerationCombinators
import StructuralExhaustion.Core.FiniteSearch

namespace StructuralExhaustion.Core.FiniteCodeCollision

universe u v

/-! Deterministic repetition search for an arbitrary finite observation code. -/

inductive OrderedCollision {Item : Type u} {Code : Type v}
    (code : Item → Code) : List Item → Type (max u v) where
  | here {first : Item} {tail : List Item}
      (second : Item) (member : second ∈ tail)
      (sameCode : code first = code second) :
      OrderedCollision code (first :: tail)
  | later {head : Item} {tail : List Item}
      (collision : OrderedCollision code tail) :
      OrderedCollision code (head :: tail)

namespace OrderedCollision

def first {Item : Type u} {Code : Type v} {code : Item → Code} {items} :
    OrderedCollision code items → Item
  | .here (first := first) _ _ _ => first
  | .later collision => collision.first

def second {Item : Type u} {Code : Type v} {code : Item → Code} {items} :
    OrderedCollision code items → Item
  | .here second _ _ => second
  | .later collision => collision.second

theorem first_mem {Item : Type u} {Code : Type v} {code : Item → Code} {items}
    (collision : OrderedCollision code items) : collision.first ∈ items := by
  induction collision with
  | here second member sameCode => simp [first]
  | later collision ih => exact List.mem_cons_of_mem _ ih

theorem second_mem {Item : Type u} {Code : Type v} {code : Item → Code} {items}
    (collision : OrderedCollision code items) : collision.second ∈ items := by
  induction collision with
  | here second member sameCode => exact List.mem_cons_of_mem _ member
  | later collision ih => exact List.mem_cons_of_mem _ ih

theorem code_eq {Item : Type u} {Code : Type v} {code : Item → Code} {items}
    (collision : OrderedCollision code items) :
    code collision.first = code collision.second := by
  induction collision with
  | here second member sameCode => exact sameCode
  | later collision ih => exact ih

theorem first_ne_second_of_nodup
    {Item : Type u} {Code : Type v} {code : Item → Code} {items}
    (collision : OrderedCollision code items) (nodup : items.Nodup) :
    collision.first ≠ collision.second := by
  induction collision with
  | @here first tail second member sameCode =>
      change first ≠ second
      intro equal
      apply (List.nodup_cons.mp nodup).1
      simpa [equal] using member
  | later collision ih =>
      exact ih (List.nodup_cons.mp nodup).2

/-- A collision is incompatible with a duplicate-free observed code list. -/
theorem false_of_codes_nodup
    {Item : Type u} {Code : Type v} {code : Item → Code} {items}
    (collision : OrderedCollision code items)
    (codesNodup : (items.map code).Nodup) : False := by
  induction collision with
  | here second member sameCode =>
      have fresh := (List.nodup_cons.mp codesNodup).1
      apply fresh
      exact List.mem_map.mpr ⟨second, member, sameCode.symm⟩
  | later collision ih =>
      exact ih (List.nodup_cons.mp codesNodup).2

end OrderedCollision

inductive Decision {Item : Type u} {Code : Type v}
    (code : Item → Code) (items : List Item) : Type (max u v) where
  | collision (result : OrderedCollision code items)
  | unique (codesNodup : (items.map code).Nodup)

/-- First collision using only equality of codes.  Unlike `decide`, this does
not materialize an enumeration of the whole code universe. -/
def decideWithDecEq {Item : Type u} {Code : Type v} [DecidableEq Code]
    (code : Item → Code) : (items : List Item) → Decision code items
  | [] => .unique (by simp)
  | first :: tail =>
      match Core.FiniteSearch.onList tail
          (fun second => code first = code second)
          (fun second => inferInstance) with
      | .found second member same => .collision (.here second member same)
      | .absent absent =>
          match decideWithDecEq code tail with
          | .collision collision => .collision (.later collision)
          | .unique tailNodup => .unique (by
              rw [List.map_cons, List.nodup_cons]
              refine ⟨?_, tailNodup⟩
              intro firstCodeMem
              obtain ⟨second, secondMem, same⟩ := List.mem_map.mp firstCodeMem
              exact absent second secondMem same.symm)

/-- First collision in inherited list order, or a proof that all observed
codes are distinct. -/
def decide {Item : Type u} {Code : Type v}
    (codes : FinEnum Code) (code : Item → Code) :
    (items : List Item) → Decision code items
  | [] => .unique (by simp)
  | first :: tail =>
      match Core.FiniteSearch.onList tail
          (fun second => code first = code second)
          (fun second => codes.decEq _ _) with
      | .found second member same => .collision (.here second member same)
      | .absent absent =>
          match decide codes code tail with
          | .collision collision => .collision (.later collision)
          | .unique tailNodup => .unique (by
              rw [List.map_cons, List.nodup_cons]
              refine ⟨?_, tailNodup⟩
              intro firstCodeMem
              obtain ⟨second, secondMem, same⟩ := List.mem_map.mp firstCodeMem
              exact absent second secondMem same.symm)

/-- A list longer than the finite code universe has an actual ordered
collision. -/
theorem collision_of_card_lt_length {Item : Type u} {Code : Type v}
    (codes : FinEnum Code) (code : Item → Code) (items : List Item)
    (large : codes.card < items.length) :
    Nonempty (OrderedCollision code items) := by
  cases decision : decide codes code items with
  | collision result => exact ⟨result⟩
  | unique codesNodup =>
      have bounded := Enumeration.length_le_elems_of_nodup codes codesNodup
      rw [List.length_map, FinEnum.orderedValues_length] at bounded
      exact (Nat.not_lt_of_ge bounded large).elim

end StructuralExhaustion.Core.FiniteCodeCollision
