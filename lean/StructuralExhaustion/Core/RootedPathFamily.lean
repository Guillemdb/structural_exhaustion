import StructuralExhaustion.Core.RootedPathRelation

namespace StructuralExhaustion.Core.RootedPathFamily

universe u

variable {Vertex : Type u}

/-- Exact first divergence of two tails following a common root.  Equality of
the `take index` prefixes is the global certificate that no earlier branch was
skipped. -/
structure FirstBranch (left right : List Vertex) where
  index : Nat
  leftBound : index < left.length
  rightBound : index < right.length
  commonPrefix : left.take index = right.take index
  noEarlier : ∀ j (leftBound : j < left.length) (rightBound : j < right.length),
    j < index → left.get ⟨j, leftBound⟩ = right.get ⟨j, rightBound⟩
  distinctNext : left.get ⟨index, leftBound⟩ ≠ right.get ⟨index, rightBound⟩

/-- A literal head-by-head scan of two stored rooted-path tails.  Prefix
outcomes are retained rather than silently treated as equality. -/
inductive Comparison (left right : List Vertex) where
  | leftPrefix (evidence : List.IsPrefix left right)
  | rightPrefix (evidence : List.IsPrefix right left)
  | branch (certificate : FirstBranch left right)

def compare [DecidableEq Vertex] :
    (left right : List Vertex) → Comparison left right
  | [], right => .leftPrefix (by simp)
  | left, [] => .rightPrefix (by simp)
  | leftHead :: leftTail, rightHead :: rightTail =>
      if equal : leftHead = rightHead then
        match compare leftTail rightTail with
        | .leftPrefix evidence => .leftPrefix
            (List.cons_prefix_cons.mpr ⟨equal, evidence⟩)
        | .rightPrefix evidence => .rightPrefix
            (List.cons_prefix_cons.mpr ⟨equal.symm, evidence⟩)
        | .branch certificate => .branch {
            index := certificate.index + 1
            leftBound := by simpa using Nat.succ_lt_succ certificate.leftBound
            rightBound := by simpa using Nat.succ_lt_succ certificate.rightBound
            commonPrefix := by simp [List.take_succ_cons, equal, certificate.commonPrefix]
            noEarlier := by
              intro j leftBound rightBound before
              cases j with
              | zero => simpa using equal
              | succ j =>
                  simp only [List.get_cons_succ]
                  exact certificate.noEarlier j (Nat.lt_of_succ_lt_succ leftBound)
                    (Nat.lt_of_succ_lt_succ rightBound) (Nat.lt_of_succ_lt_succ before)
            distinctNext := by simpa using certificate.distinctNext }
      else
        .branch {
          index := 0
          leftBound := by simp
          rightBound := by simp
          commonPrefix := by simp
          noEarlier := by omega
          distinctNext := by simpa using equal }

/-- The scan performs at most one equality test per vertex occurrence in its
left input. -/
def checks [DecidableEq Vertex] : List Vertex → List Vertex → Nat
  | [], _ => 0
  | _, [] => 0
  | left :: leftTail, right :: rightTail =>
      if left = right then checks leftTail rightTail + 1 else 1

theorem checks_le_left [DecidableEq Vertex] (left right : List Vertex) :
    checks left right ≤ left.length := by
  induction left generalizing right with
  | nil => simp [checks]
  | cons head tail ih =>
      cases right with
      | nil => simp [checks]
      | cons other rest =>
          simp only [checks, List.length_cons]
          split
          · exact Nat.succ_le_succ (ih rest)
          · omega

end StructuralExhaustion.Core.RootedPathFamily
