import StructuralExhaustion.Graph.TypeAReceiverEntryChannel
import StructuralExhaustion.Core.RootedPathFamily

namespace StructuralExhaustion.Graph.TypeADeclaredContinuationCoordinate

open StructuralExhaustion
open TypeACanonicalReceiverTrace

universe u v w x y

variable {V : Type u} (object : FiniteObject V)
variable (profile : SupportProfile object)
variable (port : TypeAAnchoredReturnCoordinate.Port object profile)
variable (Label : Type v) (SupportDatum : Type w) (Value : Type x) (Fibre : Type y)

/-- Raw proof-carrying content of one declared continuation coordinate.  The
four response fields are deliberately semantic parameters: this graph layer
does not invent an Erdős interpretation for them. -/
structure Coordinate where
  anchored : TypeAAnchoredReturnCoordinate.AnchoredReturn object profile port
  first : TypeAFirstEntryCoordinate.FirstEntry object profile port anchored
  connector : TypeAReceiverEntryChannel.Connector object profile port anchored first
  channel : TypeAReceiverEntryChannel.Channel object profile port anchored first
  label : Label
  supportDatum : SupportDatum
  declaredSupport : Finset V
  value : Value
  fibreImage : Fibre

namespace Coordinate

variable {Label SupportDatum Value Fibre}

def word (coordinate : Coordinate object profile port Label SupportDatum Value Fibre) : List V :=
  coordinate.connector.path.support

def tail (coordinate : Coordinate object profile port Label SupportDatum Value Fibre) : List V :=
  coordinate.word object profile port |>.tail

@[simp] theorem word_eq
    (coordinate : Coordinate object profile port Label SupportDatum Value Fibre) :
    coordinate.word object profile port = coordinate.first.hit.before ++
      [coordinate.first.entry object profile port coordinate.anchored] :=
  coordinate.connector.support_eq

theorem entry_mem_word
    (coordinate : Coordinate object profile port Label SupportDatum Value Fibre) :
    coordinate.first.entry object profile port coordinate.anchored ∈
      coordinate.word object profile port := by
  rw [coordinate.word_eq object profile port]
  simp

theorem word_nodup
    (coordinate : Coordinate object profile port Label SupportDatum Value Fibre) :
    (coordinate.word object profile port).Nodup :=
  coordinate.connector.isPath.support_nodup

theorem word_cons_tail
    (coordinate : Coordinate object profile port Label SupportDatum Value Fibre) :
    coordinate.word object profile port =
      port.outside object profile :: coordinate.tail object profile port := by
  exact coordinate.connector.path.cons_tail_support.symm

/-- Two connector words through the fixed port cannot be in a strict prefix
relation.  The shorter endpoint is already in the Type A support, whereas all
nonterminal vertices of the longer connector precede its first support hit. -/
theorem eq_of_prefix
    (left right : Coordinate object profile port Label SupportDatum Value Fibre)
    (prefixEvidence : List.IsPrefix (left.word object profile port) (right.word object profile port)) :
    left.word object profile port = right.word object profile port := by
  have leftEntryInRight :
      left.first.entry object profile port left.anchored ∈ right.word object profile port :=
    prefixEvidence.subset (left.entry_mem_word object profile port)
  have entriesEqual :
      left.first.entry object profile port left.anchored =
        right.first.entry object profile port right.anchored := by
    by_contra unequal
    have outside := right.connector.support_before_outside object profile port
      right.anchored right.first _ leftEntryInRight unequal
    exact outside (left.first.entry_mem_support object profile port left.anchored)
  obtain ⟨suffix, appendEq⟩ := prefixEvidence
  cases suffix with
  | nil => simpa using appendEq
  | cons next rest =>
      have lastEq := congrArg List.getLast? appendEq
      have leftNonempty : left.word object profile port ≠ [] := by
        rw [left.word_eq object profile port]
        simp
      have entryInSuffix :
          right.first.entry object profile port right.anchored ∈ next :: rest := by
        have lastRight : (right.word object profile port).getLast? =
            some (right.first.entry object profile port right.anchored) := by
          rw [right.word_eq object profile port]
          simp
        have suffixLast : (next :: rest).getLast? =
            some (right.first.entry object profile port right.anchored) := by
          simpa [lastRight] using lastEq
        obtain ⟨initial, suffixEq⟩ := List.getLast?_eq_some_iff.mp suffixLast
        rw [suffixEq]
        simp
      have disjoint := List.nodup_append.mp (by
        rw [appendEq]
        exact right.word_nodup object profile port)
      exact (disjoint.2.2 _ (left.entry_mem_word object profile port) _
        (entriesEqual ▸ entryInSuffix) entriesEqual).elim

end Coordinate

abbrev Coord := Coordinate object profile port Label SupportDatum Value Fibre

/-- A supplied finite ordered family through one fixed completion port.  The
same-fibre clause is the exact hypothesis under which connector branching is
a continuation-class separator. -/
structure Family where
  coordinates : List (Coord object profile port Label SupportDatum Value Fibre)
  nonempty : coordinates ≠ []
  sameFibre : ∀ coordinate ∈ coordinates,
    coordinate.fibreImage = (coordinates.getLast nonempty).fibreImage

namespace Family

variable {Label SupportDatum Value Fibre}

def anchor
    (family : Family object profile port Label SupportDatum Value Fibre) :
    Coord object profile port Label SupportDatum Value Fibre :=
  family.coordinates.head family.nonempty

theorem anchor_mem
    (family : Family object profile port Label SupportDatum Value Fibre) :
    family.anchor object profile port ∈ family.coordinates := by
  exact List.head_mem family.nonempty

/-- Exact first separator against the reference connector.  The branch index
and its `noEarlier` field certify the globally earliest divergence on this
pair's common prefix. -/
structure Separator
    (family : Family object profile port Label SupportDatum Value Fibre) where
  left : Coord object profile port Label SupportDatum Value Fibre
  right : Coord object profile port Label SupportDatum Value Fibre
  leftMem : left ∈ family.coordinates
  rightMem : right ∈ family.coordinates
  right_eq_anchor : right = family.anchor object profile port
  branch : Core.RootedPathFamily.FirstBranch
    (left.tail object profile port) (right.tail object profile port)
  sameFibre : left.fibreImage = right.fibreImage
  noEarlierFamily : ∀ coordinate ∈ family.coordinates,
    ∀ j (coordinateBound : j < (coordinate.tail object profile port).length)
      (anchorBound : j < (family.anchor object profile port |>.tail object profile port).length),
      j < branch.index →
      (coordinate.tail object profile port).get ⟨j, coordinateBound⟩ =
        (family.anchor object profile port |>.tail object profile port).get
          ⟨j, anchorBound⟩

namespace Separator

/-- The public separator's pairwise clean-prefix statement.  The explicit
right-anchor identity prevents an arbitrary public constructor from attaching
the anchor-relative family theorem to an unrelated right coordinate. -/
theorem noEarlierPair
    (separator : Separator object profile port family) :
    ∀ j (leftBound : j < (separator.left.tail object profile port).length)
      (rightBound : j < (separator.right.tail object profile port).length),
      j < separator.branch.index →
      (separator.left.tail object profile port).get ⟨j, leftBound⟩ =
        (separator.right.tail object profile port).get ⟨j, rightBound⟩ := by
  exact separator.branch.noEarlier

/-- Global pairwise form of the argmin certificate: every two stored
coordinates agree before the selected separator index. -/
theorem noEarlierAnyPair
    (separator : Separator object profile port family) :
    ∀ a ∈ family.coordinates, ∀ b ∈ family.coordinates,
      ∀ j (aBound : j < (a.tail object profile port).length)
        (bBound : j < (b.tail object profile port).length),
        j < separator.branch.index →
        (a.tail object profile port).get ⟨j, aBound⟩ =
          (b.tail object profile port).get ⟨j, bBound⟩ := by
  intro a aMem b bMem j aBound bBound before
  have anchorIndexBound : separator.branch.index <
      ((family.anchor object profile port).tail object profile port).length := by
    have bound := separator.branch.rightBound
    simpa [separator.right_eq_anchor] using bound
  have anchorBound : j <
      ((family.anchor object profile port).tail object profile port).length :=
    lt_trans before anchorIndexBound
  have aAnchor := separator.noEarlierFamily a aMem j aBound anchorBound before
  have bAnchor := separator.noEarlierFamily b bMem j bBound anchorBound before
  exact aAnchor.trans bAnchor.symm

def vertex
    (separator : Separator object profile port family) : V :=
  separator.left.connector.path.getVert separator.branch.index

def leftNext
    (separator : Separator object profile port family) : V :=
  separator.left.connector.path.getVert (separator.branch.index + 1)

def rightNext
    (separator : Separator object profile port family) : V :=
  separator.right.connector.path.getVert (separator.branch.index + 1)

def commonPrefix
    (separator : Separator object profile port family) : List V :=
  port.outside object profile ::
    (separator.left.tail object profile port).take separator.branch.index

def leftTail
    (separator : Separator object profile port family) : List V :=
  (separator.left.tail object profile port).drop separator.branch.index

def rightTail
    (separator : Separator object profile port family) : List V :=
  (separator.right.tail object profile port).drop separator.branch.index

private theorem leftIndex_lt_length
    (separator : Separator object profile port family) :
    separator.branch.index < separator.left.connector.path.length := by
  simpa [Coordinate.tail, Coordinate.word,
    SimpleGraph.Walk.length_support] using separator.branch.leftBound

private theorem rightIndex_lt_length
    (separator : Separator object profile port family) :
    separator.branch.index < separator.right.connector.path.length := by
  simpa [Coordinate.tail, Coordinate.word,
    SimpleGraph.Walk.length_support] using separator.branch.rightBound

theorem leftTail_eq_cons
    (separator : Separator object profile port family) :
    separator.leftTail object profile port =
      separator.leftNext object profile port ::
        (separator.left.tail object profile port).drop (separator.branch.index + 1) := by
  rw [leftTail, List.drop_eq_getElem_cons separator.branch.leftBound]
  congr 1
  have supportBound : separator.branch.index + 1 <
      separator.left.connector.path.support.length := by
    simpa [Coordinate.tail, Coordinate.word] using separator.branch.leftBound
  simpa [leftNext, Coordinate.tail, Coordinate.word, List.get_eq_getElem,
    List.getElem_tail] using
      (SimpleGraph.Walk.support_getElem_eq_getVert
        separator.left.connector.path supportBound)

theorem rightTail_eq_cons
    (separator : Separator object profile port family) :
    separator.rightTail object profile port =
      separator.rightNext object profile port ::
        (separator.right.tail object profile port).drop (separator.branch.index + 1) := by
  rw [rightTail, List.drop_eq_getElem_cons separator.branch.rightBound]
  congr 1
  have supportBound : separator.branch.index + 1 <
      separator.right.connector.path.support.length := by
    simpa [Coordinate.tail, Coordinate.word] using separator.branch.rightBound
  simpa [rightNext, Coordinate.tail, Coordinate.word, List.get_eq_getElem,
    List.getElem_tail] using
      (SimpleGraph.Walk.support_getElem_eq_getVert
        separator.right.connector.path supportBound)

theorem left_adjacent
    (separator : Separator object profile port family) :
    (TypeAReceiverEntryChannel.DeletedGraph object profile port).Adj
      (separator.vertex object profile port)
      (separator.leftNext object profile port) :=
  separator.left.connector.path.adj_getVert_succ
    (separator.leftIndex_lt_length object profile port)

theorem right_vertex_eq
    (separator : Separator object profile port family) :
    separator.right.connector.path.getVert separator.branch.index =
      separator.vertex object profile port := by
  cases index : separator.branch.index with
  | zero => simp [vertex, index]
  | succ i =>
      have leftBound : i < (separator.left.tail object profile port).length := by
        have bound := separator.branch.leftBound
        rw [index] at bound
        omega
      have rightBound : i < (separator.right.tail object profile port).length := by
        have bound := separator.branch.rightBound
        rw [index] at bound
        omega
      have earlier := separator.branch.noEarlier i leftBound rightBound (by omega)
      have leftSupportBound : i + 1 < separator.left.connector.path.support.length := by
        simpa [Coordinate.tail, Coordinate.word] using leftBound
      have rightSupportBound : i + 1 < separator.right.connector.path.support.length := by
        simpa [Coordinate.tail, Coordinate.word] using rightBound
      have result : separator.right.connector.path.getVert (i + 1) =
          separator.left.connector.path.getVert (i + 1) := by
        calc
          separator.right.connector.path.getVert (i + 1) =
              separator.right.connector.path.support[i + 1] :=
            SimpleGraph.Walk.getVert_eq_support_getElem _ (by
              rw [SimpleGraph.Walk.length_support] at rightSupportBound
              omega)
          _ = separator.left.connector.path.support[i + 1] := by
            simpa [Coordinate.tail, Coordinate.word, List.get_eq_getElem,
              List.getElem_tail] using earlier.symm
          _ = separator.left.connector.path.getVert (i + 1) :=
            SimpleGraph.Walk.support_getElem_eq_getVert _ leftSupportBound
      simpa [index, vertex] using result

theorem right_adjacent
    (separator : Separator object profile port family) :
    (TypeAReceiverEntryChannel.DeletedGraph object profile port).Adj
      (separator.vertex object profile port)
      (separator.rightNext object profile port) := by
  rw [← separator.right_vertex_eq object profile port]
  exact separator.right.connector.path.adj_getVert_succ
    (separator.rightIndex_lt_length object profile port)

theorem distinct_next
    (separator : Separator object profile port family) :
    separator.leftNext object profile port ≠
      separator.rightNext object profile port := by
  intro equal
  apply separator.branch.distinctNext
  have leftBound : separator.branch.index + 1 <
      separator.left.connector.path.support.length := by
    simpa [Coordinate.tail, Coordinate.word] using separator.branch.leftBound
  have rightBound : separator.branch.index + 1 <
      separator.right.connector.path.support.length := by
    simpa [Coordinate.tail, Coordinate.word] using separator.branch.rightBound
  simpa [leftNext, rightNext, Coordinate.tail, Coordinate.word,
    List.get_eq_getElem, List.getElem_tail,
    SimpleGraph.Walk.support_getElem_eq_getVert _ leftBound,
    SimpleGraph.Walk.support_getElem_eq_getVert _ rightBound] using equal

theorem vertex_outside_support
    (separator : Separator object profile port family) :
    separator.vertex object profile port ∉ profile.support := by
  apply separator.left.connector.support_before_outside object profile port
    separator.left.anchored separator.left.first
  · exact separator.left.connector.path.getVert_mem_support _
  · intro equal
    have endpoint : separator.left.connector.path.getVert separator.branch.index =
        separator.left.connector.path.getVert separator.left.connector.path.length := by
      simpa [vertex] using equal
    have indexLe : separator.branch.index ≤ separator.left.connector.path.length :=
      Nat.le_of_lt (separator.leftIndex_lt_length object profile port)
    have indexEq := separator.left.connector.isPath.getVert_injOn
      (by simpa using indexLe) (by simp) endpoint
    exact (Nat.ne_of_lt (separator.leftIndex_lt_length object profile port)) indexEq

theorem left_ambient_adjacent
    (separator : Separator object profile port family) :
    object.graph.Adj (separator.vertex object profile port)
      (separator.leftNext object profile port) :=
  object.graph.deleteEdges_le _ (separator.left_adjacent object profile port)

theorem right_ambient_adjacent
    (separator : Separator object profile port family) :
    object.graph.Adj (separator.vertex object profile port)
      (separator.rightNext object profile port) :=
  object.graph.deleteEdges_le _ (separator.right_adjacent object profile port)

end Separator

inductive Outcome (family : Family object profile port Label SupportDatum Value Fibre) where
  | uniform
      (connectorCoincidence : ∀ coordinate ∈ family.coordinates,
        coordinate.word object profile port =
          (family.anchor object profile port).word object profile port)
      (sameFibreIdentification : ∀ coordinate ∈ family.coordinates,
        coordinate.fibreImage = (family.anchor object profile port).fibreImage)
  | separator (certificate : Separator object profile port family)

private inductive Inspected [DecidableEq V]
    (anchor coordinate : Coord object profile port Label SupportDatum Value Fibre) where
  | coincident (equal : coordinate.word object profile port = anchor.word object profile port)
  | branch (certificate : Core.RootedPathFamily.FirstBranch
      (coordinate.tail object profile port) (anchor.tail object profile port))

private def inspect [DecidableEq V]
    (anchor coordinate : Coord object profile port Label SupportDatum Value Fibre) :
    Inspected object profile port anchor coordinate := by
  cases Core.RootedPathFamily.compare
      (coordinate.tail object profile port) (anchor.tail object profile port) with
  | leftPrefix evidence =>
      exact .coincident (Coordinate.eq_of_prefix object profile port coordinate anchor (by
        rw [coordinate.word_cons_tail object profile port, anchor.word_cons_tail object profile port]
        exact List.cons_prefix_cons.mpr ⟨rfl, evidence⟩))
  | rightPrefix evidence =>
      exact .coincident (Coordinate.eq_of_prefix object profile port anchor coordinate (by
        rw [anchor.word_cons_tail object profile port, coordinate.word_cons_tail object profile port]
        exact List.cons_prefix_cons.mpr ⟨rfl, evidence⟩) |>.symm)
  | branch certificate => exact .branch certificate

private def AgreesBefore
    (anchor coordinate : Coord object profile port Label SupportDatum Value Fibre)
    (index : Nat) : Prop :=
  ∀ j (coordinateBound : j < (coordinate.tail object profile port).length)
    (anchorBound : j < (anchor.tail object profile port).length), j < index →
    (coordinate.tail object profile port).get ⟨j, coordinateBound⟩ =
      (anchor.tail object profile port).get ⟨j, anchorBound⟩

private theorem get_eq_of_list_eq {left right : List V} (equal : left = right)
    (j : Nat) (leftBound : j < left.length) (rightBound : j < right.length) :
    left.get ⟨j, leftBound⟩ = right.get ⟨j, rightBound⟩ := by
  subst right
  rfl

private inductive ScanResult [DecidableEq V]
    (anchor : Coord object profile port Label SupportDatum Value Fibre) :
    (coordinates : List (Coord object profile port Label SupportDatum Value Fibre)) → Type _ where
  | uniform {coordinates}
      (equal : ∀ coordinate ∈ coordinates,
        coordinate.word object profile port = anchor.word object profile port) :
      ScanResult anchor coordinates
  | separator {coordinates}
      (right : Coord object profile port Label SupportDatum Value Fibre)
      (rightMem : right ∈ coordinates)
      (branch : Core.RootedPathFamily.FirstBranch
        (right.tail object profile port) (anchor.tail object profile port))
      (global : ∀ coordinate ∈ coordinates,
        AgreesBefore object profile port anchor coordinate branch.index) :
      ScanResult anchor coordinates

private def scan [DecidableEq V]
    (anchor : Coord object profile port Label SupportDatum Value Fibre) :
    (coordinates : List (Coord object profile port Label SupportDatum Value Fibre)) →
      ScanResult object profile port anchor coordinates
  | [] => .uniform (by simp)
  | coordinate :: rest =>
      match inspect object profile port anchor coordinate, scan anchor rest with
      | .coincident equal, .uniform restEqual => .uniform (by
          intro item member
          rcases List.mem_cons.mp member with rfl | member
          · exact equal
          · exact restEqual item member)
      | .coincident equal, .separator right rightMem branch global =>
          .separator right (List.mem_cons_of_mem _ rightMem) branch (by
            intro item member
            rcases List.mem_cons.mp member with rfl | member
            · intro j itemBound anchorBound _before
              have tailsEqual := congrArg List.tail equal
              exact get_eq_of_list_eq tailsEqual j itemBound anchorBound
            · exact global item member)
      | .branch current, .uniform restEqual =>
          .separator coordinate (by simp) current (by
            intro item member
            rcases List.mem_cons.mp member with rfl | member
            · exact current.noEarlier
            · intro j itemBound anchorBound _before
              have equal := restEqual item member
              have tailsEqual := congrArg List.tail equal
              exact get_eq_of_list_eq tailsEqual j itemBound anchorBound)
      | .branch current, .separator right rightMem previous global =>
          if earlier : current.index ≤ previous.index then
            .separator coordinate (by simp) current (by
              intro item member
              rcases List.mem_cons.mp member with rfl | member
              · exact current.noEarlier
              · intro j itemBound anchorBound before
                exact global item member j itemBound anchorBound (lt_of_lt_of_le before earlier))
          else
            .separator right (List.mem_cons_of_mem _ rightMem) previous (by
              intro item member
              rcases List.mem_cons.mp member with rfl | member
              · intro j itemBound anchorBound before
                exact current.noEarlier j itemBound anchorBound
                  (lt_of_lt_of_le before (Nat.le_of_not_ge earlier))
              · exact global item member)

/-- Literal reference-trie scan of the supplied family.  It retains the least
branch index across all reference comparisons. -/
def classify
    (family : Family object profile port Label SupportDatum Value Fibre) :
    Outcome object profile port family := by
  letI : DecidableEq V := object.input.vertices.decEq
  let anchor := family.anchor object profile port
  cases scan object profile port anchor family.coordinates with
  | uniform equal =>
      exact .uniform equal (by
        intro coordinate member
        exact (family.sameFibre coordinate member).trans
          (family.sameFibre anchor family.anchor_mem).symm)
  | separator right rightMem branch global =>
      exact .separator {
        left := right
        right := anchor
        leftMem := rightMem
        rightMem := family.anchor_mem
        right_eq_anchor := rfl
        branch := branch
        sameFibre := (family.sameFibre right rightMem).trans
          (family.sameFibre anchor family.anchor_mem).symm
        noEarlierFamily := global }

def totalStoredPrefixLength
    (family : Family object profile port Label SupportDatum Value Fibre) : Nat :=
  (family.coordinates.map fun coordinate =>
    coordinate.tail object profile port |>.length).sum

def classificationChecks [DecidableEq V]
    (family : Family object profile port Label SupportDatum Value Fibre) : Nat :=
  (family.coordinates.map fun coordinate =>
    Core.RootedPathFamily.checks
      (coordinate.tail object profile port)
      (family.anchor object profile port |>.tail object profile port)).sum

theorem classificationChecks_le_totalStoredPrefixLength [DecidableEq V]
    (family : Family object profile port Label SupportDatum Value Fibre) :
    family.classificationChecks object profile port ≤
      family.totalStoredPrefixLength object profile port := by
  unfold classificationChecks totalStoredPrefixLength
  induction family.coordinates with
  | nil => simp
  | cons coordinate coordinates ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (Core.RootedPathFamily.checks_le_left _ _) ih

end Family

end StructuralExhaustion.Graph.TypeADeclaredContinuationCoordinate
