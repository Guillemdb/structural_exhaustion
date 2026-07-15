import StructuralExhaustion.Core.FiniteBlockerLedger
import StructuralExhaustion.Graph.SurplusPortActivation

namespace StructuralExhaustion.Graph.SurplusPairBlocker

open StructuralExhaustion

universe u

/-!
# Local blocker scan for two activated surplus demands

The scan is deliberately local to one supplied ordered pair. Candidate data
comes only from the two exact `Gamma` supports, the two root returns, the two
three-vertex port supports, and the proof-carrying suppressed cycles retained
by activation. Boundary-profile and target-response mismatches are absent for
an admissible rank quotient by the reusable CT15 admissibility contract; they
are proposal-audit exits, not unverified candidates silently inserted here.
-/

variable {input : PackedMinimumDegreeCycle.StaticInput}
  {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
  {setup : SurplusPortActivation.Setup input ctx}

/-- One canonically ordered pair supplied by the active-slot iterator. -/
structure Pair where
  first : SurplusPortActivation.Slot setup
  second : SurplusPortActivation.Slot setup
  distinct : first ≠ second

/-- The six manuscript blocker classes at node `[130]`.  The local structural
scan decides overlap, return, shoulder, and the retained suppression-cycle
class.  Profile and target mismatches belong to the raw quotient audit; the
admissible CT15 branch proves that neither can survive admission. -/
inductive Kind where
  | overlap
  | return
  | shoulder
  | profile
  | target
  | chord
  deriving DecidableEq, Repr

/-- A marked incidence of an unordered edge. -/
structure EdgeIncidence (V : Type u) where
  edge : Sym2 V
  endpoint : V
  endpoint_mem : endpoint ∈ edge

/-- The immediately graph-checkable blocker values at node `[130]`.
Edge values retain their incident end, and shoulder values retain both port
roles, exactly as required by the manuscript. -/
inductive Candidate (V : Type u) where
  | sharedSupportVertex (vertex : V)
  | sharedSupportEdge (incidence : EdgeIncidence V)
  | sharedReturnVertex (vertex : V)
  | sharedReturnEdge (incidence : EdgeIncidence V)
  | sharedPortVertex (vertex : V)
      (firstRole secondRole : SurplusPortActivation.PortRole)
  | suppressedChordFirst
  | suppressedChordSecond

namespace Candidate

def kind {V : Type u} : Candidate V → Kind
  | .sharedSupportVertex _ | .sharedSupportEdge _ => .overlap
  | .sharedReturnVertex _ | .sharedReturnEdge _ => .return
  | .sharedPortVertex _ _ _ => .shoulder
  | .suppressedChordFirst | .suppressedChordSecond => .chord

end Candidate

namespace Pair

variable (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
variable (pair : Pair (setup := setup))

noncomputable def firstDemand := stage.demand pair.first
noncomputable def secondDemand := stage.demand pair.second

noncomputable def firstReturnVertices : Finset ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact (SurplusPortActivation.rootReturn setup pair.first).path.support.toFinset

noncomputable def secondReturnVertices : Finset ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact (SurplusPortActivation.rootReturn setup pair.second).path.support.toFinset

noncomputable def vertexIndex (vertex : ctx.G.Vertex) : Nat := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact ctx.G.object.input.vertices.orderedValues.idxOf vertex

/-- Sort one supplied local vertex support by the declared ambient positions;
the scan touches only members of that support. -/
noncomputable def orderedVertices (vertices : Finset ctx.G.Vertex) :
    List ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact vertices.toList.mergeSort fun left right ↦
    decide (vertexIndex (ctx := ctx) left ≤ vertexIndex (ctx := ctx) right)

noncomputable def incidenceKey (incidence : EdgeIncidence ctx.G.Vertex) :
    Nat × Nat × Nat := by
  let endpoint := vertexIndex (ctx := ctx) incidence.endpoint
  let edgeKey := Sym2.lift ⟨fun left right ↦
      (min (vertexIndex (ctx := ctx) left) (vertexIndex (ctx := ctx) right),
        max (vertexIndex (ctx := ctx) left) (vertexIndex (ctx := ctx) right)),
    by
      intro left right
      simp only [min_comm, max_comm]⟩ incidence.edge
  exact (edgeKey.1, edgeKey.2, endpoint)

/-- Edge incidences in the lexicographic dart order induced by the declared
vertex schedule.  Each undirected edge contributes its two incident ends. -/
noncomputable def incidences (edges : Finset (Sym2 ctx.G.Vertex)) :
    List (EdgeIncidence ctx.G.Vertex) := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  let raw : List (EdgeIncidence ctx.G.Vertex) :=
    edges.toList.flatMap fun edge =>
    edge.toFinset.attach.toList.map fun endpoint =>
      { edge := edge, endpoint := endpoint.1,
        endpoint_mem := Sym2.mem_toFinset.mp endpoint.2 }
  exact raw.mergeSort fun left right ↦
    decide (incidenceKey (ctx := ctx) left ≤ incidenceKey (ctx := ctx) right)

/-- Every marked incidence emitted by the local incidence iterator retains
membership of its underlying edge in the supplied edge set. -/
theorem incidence_edge_mem (edges : Finset (Sym2 ctx.G.Vertex))
    (incidence : EdgeIncidence ctx.G.Vertex)
    (member : incidence ∈ incidences (ctx := ctx) edges) :
    incidence.edge ∈ edges := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  letI : DecidableEq (EdgeIncidence ctx.G.Vertex) := Classical.decEq _
  rw [incidences, List.mem_mergeSort] at member
  simp only [List.mem_flatMap, List.mem_map] at member
  rcases member with ⟨edge, edgeMember, endpoint, endpointMember, rfl⟩
  simpa using edgeMember

/-- Declared blocker order `(a)` support vertices/edges, `(b)` return
vertices/edges, `(c)` shoulder/buffer vertices.  Scanning the first support is
enough: the predicate checks membership in the second support. -/
noncomputable def rawCandidates : List (Candidate ctx.G.Vertex) := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact
    (orderedVertices (ctx := ctx)
      (pair.firstDemand stage).GammaVertices).map Candidate.sharedSupportVertex ++
    (incidences (ctx := ctx) (pair.firstDemand stage).GammaEdges).map
      Candidate.sharedSupportEdge ++
    (orderedVertices (ctx := ctx) pair.firstReturnVertices).map
      Candidate.sharedReturnVertex ++
    (incidences (ctx := ctx)
      (SurplusPortActivation.ActiveDemand.rootReturnEdges setup pair.first)).map
      Candidate.sharedReturnEdge ++
    (SurplusPortActivation.portRoles.flatMap fun firstRole =>
      SurplusPortActivation.portRoles.map fun secondRole =>
        Candidate.sharedPortVertex
          (SurplusPortActivation.portVertex setup pair.first firstRole)
          firstRole secondRole) ++
    [Candidate.suppressedChordFirst, Candidate.suppressedChordSecond]

/-- Exact open-branch predicate.  An open branch carries the critical
suppressed cycle selected by minimality; a triangular branch does not. -/
def openBranchValue {slot : SurplusPortActivation.Slot setup}
    (demand : SurplusPortActivation.ActiveDemand setup slot) : Prop :=
  match demand.response with
  | .open _ _ => True
  | .triangular _ _ => False

def OpenBranch {slot : SurplusPortActivation.Slot setup}
    (demand : SurplusPortActivation.ActiveDemand setup slot) : Prop :=
  openBranchValue demand

instance openBranchDecidable {slot : SurplusPortActivation.Slot setup}
    (demand : SurplusPortActivation.ActiveDemand setup slot) :
    Decidable (OpenBranch demand) := by
  unfold OpenBranch openBranchValue
  split <;> infer_instance

/-- Duplicate removal preserves first occurrence and therefore the declared
tag/carrier order. -/
noncomputable def candidates : Core.OrderedCollection (Candidate ctx.G.Vertex) := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  letI : DecidableEq (EdgeIncidence ctx.G.Vertex) := Classical.decEq _
  letI : DecidableEq (Candidate ctx.G.Vertex) := Classical.decEq _
  let values := (pair.rawCandidates stage).dedup
  exact {
    values := values
    nodup := List.nodup_dedup _
    decEq := inferInstance
  }

/-- An edge-incidence blocker retained by the candidate scan is an actual
ambient graph edge.  This closes the typing obligation for the primitive
incidence carrier; no application may inject an unauthored edge token. -/
theorem edgeCandidate_mem_edgeSet
    (candidate : Candidate ctx.G.Vertex)
    (member : candidate ∈ (pair.candidates stage).values)
    (incidence : EdgeIncidence ctx.G.Vertex)
    (edgeCase : candidate = .sharedSupportEdge incidence ∨
      candidate = .sharedReturnEdge incidence) :
    incidence.edge ∈ ctx.G.object.graph.edgeSet := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  letI : DecidableEq (EdgeIncidence ctx.G.Vertex) := Classical.decEq _
  letI : DecidableEq (Candidate ctx.G.Vertex) := Classical.decEq _
  have rawMember : candidate ∈ pair.rawCandidates stage := by
    simpa [candidates] using member
  rcases edgeCase with rfl | rfl
  · simp [rawCandidates] at rawMember
    exact (pair.firstDemand stage).GammaEdges_subset_edgeSet _
      (incidence_edge_mem (ctx := ctx)
        (pair.firstDemand stage).GammaEdges incidence rawMember)
  · simp [rawCandidates] at rawMember
    exact SurplusPortActivation.ActiveDemand.rootReturnEdges_subset_edgeSet
      setup pair.first _
      (incidence_edge_mem (ctx := ctx)
        (SurplusPortActivation.ActiveDemand.rootReturnEdges setup pair.first)
        incidence rawMember)

/-- Exact local predicate for structural blocker types `(a)`--`(c)` and the
proof-selected suppression-cycle type `(f)`. -/
noncomputable def Blocks (candidate : Candidate ctx.G.Vertex) : Prop :=
  match candidate with
  | .sharedSupportVertex vertex =>
      vertex ∈ (pair.secondDemand stage).GammaVertices
  | .sharedSupportEdge incidence =>
      incidence.edge ∈ (pair.secondDemand stage).GammaEdges
  | .sharedReturnVertex vertex =>
      vertex ∈ pair.secondReturnVertices
  | .sharedReturnEdge incidence =>
      incidence.edge ∈ SurplusPortActivation.ActiveDemand.rootReturnEdges
        setup pair.second
  | .sharedPortVertex vertex _firstRole secondRole =>
      vertex = SurplusPortActivation.portVertex setup pair.second secondRole
  | .suppressedChordFirst => OpenBranch (pair.firstDemand stage)
  | .suppressedChordSecond => OpenBranch (pair.secondDemand stage)

noncomputable def profile :
    Core.FiniteBlockerLedger.Profile (Pair (setup := setup))
      (Candidate ctx.G.Vertex) where
  candidates := fun current ↦ current.candidates stage
  Blocks := fun current candidate ↦ current.Blocks stage candidate
  blocksDecidable := by
    intro current candidate
    letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
    unfold Blocks
    cases candidate <;> infer_instance

/-- The exact proof-carrying value of blocker type `(f)`.  The used chord set
is the singleton corresponding to this slot; the cycle and its chord use are
the values retained by the activation/minimality producer. -/
structure ChordBlocker where
  slot : SurplusPortActivation.Slot setup
  isOpen : SurplusPortActivity.portType ctx.G.object
    setup.deletionCritical slot = .open
  critical : OpenPortSuppression.Setup.CriticalCycle
    (SurplusPortActivation.openSuppressionSetup setup slot isOpen)
    input.LengthOK :=
      SurplusPortActivation.openCriticalCycleFromMinimality setup slot isOpen

/-- Every successful chord tag reconstructs the manuscript's supplied
suppression-cycle tuple without a cycle search. -/
theorem chordBlocker_of_blocks
    (candidate : Candidate ctx.G.Vertex)
    (kind : candidate.kind = .chord)
    (blocks : pair.Blocks stage candidate) :
    Nonempty (ChordBlocker (input := input) (ctx := ctx) (setup := setup)) := by
  cases candidate with
  | suppressedChordFirst =>
      unfold Blocks OpenBranch at blocks
      unfold openBranchValue at blocks
      cases responseEq : (pair.firstDemand stage).response
      · rename_i isOpen response
        exact ⟨{
          slot := pair.first
          isOpen := isOpen
          critical :=
            SurplusPortActivation.openCriticalCycleFromMinimality
              setup pair.first isOpen
        }⟩
      · simp [responseEq] at blocks
  | suppressedChordSecond =>
      unfold Blocks OpenBranch at blocks
      unfold openBranchValue at blocks
      cases responseEq : (pair.secondDemand stage).response
      · rename_i isOpen response
        exact ⟨{
          slot := pair.second
          isOpen := isOpen
          critical :=
            SurplusPortActivation.openCriticalCycleFromMinimality
              setup pair.second isOpen
        }⟩
      · simp [responseEq] at blocks
  | sharedSupportVertex vertex => simp [Candidate.kind] at kind
  | sharedSupportEdge incidence => simp [Candidate.kind] at kind
  | sharedReturnVertex vertex => simp [Candidate.kind] at kind
  | sharedReturnEdge incidence => simp [Candidate.kind] at kind
  | sharedPortVertex vertex firstRole secondRole =>
      simp [Candidate.kind] at kind

/-- Candidate kinds `(d)` and `(e)` cannot be produced by the admissible
pair scan: admissibility already proves profile preservation and universal
target response before CT15 regards a quotient as rank-reducing. -/
theorem candidate_kind_ne_profile_target
    (candidate : Candidate ctx.G.Vertex) :
    candidate.kind ≠ .profile ∧ candidate.kind ≠ .target := by
  cases candidate <;> simp [Candidate.kind]

/-- Canonical local first-blocker execution. -/
noncomputable def run := (profile stage).run pair

/-- The exact local state space: a first structural blocker or a residual
certifying absence of every declared `(a)`--`(c)` and `(f)` candidate. -/
theorem stateSpace :
    (∃ hit : Core.FiniteSearch.FirstHit (pair.candidates stage).values
        (pair.Blocks stage), pair.run stage = .found hit) ∨
      (∃ none : ∀ candidate : Candidate ctx.G.Vertex,
          candidate ∈ (pair.candidates stage).values →
            ¬pair.Blocks stage candidate,
        pair.run stage = .absent none) :=
  (profile stage).stateSpace pair

/-- Work is exactly one membership check per candidate in the two supplied
local supports. -/
theorem checks_linear :
    (profile stage).checks pair ≤ (pair.candidates stage).values.length + 1 :=
  (profile stage).checks_linear pair

/-- A local-clear result excludes all structural and proof-selected chord
blockers. The CT15 admissible-quotient pass turns this residual into a free
pair-response coordinate. -/
structure StructuralClear : Prop where
  absent : ∀ candidate : Candidate ctx.G.Vertex,
    candidate ∈ (pair.candidates stage).values →
      ¬pair.Blocks stage candidate

theorem structuralClear_of_absent
    (none : ∀ candidate : Candidate ctx.G.Vertex,
      candidate ∈ (pair.candidates stage).values →
        ¬pair.Blocks stage candidate) :
    pair.StructuralClear stage :=
  ⟨none⟩

/-- Typed route output for the structural part of node `[130]`.  The clear
constructor is the exact input consumed by the admitted-response CT15 pass. -/
inductive StructuralDecision where
  | blocked (hit : Core.FiniteSearch.FirstHit
      (pair.candidates stage).values (pair.Blocks stage))
  | pending (clear : pair.StructuralClear stage)

noncomputable def decideStructural : pair.StructuralDecision stage :=
  match pair.run stage with
  | .found hit => .blocked hit
  | .absent absentProof =>
      .pending (pair.structuralClear_of_absent stage absentProof)

namespace StructuralDecision

def Valid : pair.StructuralDecision stage → Prop
  | .blocked hit =>
      hit.value ∈ (pair.candidates stage).values ∧
        pair.Blocks stage hit.value ∧
        ∀ candidate ∈ hit.before, ¬pair.Blocks stage candidate
  | .pending _clear =>
      ∀ candidate ∈ (pair.candidates stage).values,
        ¬pair.Blocks stage candidate

theorem valid_decideStructural :
    (pair.decideStructural stage).Valid := by
  unfold Pair.decideStructural
  generalize equation : pair.run stage = result
  cases result with
  | found hit =>
    exact (profile stage).found_sound pair hit
  | absent absentProof =>
    exact absentProof

end StructuralDecision

end Pair

end StructuralExhaustion.Graph.SurplusPairBlocker
