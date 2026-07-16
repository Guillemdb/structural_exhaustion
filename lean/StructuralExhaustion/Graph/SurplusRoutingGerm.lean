import StructuralExhaustion.Core.RootedPathRelation
import StructuralExhaustion.Graph.FiniteConnector
import StructuralExhaustion.Graph.OrderedBFSTree
import StructuralExhaustion.Graph.RootIncidence
import StructuralExhaustion.Graph.SurplusRoutingSupport

namespace StructuralExhaustion.Graph.SurplusRoutingGerm

open StructuralExhaustion

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}

abbrev Pair := SurplusPairResponse.ScheduledPair (setup := setup)
abbrev Token := SurplusCapacityTokenRouting.Token (ctx := ctx) (setup := setup)

def endpointSupport (pair : Pair (setup := setup)) (first : Bool) :
    Finset ctx.G.Vertex :=
  if first then SurplusPortActivation.PortSupport setup pair.first
  else SurplusPortActivation.PortSupport setup pair.second

theorem endpointSupport_nonempty (pair : Pair (setup := setup)) (first : Bool) :
    (endpointSupport (setup := setup) pair first).Nonempty := by
  cases first with
  | false =>
      refine ⟨SurplusPortActivation.portVertex setup pair.second .buffer, ?_⟩
      exact SurplusPortActivation.portVertex_mem_portSupport
        setup pair.second .buffer
  | true =>
      refine ⟨SurplusPortActivation.portVertex setup pair.first .buffer, ?_⟩
      exact SurplusPortActivation.portVertex_mem_portSupport
        setup pair.first .buffer

/-- The literal carrier retained before any later connected-closure or BFS
construction.  It records only supports already certified by predecessors. -/
noncomputable def retainedCarrier
    (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    (token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup))
    (branch : SurplusRoutingSupport.PairBranch stage pair) :
    Finset ctx.G.Vertex := by
  classical
  exact SurplusRoutingSupport.tokenSupport (ctx := ctx) (setup := setup) token ∪
    (stage.demand pair.first).GammaVertices ∪
    (stage.demand pair.second).GammaVertices ∪
    SurplusPortActivation.PortSupport setup pair.first ∪
    SurplusPortActivation.PortSupport setup pair.second ∪
    branch.support stage

/-- Provenance for every summand of the retained carrier.  This is a support
statement only; it asserts neither connectivity nor a restricted BFS. -/
theorem retainedCarrier_provenance
    (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    (token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup))
    (branch : SurplusRoutingSupport.PairBranch stage pair) :
    SurplusRoutingSupport.tokenSupport (ctx := ctx) (setup := setup) token ⊆
        retainedCarrier stage token pair branch ∧
      (stage.demand pair.first).GammaVertices ⊆
        retainedCarrier stage token pair branch ∧
      (stage.demand pair.second).GammaVertices ⊆
        retainedCarrier stage token pair branch ∧
      SurplusPortActivation.PortSupport setup pair.first ⊆
        retainedCarrier stage token pair branch ∧
      SurplusPortActivation.PortSupport setup pair.second ⊆
        retainedCarrier stage token pair branch ∧
      branch.support stage ⊆ retainedCarrier stage token pair branch := by
  classical
  constructor
  · intro vertex membership
    simp [retainedCarrier, membership]
  constructor
  · intro vertex membership
    simp [retainedCarrier, membership]
  constructor
  · intro vertex membership
    simp [retainedCarrier, membership]
  constructor
  · intro vertex membership
    simp [retainedCarrier, membership]
  constructor <;> intro vertex membership <;>
    simp [retainedCarrier, membership]

theorem tokenRoot_mem_retainedCarrier
    (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    (token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup))
    (branch : SurplusRoutingSupport.PairBranch stage pair) :
    SurplusRoutingSupport.tokenRoot (ctx := ctx) (setup := setup) token ∈
      retainedCarrier stage token pair branch := by
  exact (retainedCarrier_provenance stage token pair branch).1
    (SurplusRoutingSupport.tokenRoot_mem token)

/-! ## Repaired root-BFS closure candidate

This section is a generic repair candidate below the manuscript node.  It
does not assert P13, execute a semantic consumer, or integrate node 144.
-/

noncomputable def bfsProfile (token : Token (ctx := ctx) (setup := setup)) :
    OrderedBFSTree.Profile ctx.G.object where
  root := SurplusRoutingSupport.tokenRoot (ctx := ctx) (setup := setup) token

abbrev bfsPreconnected : ctx.G.object.graph.Preconnected :=
  input.preconnected_of_noProperCore ctx

/-- Retained carrier closed under the canonical rooted BFS paths to all its
vertices. -/
noncomputable def Zstar
    (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    (token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup))
    (branch : SurplusRoutingSupport.PairBranch stage pair) :
    Finset ctx.G.Vertex := by
  classical
  let carrier := retainedCarrier stage token pair branch
  exact carrier ∪ carrier.biUnion fun vertex =>
    ((bfsProfile token).treeWalk bfsPreconnected vertex).support.toFinset

theorem retainedCarrier_subset_Zstar
    (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    (token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup))
    (branch : SurplusRoutingSupport.PairBranch stage pair) :
    retainedCarrier stage token pair branch ⊆ Zstar stage token pair branch := by
  classical
  intro vertex member
  simp [Zstar, member]

theorem tokenRoot_mem_Zstar
    (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    (token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup))
    (branch : SurplusRoutingSupport.PairBranch stage pair) :
    SurplusRoutingSupport.tokenRoot (ctx := ctx) (setup := setup) token ∈
      Zstar stage token pair branch :=
  retainedCarrier_subset_Zstar stage token pair branch
    (tokenRoot_mem_retainedCarrier stage token pair branch)

/-- Every retained summand is contained in the repaired closure. -/
theorem retained_summands_subset_Zstar
    (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    (token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup))
    (branch : SurplusRoutingSupport.PairBranch stage pair) :
    SurplusRoutingSupport.tokenSupport (ctx := ctx) (setup := setup) token ⊆
        Zstar stage token pair branch ∧
      (stage.demand pair.first).GammaVertices ⊆ Zstar stage token pair branch ∧
      (stage.demand pair.second).GammaVertices ⊆ Zstar stage token pair branch ∧
      SurplusPortActivation.PortSupport setup pair.first ⊆
        Zstar stage token pair branch ∧
      SurplusPortActivation.PortSupport setup pair.second ⊆
        Zstar stage token pair branch ∧
      branch.support stage ⊆ Zstar stage token pair branch := by
  have provenance := retainedCarrier_provenance stage token pair branch
  exact ⟨provenance.1.trans (retainedCarrier_subset_Zstar stage token pair branch),
    provenance.2.1.trans (retainedCarrier_subset_Zstar stage token pair branch),
    provenance.2.2.1.trans (retainedCarrier_subset_Zstar stage token pair branch),
    provenance.2.2.2.1.trans (retainedCarrier_subset_Zstar stage token pair branch),
    provenance.2.2.2.2.1.trans (retainedCarrier_subset_Zstar stage token pair branch),
    provenance.2.2.2.2.2.trans (retainedCarrier_subset_Zstar stage token pair branch)⟩

theorem carrier_treeWalk_support_subset_Zstar
    (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    (token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup))
    (branch : SurplusRoutingSupport.PairBranch stage pair)
    {endpoint : ctx.G.Vertex}
    (endpointMem : endpoint ∈ retainedCarrier stage token pair branch) :
    ∀ vertex ∈ ((bfsProfile token).treeWalk bfsPreconnected endpoint).support,
      vertex ∈ Zstar stage token pair branch := by
  classical
  intro vertex member
  simp only [Zstar, Finset.mem_union, Finset.mem_biUnion,
    List.mem_toFinset]
  exact Or.inr ⟨endpoint, endpointMem, member⟩

/-- Connectedness certificate for the closure: each closure vertex has a
literal root walk whose entire support remains in `Zstar`. -/
theorem Zstar_root_walk
    (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    (token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup))
    (branch : SurplusRoutingSupport.PairBranch stage pair)
    {vertex : ctx.G.Vertex} (member : vertex ∈ Zstar stage token pair branch) :
    ∃ walk : ctx.G.object.graph.Walk
        (SurplusRoutingSupport.tokenRoot (ctx := ctx) (setup := setup) token) vertex,
      ∀ point ∈ walk.support, point ∈ Zstar stage token pair branch := by
  classical
  let carrier := retainedCarrier stage token pair branch
  by_cases carrierMem : vertex ∈ carrier
  · exact ⟨(bfsProfile token).treeWalk bfsPreconnected vertex,
      carrier_treeWalk_support_subset_Zstar stage token pair branch carrierMem⟩
  · have unionMem : vertex ∈ carrier.biUnion fun endpoint =>
        ((bfsProfile token).treeWalk bfsPreconnected endpoint).support.toFinset := by
      simpa [Zstar, carrier, carrierMem] using member
    simp only [Finset.mem_biUnion] at unionMem
    obtain ⟨endpoint, endpointMem, vertexMem⟩ := unionMem
    have coherent := (bfsProfile token).support_eq_take_of_mem bfsPreconnected
      ((bfsProfile token).depth bfsPreconnected endpoint) endpoint vertex rfl
      (by simpa using vertexMem)
    refine ⟨(bfsProfile token).treeWalk bfsPreconnected vertex, ?_⟩
    intro point pointMem
    apply carrier_treeWalk_support_subset_Zstar stage token pair branch endpointMem
    have takenMem := Eq.mp
      (congrArg (fun values => point ∈ values) coherent) pointMem
    exact List.mem_of_mem_take takenMem

/-- First minimum-depth vertex of one endpoint port support, with declared
vertex order breaking ties.  The stage and branch parameters pin this
selection to the retained-carrier instance even though the target itself is
the literal port support. -/
noncomputable def endpointSelection
    (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    (token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup))
    (_branch : SurplusRoutingSupport.PairBranch stage pair)
    (first : Bool) :
    (bfsProfile token).TargetSelection bfsPreconnected
      (endpointSupport (setup := setup) pair first) :=
  (bfsProfile token).selectTarget bfsPreconnected
    (endpointSupport (setup := setup) pair first)
    (endpointSupport_nonempty (setup := setup) pair first)

noncomputable def selectedGerm
    (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    (token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup))
    (branch : SurplusRoutingSupport.PairBranch stage pair)
    (first : Bool) : ctx.G.object.graph.Walk
      (SurplusRoutingSupport.tokenRoot (ctx := ctx) (setup := setup) token)
      (endpointSelection stage token pair branch first).vertex :=
  (bfsProfile token).treeWalk bfsPreconnected
    (endpointSelection stage token pair branch first).vertex

theorem endpointSupport_subset_retainedCarrier
    (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    (token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup))
    (branch : SurplusRoutingSupport.PairBranch stage pair)
    (first : Bool) :
    endpointSupport (setup := setup) pair first ⊆
      retainedCarrier stage token pair branch := by
  cases first with
  | false =>
      exact (retainedCarrier_provenance stage token pair branch).2.2.2.2.1
  | true =>
      exact (retainedCarrier_provenance stage token pair branch).2.2.2.1

theorem selectedGerm_support_subset_Zstar
    (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    (token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup))
    (branch : SurplusRoutingSupport.PairBranch stage pair)
    (first : Bool) :
    ∀ vertex ∈ (selectedGerm stage token pair branch first).support,
      vertex ∈ Zstar stage token pair branch := by
  apply carrier_treeWalk_support_subset_Zstar stage token pair branch
  exact endpointSupport_subset_retainedCarrier stage token pair branch first
    (endpointSelection stage token pair branch first).vertex_mem

theorem selectedGerm_first_lands
    (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    (token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup))
    (branch : SurplusRoutingSupport.PairBranch stage pair)
    (first : Bool) :
    (endpointSelection stage token pair branch first).vertex ∈
        endpointSupport (setup := setup) pair first ∧
      ∀ index < (selectedGerm stage token pair branch first).length,
        (selectedGerm stage token pair branch first).getVert index ∉
          endpointSupport (setup := setup) pair first :=
  (endpointSelection stage token pair branch first).treeWalk_first_lands

theorem selectedGerm_shortest
    (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    (token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup))
    (branch : SurplusRoutingSupport.PairBranch stage pair)
    (first : Bool)
    {candidate : ctx.G.Vertex}
    (candidateMem : candidate ∈ endpointSupport (setup := setup) pair first)
    (walk : ctx.G.object.graph.Walk
      (SurplusRoutingSupport.tokenRoot (ctx := ctx) (setup := setup) token)
      candidate) :
    (selectedGerm stage token pair branch first).length ≤ walk.length :=
  OrderedBFSTree.Profile.TargetSelection.shortest_to_target
    (bfsProfile token) (endpointSelection stage token pair branch first)
    candidateMem walk

/-- Typed geometric comparison of the two selected endpoint germs. -/
noncomputable def classifySelectedGerms
    (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    (token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup))
    (branch : SurplusRoutingSupport.PairBranch stage pair) :
    (bfsProfile token).TreePathComparison bfsPreconnected
      (endpointSelection stage token pair branch true).vertex
      (endpointSelection stage token pair branch false).vertex :=
  (bfsProfile token).classifyTreePaths bfsPreconnected
    (endpointSelection stage token pair branch true).vertex
    (endpointSelection stage token pair branch false).vertex

/-! ## Token-root incidence after a divergent tree comparison -/

theorem tokenRoot_degree_ge_three
    (token : Token (ctx := ctx) (setup := setup)) :
    3 ≤ ctx.G.object.degree
      (SurplusRoutingSupport.tokenRoot (ctx := ctx) (setup := setup) token) := by
  rw [← setup.minimumDegree_eq_three]
  exact (SurplusPortActivation.Setup.baseline setup).trans
    (ctx.G.object.minDegree_le_degree _)

/-- Generic divergence data specialized to the actual token root. -/
abbrev RootDivergence
    (token : Token (ctx := ctx) (setup := setup)) :=
  RootIncidence.Divergence ctx.G.object
    (SurplusRoutingSupport.tokenRoot (ctx := ctx) (setup := setup) token)

abbrev ThirdRootIncidence
    (token : Token (ctx := ctx) (setup := setup))
    (divergence : RootDivergence token) :=
  RootIncidence.Third ctx.G.object
    (SurplusRoutingSupport.tokenRoot (ctx := ctx) (setup := setup) token)
    divergence

abbrev TokenRootIncidenceBranch
    (token : Token (ctx := ctx) (setup := setup))
    (divergence : RootDivergence token) :=
  RootIncidence.Branch ctx.G.object
    (SurplusRoutingSupport.tokenRoot (ctx := ctx) (setup := setup) token)
    divergence

noncomputable def classifyTokenRootIncidence
    (token : Token (ctx := ctx) (setup := setup))
    (divergence : RootDivergence token) :
    TokenRootIncidenceBranch token divergence :=
  RootIncidence.classify ctx.G.object
    (SurplusRoutingSupport.tokenRoot (ctx := ctx) (setup := setup) token)
    (tokenRoot_degree_ge_three (setup := setup) token) divergence

noncomputable def tokenRootIncidenceChecks
    (token : Token (ctx := ctx) (setup := setup)) : Nat :=
  RootIncidence.checks ctx.G.object
    (SurplusRoutingSupport.tokenRoot (ctx := ctx) (setup := setup) token)

theorem tokenRootIncidenceChecks_le_order
    (token : Token (ctx := ctx) (setup := setup)) :
    tokenRootIncidenceChecks token ≤ ctx.G.object.input.vertices.card :=
  RootIncidence.checks_le_order ctx.G.object
    (SurplusRoutingSupport.tokenRoot (ctx := ctx) (setup := setup) token)

/-- The complete incidence payload obtained from an actual root-divergence
comparison, with no semantic interpretation attached. -/
structure ClassifiedRootDivergence
    (token : Token (ctx := ctx) (setup := setup)) where
  divergence : RootDivergence token
  branch : TokenRootIncidenceBranch token divergence

/-- Routine adapter from the `divergeAtRoot` constructor of the two selected
germs.  All other geometric outcomes deliberately return `none`. -/
noncomputable def classifySelectedRootIncidence?
    (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    (token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup))
    (branch : SurplusRoutingSupport.PairBranch stage pair) :
    Option (ClassifiedRootDivergence token) :=
  match classifySelectedGerms stage token pair branch with
  | .divergeAtRoot leftNext rightNext _leftTail _rightTail
      _leftEq _rightEq distinct leftAdjacent rightAdjacent _disjoint =>
      let divergence : RootDivergence token := {
        leftNext := leftNext
        rightNext := rightNext
        leftAdjacent := leftAdjacent
        rightAdjacent := rightAdjacent
        distinct := distinct
      }
      some ⟨divergence, classifyTokenRootIncidence token divergence⟩
  | _ => none

/-- Executable tag recording exactly when the selected-germ comparison has
the root-divergence shape consumed by the adapter. -/
noncomputable def selectedGermsDivergeAtRoot
    (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    (token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup))
    (branch : SurplusRoutingSupport.PairBranch stage pair) : Bool :=
  match classifySelectedGerms stage token pair branch with
  | .divergeAtRoot .. => true
  | _ => false

theorem classifySelectedRootIncidence?_isSome
    (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    (token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup))
    (branch : SurplusRoutingSupport.PairBranch stage pair) :
    (classifySelectedRootIncidence? stage token pair branch).isSome =
      selectedGermsDivergeAtRoot stage token pair branch := by
  unfold classifySelectedRootIncidence? selectedGermsDivergeAtRoot
  cases comparison : classifySelectedGerms stage token pair branch <;> rfl

/-- Complete proof-carrying incidence payload at the separator of an actual
after-edge divergence. -/
structure ClassifiedAfterEdgeIncidence
    (token : Token (ctx := ctx) (setup := setup)) where
  separator : ctx.G.Vertex
  incidence : RootIncidence.AfterEdge ctx.G.object separator
  degreeBranch : RootIncidence.AfterEdgeBranch ctx.G.object separator incidence

/-- Adapter from the exact `divergeAfterEdge` result.  Pairwise distinctness
of predecessor and residual next vertices is recovered from the noduplicated
canonical tree paths; no semantic conclusion is added. -/
noncomputable def classifySelectedAfterEdgeIncidence?
    (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    (token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup))
    (branch : SurplusRoutingSupport.PairBranch stage pair) :
    Option (ClassifiedAfterEdgeIncidence token) :=
  match classifySelectedGerms stage token pair branch with
  | .divergeAfterEdge stem predecessor separator leftNext rightNext
      leftTail rightTail leftEq rightEq predecessorAdjacent leftAdjacent
      rightAdjacent distinct _residualDisjoint => by
      have predecessorNeLeft : predecessor ≠ leftNext := by
        have nodup := ((bfsProfile token).treeWalk_isPath bfsPreconnected
          (endpointSelection stage token pair branch true).vertex).support_nodup
        rw [leftEq] at nodup
        have separated : List.Disjoint
            (stem ++ [predecessor, separator]) (leftNext :: leftTail) :=
          nodup.disjoint
        intro equal
        have predecessorRest : predecessor ∈ leftNext :: leftTail := by
          simp [equal]
        exact (List.disjoint_left.mp separated) (by simp) predecessorRest
      have predecessorNeRight : predecessor ≠ rightNext := by
        have nodup := ((bfsProfile token).treeWalk_isPath bfsPreconnected
          (endpointSelection stage token pair branch false).vertex).support_nodup
        rw [rightEq] at nodup
        have separated : List.Disjoint
            (stem ++ [predecessor, separator]) (rightNext :: rightTail) :=
          nodup.disjoint
        intro equal
        have predecessorRest : predecessor ∈ rightNext :: rightTail := by
          simp [equal]
        exact (List.disjoint_left.mp separated) (by simp) predecessorRest
      let incidence : RootIncidence.AfterEdge ctx.G.object separator := {
        predecessor := predecessor
        leftNext := leftNext
        rightNext := rightNext
        predecessorAdjacent := predecessorAdjacent.symm
        leftAdjacent := leftAdjacent
        rightAdjacent := rightAdjacent
        predecessor_ne_left := predecessorNeLeft
        predecessor_ne_right := predecessorNeRight
        left_ne_right := distinct
      }
      have degreeGe : 3 ≤ ctx.G.object.degree separator := by
        rw [← setup.minimumDegree_eq_three]
        exact (SurplusPortActivation.Setup.baseline setup).trans
          (ctx.G.object.minDegree_le_degree separator)
      exact some ⟨separator, incidence,
        RootIncidence.classifyAfterEdge ctx.G.object separator degreeGe incidence⟩
  | _ => none

noncomputable def selectedGermsDivergeAfterEdge
    (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    (token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup))
    (branch : SurplusRoutingSupport.PairBranch stage pair) : Bool :=
  match classifySelectedGerms stage token pair branch with
  | .divergeAfterEdge .. => true
  | _ => false

theorem classifySelectedAfterEdgeIncidence?_isSome
    (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    (token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup))
    (branch : SurplusRoutingSupport.PairBranch stage pair) :
    (classifySelectedAfterEdgeIncidence? stage token pair branch).isSome =
      selectedGermsDivergeAfterEdge stage token pair branch := by
  unfold classifySelectedAfterEdgeIncidence? selectedGermsDivergeAfterEdge
  cases comparison : classifySelectedGerms stage token pair branch <;> rfl

/-- Static polynomial work envelope for the shared BFS, carrier path closure,
and two endpoint selections.  This is not an instrumented runtime count. -/
noncomputable def zstarBudget
    (token : Token (ctx := ctx) (setup := setup)) : Nat :=
  let order := ctx.G.object.input.vertices.card
  (bfsProfile token).budget order + order * (order + 1) +
    2 * ((order + 1) * (order + 1))

theorem zstarBudget_polynomial
    (token : Token (ctx := ctx) (setup := setup)) :
    zstarBudget token ≤
      1 + ctx.G.object.input.vertices.card *
          (ctx.G.object.input.vertices.card *
            (ctx.G.object.input.vertices.card + 1)) +
        ctx.G.object.input.vertices.card *
          (ctx.G.object.input.vertices.card + 1) +
        2 * ((ctx.G.object.input.vertices.card + 1) *
          (ctx.G.object.input.vertices.card + 1)) := by
  unfold zstarBudget
  exact Nat.add_le_add_right
    (Nat.add_le_add_right
      ((bfsProfile token).budget_polynomial
        ctx.G.object.input.vertices.card)
      (ctx.G.object.input.vertices.card *
        (ctx.G.object.input.vertices.card + 1)))
    (2 * ((ctx.G.object.input.vertices.card + 1) *
      (ctx.G.object.input.vertices.card + 1)))

/-- One proof-carrying shortest germ from the actual token root to one of the
two literal three-vertex port supports of a scheduled pair. -/
noncomputable def germ (token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup)) (first : Bool) :
    FiniteConnector.Certificate ctx.G.object
      {SurplusRoutingSupport.tokenRoot (ctx := ctx) (setup := setup) token}
      (endpointSupport (setup := setup) pair first) :=
  FiniteConnector.canonical ctx.G.object
    (input.preconnected_of_noProperCore ctx)
    (by simp)
    (endpointSupport_nonempty (setup := setup) pair first)

theorem germ_start (token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup)) (first : Bool) :
    (germ token pair first).start =
      SurplusRoutingSupport.tokenRoot (ctx := ctx) (setup := setup) token := by
  simpa using (germ token pair first).start_mem

/-- The observable finite vertex word of the retained germ. -/
noncomputable def word (token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup)) (first : Bool) : List ctx.G.Vertex :=
  (germ token pair first).path.support

/-- Compare two actual germs after their common literal token root.  The
returned separator is the last common vertex before the first unequal next
vertices; exhaustion of either word is the parallel case. -/
noncomputable def compare
    (token : Token (ctx := ctx) (setup := setup))
    (left : Pair (setup := setup)) (leftFirst : Bool)
    (right : Pair (setup := setup)) (rightFirst : Bool) :
    Core.RootedPathRelation.Comparison ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact Core.RootedPathRelation.compare
    (SurplusRoutingSupport.tokenRoot (ctx := ctx) (setup := setup) token)
    (word token left leftFirst).tail
    (word token right rightFirst).tail

/-- Exhaustive geometric refinement on the exact selected graph. -/
noncomputable def route
    (token : Token (ctx := ctx) (setup := setup))
    (left : Pair (setup := setup)) (leftFirst : Bool)
    (right : Pair (setup := setup)) (rightFirst : Bool) :
    Core.RootedPathRelation.Routed ctx.G.object.degree := by
  exact Core.RootedPathRelation.route ctx.G.object.degree
    (fun vertex => by
      rw [← setup.minimumDegree_eq_three]
      exact (SurplusPortActivation.Setup.baseline setup).trans
        (ctx.G.object.minDegree_le_degree vertex))
    (compare token left leftFirst right rightFirst)

noncomputable def checks
    (token : Token (ctx := ctx) (setup := setup))
    (left : Pair (setup := setup)) (leftFirst : Bool)
    (right : Pair (setup := setup)) (rightFirst : Bool) : Nat := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact Core.RootedPathRelation.checks
    (word token left leftFirst).tail
    (word token right rightFirst).tail

theorem checks_le_left
    (token : Token (ctx := ctx) (setup := setup))
    (left : Pair (setup := setup)) (leftFirst : Bool)
    (right : Pair (setup := setup)) (rightFirst : Bool) :
    checks token left leftFirst right rightFirst ≤
      (word token left leftFirst).tail.length :=
  by
    letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
    exact Core.RootedPathRelation.checks_le_left_length _ _

end StructuralExhaustion.Graph.SurplusRoutingGerm
