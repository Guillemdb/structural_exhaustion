import Erdos64EG.P13WeightedColdRestrictedF1Completion
import Erdos64EG.P13WeightedColdRestrictedBoundedInterface
import Erdos64EG.CT2BridgeContraction
import Erdos64EG.P13FixedColdCutState
import StructuralExhaustion.Graph.FiniteSupportRawCurvature
import StructuralExhaustion.Graph.WalkTypeAD5Projection
import StructuralExhaustion.Graph.TypeAFullD5Signature
import StructuralExhaustion.Core.FiniteRoleSupportNormalization

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

namespace P13WeightedColdRestrictedPrefixPackage

noncomputable section

variable (package : P13WeightedColdRestrictedPrefixPackage ctx node21)

noncomputable abbrev ambientPrefix (stage : package.Stage) :=
  InducedPathRestrictedPrefixCompletion.ambientPrefix package.input stage

noncomputable abbrev activeSupport (stage : package.Stage) : Finset ctx.G.Vertex :=
  WalkTypeASupportProfile.support ctx.G.object (package.ambientPrefix stage)

abbrev D4Role := Core.FixedTwoBoundaryCutState.BoundaryRole

@[implicit_reducible]
noncomputable def d4Roles : FinEnum D4Role := inferInstance

noncomputable def d4BoundaryWindow (role : D4Role) :
    InducedPathWindowLedger.WindowIndex ctx.G.object :=
  if role = 0 then package.input.anchor.window
  else (InducedPathRestrictedComponentBoundarySchedule.successor package.input).window

noncomputable def d4Label (stage : package.Stage) (role : D4Role)
    (vertex : ctx.G.Vertex) : InducedPathAttachment.Label 13 :=
  InducedPathAttachment.finiteObjectAttachmentLabel ctx.G.object
    (InducedPathWindowLedger.selectedWindow ctx.G.object
      (d4BoundaryWindow package role)) vertex

abbrev D4Coordinate (stage : package.Stage) :=
  FiniteSupportRawCurvature.Coordinate (Role := D4Role) ctx.G.object
    (package.boundedActiveInterface stage)

@[implicit_reducible]
noncomputable def d4Coordinates (stage : package.Stage) :
    FinEnum (package.D4Coordinate stage) :=
  FiniteSupportRawCurvature.coordinates ctx.G.object d4Roles
    (package.boundedActiveInterface stage)

/-- Literal D4 value at one stored cold-prefix stage. -/
noncomputable def d4Response (stage : package.Stage)
    (coordinate : package.D4Coordinate stage) : Bool :=
  FiniteSupportRawCurvature.response ctx.G.object
    (package.boundedActiveInterface stage)
    PowerOfTwoLength powerOfTwoLengthDecidable (package.d4Label stage) coordinate

theorem d4Response_true_iff (stage : package.Stage)
    (coordinate : package.D4Coordinate stage) :
    package.d4Response stage coordinate = true ↔
      InducedPathAttachment.omegaTwo 13 PowerOfTwoLength powerOfTwoLengthDecidable
        (package.d4Label stage coordinate.1 coordinate.2.left)
        (package.d4Label stage coordinate.1 coordinate.2.center)
        (package.d4Label stage coordinate.1 coordinate.2.right) = 1 :=
  FiniteSupportRawCurvature.response_true_iff ctx.G.object
    (package.boundedActiveInterface stage) PowerOfTwoLength
      powerOfTwoLengthDecidable
      (package.d4Label stage) coordinate

theorem every_supported_d4_coordinate_is_stored (stage : package.Stage)
    (coordinate : package.D4Coordinate stage) :
    coordinate ∈ (package.d4Coordinates stage).orderedValues :=
  FiniteSupportRawCurvature.coordinate_mem ctx.G.object d4Roles
    (package.boundedActiveInterface stage) coordinate

theorem d4Checks_cubic (stage : package.Stage) :
    FiniteSupportRawCurvature.visibleChecks
        d4Roles (package.boundedActiveInterface stage) ≤
      4 * ctx.G.object.input.vertices.card ^ 3 := by
  have rolesCard : d4Roles.card = 2 := by rfl
  simpa [rolesCard] using
    (FiniteSupportRawCurvature.visibleChecks_le_cubic ctx.G.object
      d4Roles (package.boundedActiveInterface stage))

/-- The node-[153] D4 scan is genuinely local: the two-window,
two-endpoint carrier has at most thirty vertices, so the complete two-role
wedge scan has a graph-size-independent bound. -/
theorem d4Checks_le_108000 (stage : package.Stage) :
    FiniteSupportRawCurvature.visibleChecks
        d4Roles (package.boundedActiveInterface stage) ≤ 108000 := by
  have rolesCard : d4Roles.card = 2 := by rfl
  rw [FiniteSupportRawCurvature.visibleChecks, rolesCard]
  have carrierBound := package.boundedActiveInterface_card_le_30 stage
  calc
    (2 + 2) * (package.boundedActiveInterface stage).card ^ 3
        ≤ 4 * 30 ^ 3 :=
      Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left carrierBound 3)
    _ = 108000 := by decide

/-! ## Fixed structural-role normalization for D4 -/

/-- A D4 wedge is named only by its boundary role and the three fixed carrier
roles of its left endpoint, center, and right endpoint.  The graph predicate
remains in the source coordinate; this alphabet contains no ambient vertex. -/
abbrev D4FixedCoordinate :=
  D4Role × (BoundedCarrierRole × BoundedCarrierRole × BoundedCarrierRole)

noncomputable def d4FixedCoordinate (stage : package.Stage)
    (coordinate : package.D4Coordinate stage) : D4FixedCoordinate :=
  (coordinate.1,
    ((package.boundedCarrierCode stage coordinate.2.left
      coordinate.2.left_mem).role,
    (package.boundedCarrierCode stage coordinate.2.center
      coordinate.2.center_mem).role,
    (package.boundedCarrierCode stage coordinate.2.right
      coordinate.2.right_mem).role))

theorem d4FixedCoordinate_injective (stage : package.Stage) :
    Function.Injective (package.d4FixedCoordinate stage) := by
  intro left right equal
  have roleEqual : left.1 = right.1 :=
    congrArg (fun code : D4FixedCoordinate => code.1) equal
  have leftCodeEqual :
      (package.boundedCarrierCode stage left.2.left left.2.left_mem).role =
        (package.boundedCarrierCode stage right.2.left right.2.left_mem).role :=
    congrArg (fun code => code.2.1) equal
  have centerCodeEqual :
      (package.boundedCarrierCode stage left.2.center left.2.center_mem).role =
        (package.boundedCarrierCode stage right.2.center right.2.center_mem).role :=
    congrArg (fun code => code.2.2.1) equal
  have rightCodeEqual :
      (package.boundedCarrierCode stage left.2.right left.2.right_mem).role =
        (package.boundedCarrierCode stage right.2.right right.2.right_mem).role :=
    congrArg (fun code => code.2.2.2) equal
  have leftVertexEqual : left.2.left = right.2.left :=
    package.boundedCarrierCode_injective stage left.2.left_mem right.2.left_mem
      leftCodeEqual
  have centerVertexEqual : left.2.center = right.2.center :=
    package.boundedCarrierCode_injective stage left.2.center_mem right.2.center_mem
      centerCodeEqual
  have rightVertexEqual : left.2.right = right.2.right :=
    package.boundedCarrierCode_injective stage left.2.right_mem right.2.right_mem
      rightCodeEqual
  apply Prod.ext roleEqual
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact centerVertexEqual
  · apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact leftVertexEqual
    · apply Subtype.ext
      exact rightVertexEqual

theorem d4FixedCoordinate_card :
    Fintype.card D4FixedCoordinate = 43904 := by
  change Fintype.card (D4Role ×
    ((Fin 13 ⊕ (Fin 13 ⊕ Bool)) ×
      (Fin 13 ⊕ (Fin 13 ⊕ Bool)) ×
      (Fin 13 ⊕ (Fin 13 ⊕ Bool)))) = 43904
  simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_bool]

theorem minimumDegreeThree : 3 ≤ ctx.G.object.minDegree :=
  (packedStaticInput.fixedContext ctx).baseline

noncomputable def d5DegreeSplit (stage : package.Stage) :=
  WalkTypeAD5Projection.degreeSplit (package.ambientPrefix stage)
    (minimumDegreeThree (ctx := ctx))

/-- The deleted anchor-window vertex proves that every literal prefix support
is proper.  This is the missing same-support input needed by minimality's
internal-three-core theorem. -/
theorem anchorWindowOutsidePrefix (stage : package.Stage) :
    InducedPathWindowLedger.selectedWindow ctx.G.object package.input.anchor.window
        package.input.anchor.offset ∉ package.activeSupport stage := by
  intro member
  exact InducedPathRestrictedPrefixCompletion.ambientPrefix_outside_anchor_window
    package.input stage
      (InducedPathWindowLedger.selectedWindow ctx.G.object
        package.input.anchor.window package.input.anchor.offset)
      (by simpa [activeSupport, WalkTypeASupportProfile.support] using member)
      package.input.anchor.offset rfl

noncomputable def D5Profile (stage : package.Stage)
    (noHigh : WalkTypeAD5Projection.NoHigh (package.ambientPrefix stage)
      (minimumDegreeThree (ctx := ctx))) :=
  WalkTypeAD5Projection.typeAProfile (package.ambientPrefix stage)
    (minimumDegreeThree (ctx := ctx)) rfl
    (InducedPathWindowLedger.selectedWindow ctx.G.object package.input.anchor.window
      package.input.anchor.offset)
    (package.anchorWindowOutsidePrefix stage) noHigh

noncomputable def d5ReturnProducer (stage : package.Stage)
    (noHigh : WalkTypeAD5Projection.NoHigh (package.ambientPrefix stage)
      (minimumDegreeThree (ctx := ctx))) :
    WalkTypeAD5Projection.Profile.ReturnProducer (package.D5Profile stage noHigh) where
  notBridge := fun port => minimality_dart_not_bridge ctx
    (TypeAAnchoredReturnCoordinate.dart ctx.G.object
      (package.D5Profile stage noHigh) port)

structure D5Available (stage : package.Stage) where
  noHigh : WalkTypeAD5Projection.NoHigh (package.ambientPrefix stage)
    (minimumDegreeThree (ctx := ctx))
  profile : TypeACanonicalReceiverTrace.SupportProfile ctx.G.object
  profileExact : profile = package.D5Profile stage noHigh
  coordinates : FinEnum (WalkTypeAD5Projection.Profile.Coordinate profile)
  coordinatesExact : coordinates = WalkTypeAD5Projection.Profile.coordinates profile
  returnProducer : WalkTypeAD5Projection.Profile.ReturnProducer profile
  returnProducerExact : returnProducer = by
    rw [profileExact]
    exact package.d5ReturnProducer stage noHigh

namespace D5Available

variable {package}
variable {stage : package.Stage}
variable (available : package.D5Available stage)

theorem profileSupportExact :
    available.profile.support = package.activeSupport stage := by
  rw [available.profileExact]
  rfl

/-! The complete paper D5 base signature on the literal bounded interface. -/

abbrev FullBaseCoordinate :=
  TypeAFullD5Signature.LocalBaseCoordinate ctx.G.object available.profile
    available.returnProducer (package.boundedActiveInterface stage)

@[implicit_reducible]
noncomputable def fullBaseCoordinates : FinEnum available.FullBaseCoordinate :=
  TypeAFullD5Signature.localBaseCoordinatesFromCarrier ctx.G.object available.profile
    available.returnProducer (package.boundedActiveInterface stage)
    (package.boundedCarrierVertices stage)

noncomputable def fullBaseValue (coordinate : available.FullBaseCoordinate) :=
  TypeAFullD5Signature.value ctx.G.object available.profile
    available.returnProducer coordinate.1

/-- Total carrier-role encoder used by D5 normalization.  Its fallback is
never observed by a locally supported coordinate; it only makes the function
total without scanning the ambient vertex enumeration. -/
noncomputable def fullBaseRole (vertex : ctx.G.Vertex) : BoundedCarrierRole := by
  classical
  by_cases member : vertex ∈ package.boundedActiveInterface stage
  · exact (package.boundedCarrierCode stage vertex member).role
  · exact .inr (.inr false)

theorem boundedCarrierRoleVertex_fullBaseRole
    (vertex : ctx.G.Vertex)
    (member : vertex ∈ package.boundedActiveInterface stage) :
    package.boundedCarrierRoleVertex stage
      (fullBaseRole (package := package) (stage := stage) vertex) = vertex := by
  classical
  simp only [fullBaseRole, dif_pos member]
  exact (package.boundedCarrierCode stage vertex member).exact

/-- Exact role-normalized value of every currently available D5 coordinate.
All ambient vertices in the payload have been replaced by one of the 28
semantic carrier roles. -/
noncomputable def fullBaseRoleValue (coordinate : available.FullBaseCoordinate) :
    TypeAFullD5Signature.RoleValue BoundedCarrierRole :=
  TypeAFullD5Signature.roleValue ctx.G.object available.profile
    (fullBaseRole (package := package) (stage := stage)) available.returnProducer
    (package.boundedActiveInterface stage) coordinate

/-- Equality of locally normalized values is equivalent to equality of the
paper's complete labelled base observation. -/
theorem fullBaseRoleValue_eq_iff (left right : available.FullBaseCoordinate) :
    available.fullBaseRoleValue left = available.fullBaseRoleValue right ↔
      available.fullBaseValue left = available.fullBaseValue right :=
  TypeAFullD5Signature.roleValue_eq_iff ctx.G.object available.profile
    (fullBaseRole (package := package) (stage := stage))
    (package.boundedCarrierRoleVertex stage)
    available.returnProducer (package.boundedActiveInterface stage)
    (fun vertex member =>
      boundedCarrierRoleVertex_fullBaseRole
        (package := package) (stage := stage) vertex member)
    left right

/-! The fixed finite alphabet used by the cold count.  Ordered path payloads
are bounded lists of at most thirty carrier roles, and every numerical field
is stored in `Fin 31`. -/

/-- A symbolic bounded vector.  Unlike a bounded-list `FinEnum`, this does not
materialize the astronomical list alphabet: its cardinal is represented by
the dependent finite function type itself. -/
abbrev FixedD5RoleList :=
  Sigma fun length : Fin 31 => Fin length.1 → BoundedCarrierRole

/-- Seven tagged, genuinely finite value families. -/
abbrev FixedD5RoleValue :=
  FixedD5RoleList ⊕
  (BoundedCarrierRole × Fin 31 × Bool) ⊕
  (BoundedCarrierRole × BoundedCarrierRole) ⊕
  FixedD5RoleList ⊕
  (BoundedCarrierRole × BoundedCarrierRole) ⊕
  FixedD5RoleList ⊕
  Fin 31

noncomputable instance : Fintype FixedD5RoleList := by
  letI : (length : Fin 31) →
      Fintype (Fin length.1 → BoundedCarrierRole) := fun _ => inferInstance
  infer_instance

noncomputable instance : DecidableEq FixedD5RoleList := Classical.decEq _
noncomputable instance : Fintype FixedD5RoleValue := by
  infer_instance
noncomputable instance : DecidableEq FixedD5RoleValue := Classical.decEq _

/-- Fixed local labels of the seven base coordinate families.  Trace
positions use `Fin 31`; no ambient vertex or unbounded natural remains. -/
inductive FixedD5RoleLabel
  | canonicalTrace (source : BoundedCarrierRole)
  | traceIncidence (source : BoundedCarrierRole) (position : Fin 31)
  | completionPort (receiver outside : BoundedCarrierRole)
  | canonicalReturn (receiver outside : BoundedCarrierRole)
  | firstEntryReceiver (receiver outside : BoundedCarrierRole)
  | connectorPath (receiver outside : BoundedCarrierRole)
  | connectorLength (receiver outside : BoundedCarrierRole)
  deriving DecidableEq, Fintype

/-- A complete fixed D5 code: clause kind, exact coordinate label, complete
declared-support mask on the 28 semantic roles, and exact bounded value.  The
representation is the reusable framework-owned normalization code. -/
abbrev FixedD5Code :=
  Core.FiniteRoleSupportNormalization.Profile.Code
    BoundedCarrierRole TypeAFullD5Signature.BaseKind
      FixedD5RoleLabel FixedD5RoleValue

/-- The symbolic fixed alphabet size.  `Fintype.card` is used only as a
theorem-level numeral; the production runner never enumerates this type. -/
noncomputable def FixedD5AlphabetSize : Nat := Fintype.card FixedD5Code

/-- Canonical injection into the corresponding finite ordinal.  This is an
equivalence supplied by finiteness, not a materialized alphabet schedule. -/
noncomputable def fixedD5CodeToFin : FixedD5Code ≃ Fin FixedD5AlphabetSize :=
  Fintype.equivFin FixedD5Code

theorem fixedD5CodeToFin_injective : Function.Injective fixedD5CodeToFin :=
  fixedD5CodeToFin.injective

/-- Symbolic cardinality of the fixed alphabet.  In particular the support
factor is exactly `2^28`; neither this theorem nor the runner enumerates those
masks. -/
theorem fixedD5Code_card :
    Fintype.card FixedD5Code =
      7 * Fintype.card FixedD5RoleLabel *
        2 ^ 28 * Fintype.card FixedD5RoleValue := by
  have kindCard : Fintype.card TypeAFullD5Signature.BaseKind = 7 := by
    native_decide
  have roleCard : Fintype.card BoundedCarrierRole = 28 := by
    change Fintype.card (Fin 13 ⊕ (Fin 13 ⊕ Bool)) = 28
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool]
  rw [Core.FiniteRoleSupportNormalization.Profile.code_card]
  rw [kindCard, roleCard]

private theorem supportedNodupList_length_le_30
    (values : List ctx.G.Vertex) (nodup : values.Nodup)
    (supported : ∀ vertex ∈ values,
      vertex ∈ package.boundedActiveInterface stage) :
    values.length ≤ 30 := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  calc
    values.length = values.toFinset.card :=
      (List.toFinset_card_of_nodup nodup).symm
    _ ≤ (package.boundedActiveInterface stage).card :=
      Finset.card_le_card (by
        intro vertex member
        exact supported vertex (by simpa using member))
    _ ≤ 30 := package.boundedActiveInterface_card_le_30 stage

private theorem roleList_length_le_30
    (values : List ctx.G.Vertex) (nodup : values.Nodup)
    (supported : ∀ vertex ∈ values,
      vertex ∈ package.boundedActiveInterface stage) :
    (values.map (fullBaseRole (package := package) (stage := stage))).length ≤ 30 := by
  simpa using supportedNodupList_length_le_30
    (package := package) (stage := stage) values nodup supported

noncomputable def fixedD5RoleList (values : List ctx.G.Vertex)
    (bound : (values.map
      (fullBaseRole (package := package) (stage := stage))).length ≤ 30) :
    FixedD5RoleList := by
  let roles := values.map (fullBaseRole (package := package) (stage := stage))
  exact ⟨⟨roles.length, by simpa [roles] using Nat.lt_succ_iff.mpr bound⟩,
    fun index => roles.get ⟨index.1, by simpa using index.2⟩⟩

private theorem traceIncidence_position_lt_31
    (incidence : TypeAFullD5Signature.TraceIncidence ctx.G.object available.profile)
    (supported : TypeAFullD5Signature.declaredSupport ctx.G.object available.profile
      available.returnProducer
        (TypeAFullD5Signature.BaseCoordinate.traceIncidence
          ctx.G.object available.profile incidence) ⊆
      package.boundedActiveInterface stage) :
    incidence.position ctx.G.object available.profile < 31 := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  have supportCard : (incidence.support ctx.G.object available.profile).card ≤ 30 :=
    (Finset.card_le_card supported).trans
      (package.boundedActiveInterface_card_le_30 stage)
  have exactCard := incidence.support_card_eq_length_add_one
    ctx.G.object available.profile
  have positionBound := incidence.position_le_length ctx.G.object available.profile
  omega

noncomputable def fullBaseFixedLabel
    (coordinate : available.FullBaseCoordinate) : FixedD5RoleLabel := by
  let role := fullBaseRole (package := package) (stage := stage)
  rcases coordinate with ⟨coordinate, supported⟩
  rcases coordinate with cubic | (incidence | (port | (returned | (entry | (path | length)))))
  · exact .canonicalTrace (role cubic.1.1)
  · exact .traceIncidence
      (role (incidence.source ctx.G.object available.profile).1.1)
      ⟨incidence.position ctx.G.object available.profile,
        traceIncidence_position_lt_31 (package := package) (stage := stage)
          (available := available) incidence supported⟩
  · exact .completionPort
      (role (port.receiver ctx.G.object available.profile).1)
      (role (port.outside ctx.G.object available.profile))
  · exact .canonicalReturn
      (role (returned.receiver ctx.G.object available.profile).1)
      (role (returned.outside ctx.G.object available.profile))
  · exact .firstEntryReceiver
      (role (entry.receiver ctx.G.object available.profile).1)
      (role (entry.outside ctx.G.object available.profile))
  · exact .connectorPath
      (role (path.receiver ctx.G.object available.profile).1)
      (role (path.outside ctx.G.object available.profile))
  · exact .connectorLength
      (role (length.receiver ctx.G.object available.profile).1)
      (role (length.outside ctx.G.object available.profile))

noncomputable def FixedD5RoleLabel.decode (label : FixedD5RoleLabel) :
    TypeAFullD5Signature.BaseLabel (V := ctx.G.Vertex) :=
  let vertex := package.boundedCarrierRoleVertex stage
  match label with
  | .canonicalTrace source => .canonicalTrace (vertex source)
  | .traceIncidence source position => .traceIncidence (vertex source) position.1
  | .completionPort receiver outside => .completionPort (vertex receiver) (vertex outside)
  | .canonicalReturn receiver outside => .canonicalReturn (vertex receiver) (vertex outside)
  | .firstEntryReceiver receiver outside =>
      .firstEntryReceiver (vertex receiver) (vertex outside)
  | .connectorPath receiver outside => .connectorPath (vertex receiver) (vertex outside)
  | .connectorLength receiver outside => .connectorLength (vertex receiver) (vertex outside)

theorem fullBaseFixedLabel_decode_exact
    (coordinate : available.FullBaseCoordinate) :
    FixedD5RoleLabel.decode (package := package) (stage := stage)
        (available.fullBaseFixedLabel coordinate) =
      TypeAFullD5Signature.BaseCoordinate.label ctx.G.object available.profile
        coordinate.1 := by
  classical
  rcases coordinate with ⟨coordinate, supported⟩
  rcases coordinate with cubic | (incidence | (port | (returned | (entry | (path | length)))))
  · have sourceMember : cubic.1.1 ∈ package.boundedActiveInterface stage := by
      apply supported
      exact TypeAFullD5Signature.canonicalTrace_mem_declaredSupport
        ctx.G.object available.profile available.returnProducer cubic
          (by
            apply List.mem_map.mpr
            exact ⟨cubic.1,
              (available.profile.trace ctx.G.object cubic).start_mem_support, rfl⟩)
    simp only [fullBaseFixedLabel, FixedD5RoleLabel.decode,
      TypeAFullD5Signature.BaseCoordinate.label]
    rw [boundedCarrierRoleVertex_fullBaseRole
      (package := package) (stage := stage) cubic.1.1 sourceMember]
  · have sourceMember :
        (incidence.source ctx.G.object available.profile).1.1 ∈
          package.boundedActiveInterface stage := by
      apply supported
      exact incidence.source_mem_support ctx.G.object available.profile
    simp only [fullBaseFixedLabel, FixedD5RoleLabel.decode,
      TypeAFullD5Signature.BaseCoordinate.label]
    rw [boundedCarrierRoleVertex_fullBaseRole
      (package := package) (stage := stage)
      (incidence.source ctx.G.object available.profile).1.1 sourceMember]
  · obtain ⟨receiverMember, outsideMember⟩ :=
      TypeAFullD5Signature.port_endpoints_mem_declaredSupport
        ctx.G.object available.profile available.returnProducer
        (package.boundedActiveInterface stage) port
        (TypeAFullD5Signature.BaseCoordinate.completionPort
          ctx.G.object available.profile port) (Or.inl rfl) supported
    simp only [fullBaseFixedLabel, FixedD5RoleLabel.decode,
      TypeAFullD5Signature.BaseCoordinate.label]
    rw [boundedCarrierRoleVertex_fullBaseRole
        (package := package) (stage := stage) _ receiverMember,
      boundedCarrierRoleVertex_fullBaseRole
        (package := package) (stage := stage) _ outsideMember]
  · obtain ⟨receiverMember, outsideMember⟩ :=
      TypeAFullD5Signature.port_endpoints_mem_declaredSupport
        ctx.G.object available.profile available.returnProducer
        (package.boundedActiveInterface stage) returned
        (TypeAFullD5Signature.BaseCoordinate.canonicalReturn
          ctx.G.object available.profile returned) (Or.inr (Or.inl rfl)) supported
    simp only [fullBaseFixedLabel, FixedD5RoleLabel.decode,
      TypeAFullD5Signature.BaseCoordinate.label]
    rw [boundedCarrierRoleVertex_fullBaseRole
        (package := package) (stage := stage) _ receiverMember,
      boundedCarrierRoleVertex_fullBaseRole
        (package := package) (stage := stage) _ outsideMember]
  · obtain ⟨receiverMember, outsideMember⟩ :=
      TypeAFullD5Signature.port_endpoints_mem_declaredSupport
        ctx.G.object available.profile available.returnProducer
        (package.boundedActiveInterface stage) entry
        (TypeAFullD5Signature.BaseCoordinate.firstEntryReceiver
          ctx.G.object available.profile entry)
        (Or.inr (Or.inr (Or.inl rfl))) supported
    simp only [fullBaseFixedLabel, FixedD5RoleLabel.decode,
      TypeAFullD5Signature.BaseCoordinate.label]
    rw [boundedCarrierRoleVertex_fullBaseRole
        (package := package) (stage := stage) _ receiverMember,
      boundedCarrierRoleVertex_fullBaseRole
        (package := package) (stage := stage) _ outsideMember]
  · obtain ⟨receiverMember, outsideMember⟩ :=
      TypeAFullD5Signature.port_endpoints_mem_declaredSupport
        ctx.G.object available.profile available.returnProducer
        (package.boundedActiveInterface stage) path
        (TypeAFullD5Signature.BaseCoordinate.connectorPath
          ctx.G.object available.profile path)
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) supported
    simp only [fullBaseFixedLabel, FixedD5RoleLabel.decode,
      TypeAFullD5Signature.BaseCoordinate.label]
    rw [boundedCarrierRoleVertex_fullBaseRole
        (package := package) (stage := stage) _ receiverMember,
      boundedCarrierRoleVertex_fullBaseRole
        (package := package) (stage := stage) _ outsideMember]
  · obtain ⟨receiverMember, outsideMember⟩ :=
      TypeAFullD5Signature.port_endpoints_mem_declaredSupport
        ctx.G.object available.profile available.returnProducer
        (package.boundedActiveInterface stage) length
        (TypeAFullD5Signature.BaseCoordinate.connectorLength
          ctx.G.object available.profile length)
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) supported
    simp only [fullBaseFixedLabel, FixedD5RoleLabel.decode,
      TypeAFullD5Signature.BaseCoordinate.label]
    rw [boundedCarrierRoleVertex_fullBaseRole
        (package := package) (stage := stage) _ receiverMember,
      boundedCarrierRoleVertex_fullBaseRole
        (package := package) (stage := stage) _ outsideMember]

noncomputable def fullBaseSupportMask
    (coordinate : available.FullBaseCoordinate) : BoundedCarrierRole → Bool := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact fun role => decide
    (package.boundedCarrierRoleVertex stage role ∈
      TypeAFullD5Signature.declaredSupport ctx.G.object available.profile
        available.returnProducer coordinate.1)

/-- Fixed finite value attached to one actual D5 coordinate.  This packages
only observed lists; it does not enumerate the (very large) ambient bounded-
list alphabet. -/
noncomputable def fullBaseFixedValue
    (coordinate : available.FullBaseCoordinate) : FixedD5RoleValue := by
  classical
  let role := fullBaseRole (package := package) (stage := stage)
  rcases coordinate with ⟨coordinate, supported⟩
  rcases coordinate with cubic | (incidence | (port | (returned | (entry | (path | length)))))
  · let values := (available.profile.trace ctx.G.object cubic).support.map
        (fun vertex => vertex.1)
    have nodup : values.Nodup :=
      (available.profile.trace_support_nodup ctx.G.object cubic).map
        (fun _ _ equal => Subtype.ext equal)
    have valuesSupported : ∀ vertex ∈ values,
        vertex ∈ package.boundedActiveInterface stage := by
      intro vertex member
      apply supported
      exact TypeAFullD5Signature.canonicalTrace_mem_declaredSupport
        ctx.G.object available.profile available.returnProducer cubic member
    exact .inl (fixedD5RoleList (package := package) (stage := stage) values
      (roleList_length_le_30 (package := package) (stage := stage)
        values nodup valuesSupported))
  · have degreeBound :
        incidence.internalDegree ctx.G.object available.profile < 31 := by
      rw [TypeATraceIncidenceCoordinate.Coordinate.internalDegree]
      exact lt_of_le_of_lt
        (available.profile.degree_le_three
          (incidence.vertex ctx.G.object available.profile)) (by omega)
    exact .inr (.inl
      (role (incidence.ambientVertex ctx.G.object available.profile),
        ⟨incidence.internalDegree ctx.G.object available.profile, degreeBound⟩,
        incidence.terminal ctx.G.object available.profile))
  · exact .inr (.inr (.inl
      (role (port.receiver ctx.G.object available.profile).1,
        role (port.outside ctx.G.object available.profile))))
  · let values :=
        (TypeAFullD5Signature.anchored ctx.G.object available.profile
          available.returnProducer returned).path.support
    have nodup : values.Nodup :=
      (TypeAFullD5Signature.anchored ctx.G.object available.profile
        available.returnProducer returned).isPath ctx.G.object available.profile
        |>.support_nodup
    have valuesSupported : ∀ vertex ∈ values,
        vertex ∈ package.boundedActiveInterface stage := by
      intro vertex member
      apply supported
      exact TypeAFullD5Signature.canonicalReturn_mem_declaredSupport
        ctx.G.object available.profile available.returnProducer returned member
    exact .inr (.inr (.inr (.inl
      (fixedD5RoleList (package := package) (stage := stage) values
        (roleList_length_le_30 (package := package) (stage := stage)
          values nodup valuesSupported)))))
  · let first := TypeAFullD5Signature.firstEntry ctx.G.object available.profile
        available.returnProducer entry
    exact .inr (.inr (.inr (.inr (.inl
      (role (first.entry ctx.G.object available.profile entry
          (TypeAFullD5Signature.anchored ctx.G.object available.profile
            available.returnProducer entry)),
        role (first.predecessor ctx.G.object available.profile entry
          (TypeAFullD5Signature.anchored ctx.G.object available.profile
            available.returnProducer entry)))))))
  · let connector := TypeAFullD5Signature.connector ctx.G.object available.profile
        available.returnProducer path
    let values := connector.path.support
    have nodup : values.Nodup := connector.isPath.support_nodup
    have valuesSupported : ∀ vertex ∈ values,
        vertex ∈ package.boundedActiveInterface stage := by
      intro vertex member
      apply supported
      exact TypeAFullD5Signature.connectorPath_mem_declaredSupport
        ctx.G.object available.profile available.returnProducer path member
    exact Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
      (fixedD5RoleList (package := package) (stage := stage) values
        (roleList_length_le_30 (package := package) (stage := stage)
          values nodup valuesSupported)))))))
  · let anchored := TypeAFullD5Signature.anchored ctx.G.object available.profile
        available.returnProducer length
    let first := TypeAFullD5Signature.firstEntry ctx.G.object available.profile
        available.returnProducer length
    let connector := TypeAFullD5Signature.connector ctx.G.object available.profile
        available.returnProducer length
    let values := connector.path.support
    have nodup : values.Nodup := connector.isPath.support_nodup
    have valuesSupported : ∀ vertex ∈ values,
        vertex ∈ package.boundedActiveInterface stage := by
      intro vertex member
      apply supported
      exact TypeAFullD5Signature.connectorLength_mem_declaredSupport
        ctx.G.object available.profile available.returnProducer length member
    have supportLength : values.length ≤ 30 :=
      supportedNodupList_length_le_30 (package := package) (stage := stage)
        values nodup valuesSupported
    have connectorLength : connector.length ctx.G.object available.profile
        length anchored first < 31 := by
      have walkLength : values.length = connector.path.length + 1 := by
        simpa [values] using connector.path.length_support
      simp only [TypeAReceiverEntryChannel.Connector.length] at ⊢
      omega
    exact .inr (.inr (.inr (.inr (.inr (.inr
      ⟨connector.length ctx.G.object available.profile length anchored first,
        connectorLength⟩)))))

/-- Framework-owned normalization profile for the actually executed D5
carrier schedule. -/
noncomputable def fullBaseNormalizationProfile :
    Core.FiniteRoleSupportNormalization.Profile
      BoundedCarrierRole ctx.G.Vertex TypeAFullD5Signature.BaseKind
        FixedD5RoleLabel FixedD5RoleValue available.FullBaseCoordinate where
  roles := package.boundedCarrierRoles
  vertexDecEq := ctx.G.object.input.vertices.decEq
  roleVertex := package.boundedCarrierRoleVertex stage
  carrier := package.boundedActiveInterface stage
  memCarrier_iff_role := package.mem_boundedActiveInterface_iff_role stage
  coordinates := available.fullBaseCoordinates
  kind := fun coordinate => coordinate.1.kind ctx.G.object available.profile
  label := available.fullBaseFixedLabel
  support := fun coordinate =>
    TypeAFullD5Signature.declaredSupport ctx.G.object available.profile
      available.returnProducer coordinate.1
  supportContained := fun coordinate => coordinate.2
  value := available.fullBaseFixedValue

/-- Complete fixed code of one actually stored carrier-local D5 coordinate. -/
noncomputable def fullBaseFixedCode
    (coordinate : available.FullBaseCoordinate) : FixedD5Code :=
  available.fullBaseNormalizationProfile.code coordinate

/-- The fixed label alone already reflects the exact coordinate identity;
the remaining code fields retain the complete support and value rather than
being used as a surrogate for the label. -/
theorem fullBaseFixedLabel_injective :
    Function.Injective available.fullBaseFixedLabel := by
  intro left right equal
  have decoded := congrArg
    (FixedD5RoleLabel.decode (package := package) (stage := stage)) equal
  rw [available.fullBaseFixedLabel_decode_exact left,
    available.fullBaseFixedLabel_decode_exact right] at decoded
  apply Subtype.ext
  exact TypeAFullD5Signature.BaseCoordinate.label_injective
    ctx.G.object available.profile decoded

theorem fullBaseFixedCode_injective :
    Function.Injective available.fullBaseFixedCode := by
  intro left right equal
  exact available.fullBaseFixedLabel_injective
    (congrArg (fun code : FixedD5Code => code.2.1) equal)

/-- Equality of fixed codes is equivalent to equality of all four exact
graph-level D5 fields `(kind,label,support,value)`. -/
theorem fullBaseFixedCode_eq_iff_exactDatum
    (left right : available.FullBaseCoordinate) :
    available.fullBaseFixedCode left = available.fullBaseFixedCode right ↔
      TypeAFullD5Signature.exactDatum ctx.G.object available.profile
          available.returnProducer left.1 =
        TypeAFullD5Signature.exactDatum ctx.G.object available.profile
          available.returnProducer right.1 := by
  constructor
  · intro equal
    have coordinateEqual := available.fullBaseFixedCode_injective equal
    subst right
    rfl
  · intro equal
    have baseEqual := TypeAFullD5Signature.exactDatum_injective
      ctx.G.object available.profile available.returnProducer equal
    have coordinateEqual : left = right := Subtype.ext baseEqual
    subst right
    rfl

/-- The composed finite-ordinal code is injective without evaluating or
enumerating the fixed alphabet. -/
theorem fullBaseFinCode_injective : Function.Injective
    (fun coordinate : available.FullBaseCoordinate =>
      fixedD5CodeToFin (available.fullBaseFixedCode coordinate)) :=
  fixedD5CodeToFin_injective.comp available.fullBaseFixedCode_injective

/-- Observed-only normalized D5 schedule.  The only mapped list is the
carrier-first schedule already executed at this stage. -/
noncomputable def normalizedFullBaseCodes : List FixedD5Code := by
  exact Core.FiniteRoleSupportNormalization.Profile.normalizedCodes
    available.fullBaseNormalizationProfile

theorem normalizedFullBaseCodes_nodup :
    available.normalizedFullBaseCodes.Nodup := by
  exact Core.FiniteRoleSupportNormalization.Profile.normalizedCodes_nodup
    available.fullBaseNormalizationProfile

theorem normalizedFullBaseCodes_length_le_alphabet :
    available.normalizedFullBaseCodes.length ≤ FixedD5AlphabetSize := by
  rw [FixedD5AlphabetSize]
  exact Core.FiniteRoleSupportNormalization.Profile.normalizedCodes_length_le_card
    available.fullBaseNormalizationProfile

theorem everyFullBaseCoordinate_has_normalized_code
    (coordinate : available.FullBaseCoordinate) :
    available.fullBaseFixedCode coordinate ∈ available.normalizedFullBaseCodes := by
  exact Core.FiniteRoleSupportNormalization.Profile.every_coordinate_has_normalizedCode
    available.fullBaseNormalizationProfile coordinate

theorem everySupportedFullBaseCoordinateStored
    (coordinate : TypeAFullD5Signature.BaseCoordinate ctx.G.object available.profile)
    (supported : TypeAFullD5Signature.declaredSupport ctx.G.object available.profile
      available.returnProducer coordinate ⊆ package.boundedActiveInterface stage) :
    (⟨coordinate, supported⟩ : available.FullBaseCoordinate) ∈
      available.fullBaseCoordinates.orderedValues :=
  TypeAFullD5Signature.localBaseCoordinate_mem_fromCarrier ctx.G.object available.profile
    available.returnProducer (package.boundedActiveInterface stage)
    (package.boundedCarrierVertices stage) ⟨coordinate, supported⟩

/-- Exact source-by-position bound for the full-parent-trace incidence family.
The proof uses only the carrier bound `|A_i| ≤ 30`; it never scans the ambient
prefix or a path universe. -/
theorem localTraceIncidences_card_le_900 :
    (TypeAFullD5Signature.localTraceIncidencesFromCarrier ctx.G.object available.profile
      (package.boundedActiveInterface stage)
      (package.boundedCarrierVertices stage)).card ≤ 900 :=
  TypeAFullD5Signature.localTraceIncidencesFromCarrier_card_le_900
    ctx.G.object available.profile (package.boundedActiveInterface stage)
    (package.boundedCarrierVertices stage)
    (package.boundedActiveInterface_card_le_30 stage)

/-- Fixed primitive-decision envelope for the entire carrier-first D5 base
schedule on the deduplicated 28-role interface. -/
theorem carrierFirstD5Checks_le_5516 :
    TypeAFullD5Signature.carrierVisibleChecks
      (package.boundedActiveInterface stage) ≤ 5516 :=
  TypeAFullD5Signature.carrierVisibleChecks_le_5516
    (package.boundedActiveInterface stage)
    (package.boundedActiveInterface_card_le_28 stage)

end D5Available

inductive D5Result (stage : package.Stage) where
  | d6 (high : WalkTypeAD5Projection.High (package.ambientPrefix stage))
  | d5 (available : package.D5Available stage)

/-- Exact paper routing at D5: a first high center leaves through D6; otherwise
the same prefix has its complete locally supported Type-A D5 schedule. -/
noncomputable def runD5 (stage : package.Stage) : package.D5Result stage := by
  cases package.d5DegreeSplit stage with
  | high high => exact .d6 high
  | noHigh noHigh =>
      let profile := package.D5Profile stage noHigh
      exact .d5 {
        noHigh := noHigh
        profile := profile
        profileExact := rfl
        coordinates := WalkTypeAD5Projection.Profile.coordinates profile
        coordinatesExact := rfl
        returnProducer := package.d5ReturnProducer stage noHigh
        returnProducerExact := rfl
      }

theorem runD5_exhaustive (stage : package.Stage) :
    (∃ high, package.runD5 stage = .d6 high) ∨
      (∃ available, package.runD5 stage = .d5 available) := by
  cases equation : package.runD5 stage with
  | d6 high => exact Or.inl ⟨high, rfl⟩
  | d5 available => exact Or.inr ⟨available, rfl⟩

end

end P13WeightedColdRestrictedPrefixPackage

end Erdos64EG.Internal
