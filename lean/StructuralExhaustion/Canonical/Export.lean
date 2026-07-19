import StructuralExhaustion.Canonical.Registry
import StructuralExhaustion.Canonical.DocumentationRegistry
import StructuralExhaustion.CT1.TargetEncoding
import StructuralExhaustion.CT2.CertifiedReduction
import StructuralExhaustion.CT2.LocalDeletion
import StructuralExhaustion.CT3.TargetCompression
import StructuralExhaustion.CT4.Cardinality
import StructuralExhaustion.CT11.NegativeBudget
import StructuralExhaustion.CT12.DisjointPacking
import StructuralExhaustion.CT12.ListPeeling
import StructuralExhaustion.CT12.RefinedLedgerCompletion
import Lean

open Lean Meta Elab Command

namespace StructuralExhaustion.Canonical.Export

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def inductiveConstructors
    (env : Environment) (name : Name) : CommandElabM (Array Name) := do
  let some (.inductInfo info) := env.find? name
    | throwError "automation-first export: missing inductive declaration {name}"
  pure info.ctors.toArray

private def reducedString (expression : Expr) : TermElabM String := do
  let value ← whnf expression
  match value with
  | .lit (.strVal result) => pure result
  | _ => throwError "automation-first export: expected a reduced string, got {value}"

private def nodeCode (codeDeclaration constructor : Name) : CommandElabM String :=
  liftTermElabM do
    reducedString (mkApp (mkConst codeDeclaration) (mkConst constructor))

private def edgeEndpoints (info : ConstantInfo) : CommandElabM (Expr × Expr) :=
  liftTermElabM do
    forallTelescopeReducing info.type fun _ result => do
      let arguments := result.getAppArgs
      if arguments.size < 2 then
        throwError "automation-first export: edge result has too few indices: {result}"
      pure (arguments[arguments.size - 2]!, arguments[arguments.size - 1]!)

private def expressionNodeCode
    (codeDeclaration : Name) (expression : Expr) : CommandElabM String :=
  liftTermElabM do reducedString (mkApp (mkConst codeDeclaration) expression)

private def declarationType (info : ConstantInfo) : CommandElabM String :=
  liftTermElabM do pure (toString (← ppExpr info.type))

private def declarationJson
    (env : Environment) (name : Name) : CommandElabM Json := do
  let some info := env.find? name
    | throwError "automation-first export: missing declaration {name}"
  pure <| Json.mkObj [
    ("name", toJson name.toString),
    ("kind", toJson (declarationKind info)),
    ("type", toJson (← declarationType info))
  ]

private def optionalDeclarationJson
    (env : Environment) (name : Name) : CommandElabM (Option Json) := do
  match env.find? name with
  | none => pure none
  | some _ => pure (some (← declarationJson env name))

private def provisionedRefJson (reference : Core.ProvisionedRef) : Json :=
  Json.mkObj [
    ("ref", toJson reference.ref),
    ("provision", toJson reference.provision.key)
  ]

private def provisionedRefsJson (references : List Core.ProvisionedRef) : Json :=
  Json.arr (references.map provisionedRefJson).toArray

private def duplicate? (values : List String) : Option String :=
  match values with
  | [] => none
  | value :: rest =>
      if rest.contains value then some value else duplicate? rest

private def distinctStrings (values : List String) : List String :=
  values.foldl (fun result value =>
    if result.contains value then result else result ++ [value]) []

private def capabilityRequirementJson
    (concepts : List CapabilityConcept)
    (reference : Core.ProvisionedRef) : CommandElabM Json := do
  let some concept := concepts.find? fun concept =>
      concept.requirementRef == reference.ref
    | throwError
        "automation-first export: no capability concept for requirement {reference.ref}"
  pure <| Json.mkObj [
    ("ref", toJson reference.ref),
    ("provision", toJson reference.provision.key),
    ("conceptId", toJson concept.conceptId)
  ]

private def capabilityConceptJson
    (env : Environment) (concept : CapabilityConcept) : CommandElabM Json := do
  let formalDeclaration ← declarationJson env concept.declarationName
  let presentation := Json.mkObj [
    ("label", toJson concept.presentation.label),
    ("mathematicalDefinition",
      toJson concept.presentation.mathematicalDefinition),
    ("plainExplanation", toJson concept.presentation.plainExplanation)
  ]
  pure <| Json.mkObj [
    ("conceptId", toJson concept.conceptId),
    ("requirementRef", toJson concept.requirementRef),
    ("formalDeclaration", formalDeclaration),
    ("presentation", presentation)
  ]

private def theoremRefs (names : List String) : List Core.ProvisionedRef :=
  names.map fun name => ⟨name, .derivedByGenericTheorem⟩

private def automationJson (contract : Core.NodeAutomationContract) : Json :=
  let inferred := contract.inferredInputs
  let predecessor := contract.predecessorInputs
  let derived := contract.frameworkDerivedInputs
  let frameworkTheorems := theoremRefs contract.frameworkTheorems
  let transitive := contract.authorInputs ++ inferred ++ predecessor ++
    derived ++ frameworkTheorems
  Json.mkObj [
    ("executionClass", toJson contract.executionClass.key),
    ("authorInputs", provisionedRefsJson contract.authorInputs),
    ("inferredInputs", provisionedRefsJson inferred),
    ("predecessorInputs", provisionedRefsJson predecessor),
    ("derivedInputs", provisionedRefsJson derived),
    ("transitiveDependencies", provisionedRefsJson transitive),
    ("frameworkTheorems", provisionedRefsJson frameworkTheorems),
    ("generatedOutputs", provisionedRefsJson contract.generatedOutputs),
    ("manualObligations", Json.arr (contract.manualObligations.map toJson).toArray)
  ]

private def capabilityJson
    (concepts : List CapabilityConcept)
    (contract : Core.CapabilityContract) : CommandElabM Json := do
  let requiredInstances := contract.requiredInstances.map fun reference =>
    Core.ProvisionedRef.mk reference .typeclassInferred
  let derivedOperations := contract.derivedOperations.map fun reference =>
    Core.ProvisionedRef.mk reference .frameworkConstant
  let requiredDefinitions ← contract.requiredDefinitions.mapM
    (capabilityRequirementJson concepts)
  pure <| Json.mkObj [
    ("capabilityId", toJson contract.capabilityId),
    ("tacticId", toJson contract.tacticId),
    ("requiredDefinitions", Json.arr requiredDefinitions.toArray),
    ("requiredInstances", provisionedRefsJson requiredInstances),
    ("derivedOperations", provisionedRefsJson derivedOperations)
  ]

private def residualFieldJson (field : Core.ResidualFieldContract) : Json :=
  Json.mkObj [
    ("fieldName", toJson field.fieldName),
    ("leanType", toJson field.leanType),
    ("provision", toJson field.provision.key)
  ]

private def residualKindJson (contract : Core.ResidualKindContract) : Json :=
  Json.mkObj [
    ("residualKindId", toJson contract.residualKindId),
    ("leanType", toJson contract.leanType),
    ("semanticFields", Json.arr
      (contract.semanticFields.map residualFieldJson).toArray),
    ("inheritedContext", toJson contract.inheritedContext.key)
  ]

private def stringListJson (values : List String) : Json :=
  Json.arr (values.map toJson).toArray

private def transitionSemanticDiscoveryJson
    (discovery : Core.TransitionSemanticDiscovery) : Json :=
  Json.mkObj [
    ("kind", toJson discovery.key),
    ("adapterType", match discovery.adapterType? with
      | none => Json.null
      | some adapterType => toJson adapterType)
  ]

private def transitionAuthoringBoundaryJson
    (contract : Core.CTTransitionProfileContract) : Json :=
  Json.mkObj [
    ("semanticDiscovery", transitionSemanticDiscoveryJson contract.semanticDiscovery),
    ("problemSpecificInputs", stringListJson
      (contract.problemSpecificInputs.map Core.TransitionProblemInput.key)),
    ("frameworkOwnedResponsibilities", stringListJson
      (Core.CTTransitionFrameworkResponsibility.all.map
        Core.CTTransitionFrameworkResponsibility.key))
  ]

private def transitionProfileJson
    (contract : Core.CTTransitionProfileContract) : Json :=
  Json.mkObj [
    ("profileId", toJson contract.profileId),
    ("familyId", toJson contract.familyId),
    ("sourceTacticId", toJson contract.sourceTacticId),
    ("targetTacticId", toJson contract.targetTacticId),
    ("sourceResidualKind", toJson contract.sourceResidualKind),
    ("targetExecutableInterface", toJson contract.targetExecutableInterface),
    ("transitionConstructor", toJson contract.transitionConstructor),
    ("advanceExecutor", toJson contract.advanceExecutor),
    ("selectionClass", toJson contract.selectionClass.key),
    ("authoringBoundary", transitionAuthoringBoundaryJson contract)
  ]

private def transitionFamilyJson
    (family : RegisteredTransitionFamilyDescriptor) : Json :=
  Json.mkObj [
    ("familyId", toJson family.familyId),
    ("sourceTacticId", toJson family.sourceTacticId),
    ("targetTacticId", toJson family.targetTacticId),
    ("profileIds", stringListJson
      (family.profiles.map fun profile => profile.contract.profileId))
  ]

private def dottedName (reference : String) : Name :=
  (reference.splitOn ".").foldl (fun name component => name.str component)
    .anonymous

private def sourcePath (namespaceName : Name) : String :=
  String.intercalate "/" (namespaceName.toString.splitOn ".") ++ ".lean"

private def prefixedName (namePrefix : Name) (reference : String) : Name :=
  (reference.splitOn ".").foldl (fun name component => name.str component) namePrefix

private def projectName (name : Name) : Bool :=
  (`StructuralExhaustion).isPrefixOf name

private def distinctNames (names : List Name) : List Name :=
  names.foldl (fun result name =>
    if result.contains name then result else result ++ [name]) []

private def sortedNames (names : List Name) : List Name :=
  distinctNames names |>.mergeSort fun first second =>
    first.toString < second.toString

private def typeDependencies (info : ConstantInfo) : List Name :=
  sortedNames info.type.getUsedConstants.toList

private def valueDependencies : ConstantInfo → List Name
  | .defnInfo info => sortedNames info.value.getUsedConstants.toList
  | .thmInfo info => sortedNames info.value.getUsedConstants.toList
  | .opaqueInfo info => sortedNames info.value.getUsedConstants.toList
  | .inductInfo info => sortedNames info.ctors
  | _ => []

private def hasBody : ConstantInfo → Bool
  | .defnInfo _ | .thmInfo _ | .opaqueInfo _ => true
  | _ => false

private def directProjectDependencies
    (env : Environment) (name : Name) : List Name :=
  match env.find? name with
  | none => []
  | some info =>
      sortedNames <| (typeDependencies info ++ valueDependencies info).filter fun dependency =>
        projectName dependency && dependency != name

private partial def projectDeclarationClosure
    (env : Environment) (pending seen : List Name) : List Name :=
  match pending with
  | [] => seen.reverse
  | name :: rest =>
      if seen.contains name then projectDeclarationClosure env rest seen
      else
        projectDeclarationClosure env
          (rest ++ directProjectDependencies env name) (name :: seen)

private def referenceCandidates
    (tactic : TacticDescriptor) (reference : String) : List Name :=
  distinctNames [
    dottedName reference,
    prefixedName `StructuralExhaustion reference,
    prefixedName tactic.namespaceName reference,
    prefixedName `StructuralExhaustion.Core reference
  ]

private def resolveReference?
    (env : Environment) (tactic : TacticDescriptor) (reference : String) : Option Name :=
  (referenceCandidates tactic reference).find? fun candidate =>
    env.find? candidate |>.isSome

private def positionJson (position : Position) : Json :=
  Json.mkObj [
    ("line", toJson position.line),
    ("column", toJson position.column)
  ]

private def rangeJson (range : DeclarationRange) : Json :=
  Json.mkObj [
    ("start", positionJson range.pos),
    ("end", positionJson range.endPos)
  ]

private def declarationModule?
    (env : Environment) (name : Name) : Option Name := do
  let moduleIdx ← env.getModuleIdxFor? name
  pure env.header.moduleNames[moduleIdx.toNat]!

private def internalDeclarationJson
    (env : Environment) (name : Name) : CommandElabM Json := do
  let some info := env.find? name
    | throwError "automation-first export: missing internal declaration {name}"
  let typeDeps := typeDependencies info |>.filter (· != name)
  let bodyDeps := valueDependencies info |>.filter fun dependency =>
    dependency != name && !typeDeps.contains dependency
  let ranges? ← findDeclarationRanges? name
  let rangeValue := match ranges? with
    | none => Json.null
    | some ranges => rangeJson ranges.range
  let selectionRangeValue := match ranges? with
    | none => Json.null
    | some ranges => rangeJson ranges.selectionRange
  let moduleValue := match declarationModule? env name with
    | none => Json.null
    | some moduleName => toJson moduleName.toString
  let sourceValue := match declarationModule? env name with
    | none => Json.null
    | some moduleName => toJson (sourcePath moduleName)
  let docValue := match ← findDocString? env name with
    | none => Json.null
    | some doc => toJson doc
  pure <| Json.mkObj [
    ("declarationId", toJson name.toString),
    ("name", toJson name.toString),
    ("kind", toJson (declarationKind info)),
    ("type", toJson (← declarationType info)),
    ("docString", docValue),
    ("module", moduleValue),
    ("sourceFile", sourceValue),
    ("range", rangeValue),
    ("selectionRange", selectionRangeValue),
    ("bodyAvailable", toJson (hasBody info)),
    ("typeDependencies", toJson (typeDeps.map (·.toString))),
    ("bodyDependencies", toJson (bodyDeps.map (·.toString)))
  ]

private def genericStepExplanation
    (step : NodeInternalStepDescriptor) : String :=
  match step.role with
  | .authorObject =>
      s!"Application-supplied mathematical data or operation used by this node: {step.reference.ref}."
  | .inferredInstance =>
      s!"Executable instance inferred by Lean for this node: {step.reference.ref}."
  | .predecessorState =>
      s!"Typed state inherited from the immediately preceding CT node: {step.reference.ref}."
  | .operation =>
      s!"Framework-owned operation executed inside this node: {step.reference.ref}."
  | .theorem =>
      s!"Framework theorem certifying the semantic correctness of this node: {step.reference.ref}."
  | .output =>
      s!"State, decision, certificate, or residual produced by this node: {step.reference.ref}."

private def internalStepDeclaration?
    (env : Environment) (tactic : TacticDescriptor)
    (step : NodeInternalStepDescriptor) : Option Name :=
  match tactic.capabilityConcepts.find? fun concept =>
      concept.requirementRef == step.reference.ref with
  | some concept => some concept.declarationName
  | none => resolveReference? env tactic step.reference.ref

private def internalStepJson
    (env : Environment) (tactic : TacticDescriptor)
    (step : NodeInternalStepDescriptor) : CommandElabM Json := do
  let concept? := tactic.capabilityConcepts.find? fun concept =>
    concept.requirementRef == step.reference.ref
  let declaration? := internalStepDeclaration? env tactic step
  let label := match concept? with
    | some concept => concept.presentation.label
    | none => step.reference.ref
  let explanation ← match concept?, declaration? with
    | some concept, _ => pure concept.presentation.plainExplanation
    | none, some declaration => do
        let doc? ← findDocString? env declaration
        pure (doc?.getD (genericStepExplanation step))
    | none, none => pure (genericStepExplanation step)
  let mathematicalDefinition := match concept? with
    | some concept => toJson concept.presentation.mathematicalDefinition
    | none => Json.null
  pure <| Json.mkObj [
    ("stepId", toJson step.stepId),
    ("label", toJson label),
    ("role", toJson step.role.key),
    ("reference", provisionedRefJson step.reference),
    ("declarationId", match declaration? with
      | none => Json.null
      | some declaration => toJson declaration.toString),
    ("plainExplanation", toJson explanation),
    ("mathematicalDefinition", mathematicalDefinition)
  ]

private def internalEdgeJson (edge : NodeInternalEdgeDescriptor) : Json :=
  Json.mkObj [
    ("edgeId", toJson edge.edgeId),
    ("sourceStepId", toJson edge.sourceStepId),
    ("targetStepId", toJson edge.targetStepId),
    ("relation", toJson edge.relation.key)
  ]

private def internalFlowJson
    (env : Environment) (tactic : TacticDescriptor)
    (flow : NodeInternalFlowDescriptor) : CommandElabM Json := do
  pure <| Json.mkObj [
    ("nodeId", toJson flow.nodeId),
    ("steps", Json.arr (← flow.steps.mapM (internalStepJson env tactic)).toArray),
    ("edges", Json.arr (flow.edges.map internalEdgeJson).toArray)
  ]

private def contractReferences
    (contract : Core.NodeAutomationContract) : List String :=
  (contract.authorInputs ++ contract.derivedInputs ++
    (contract.frameworkTheorems.map fun name =>
      Core.ProvisionedRef.mk name .derivedByGenericTheorem) ++
    contract.generatedOutputs).map (·.ref)

private def validateInternalFlow
    (contract : Core.NodeAutomationContract)
    (flow : NodeInternalFlowDescriptor) : CommandElabM Unit := do
  unless flow.nodeId == contract.nodeId do
    throwError
      "automation-first export: internal flow {flow.nodeId} does not match {contract.nodeId}"
  let stepIds := flow.steps.map (·.stepId)
  let edgeIds := flow.edges.map (·.edgeId)
  if let some duplicate := duplicate? stepIds then
    throwError "automation-first export: {flow.nodeId} repeats internal step {duplicate}"
  if let some duplicate := duplicate? edgeIds then
    throwError "automation-first export: {flow.nodeId} repeats internal edge {duplicate}"
  for edge in flow.edges do
    unless stepIds.contains edge.sourceStepId && stepIds.contains edge.targetStepId do
      throwError
        "automation-first export: {flow.nodeId} internal edge {edge.edgeId} has an unknown endpoint"
  let expected := contractReferences contract
  let actual := flow.steps.map (·.reference.ref)
  if let some duplicate := duplicate? actual then
    throwError
      "automation-first export: {flow.nodeId} classifies internal reference {duplicate} twice"
  for reference in expected do
    unless actual.contains reference do
      throwError
        "automation-first export: {flow.nodeId} does not expose internal reference {reference}"
  for reference in actual do
    unless expected.contains reference do
      throwError
        "automation-first export: {flow.nodeId} exposes unrelated internal reference {reference}"

private def hasFragment (value fragment : String) : Bool :=
  (value.splitOn fragment).length > 1

private def hasToken (value token : String) : Bool :=
  (value.splitOn ".").contains token

private def nodeKind
    (code : String) (isTerminal : Bool) (incomingTypes : List String) : String :=
  if isTerminal then
    if hasToken code "certificate" || hasToken code "c1" ||
        hasToken code "c2" || hasToken code "c3" || hasToken code "c4" ||
        hasToken code "c5" || incomingTypes.any (hasFragment · "Certificate") then
      "certificate"
    else
      "residual"
  else if hasToken code "entry" then
    "entry"
  else if hasToken code "certify" || hasToken code "verify" then
    "certification"
  else if hasToken code "decide" || hasToken code "compare" then
    "decision"
  else if hasToken code "compute" || hasToken code "search" then
    "computation"
  else if hasToken code "loop" then
    "loop"
  else
    "definition"

private def terminalCase (code tacticId : String) : CommandElabM String := do
  let terminalPrefix := tacticId ++ ".terminal."
  unless code.startsWith terminalPrefix do
    throwError "automation-first export: terminal maps to nonterminal node {code}"
  pure (code.drop terminalPrefix.length |>.toString)

private structure TransitionSnapshot where
  ordinal : Nat
  edgeId : String
  constructor : Name
  constructorType : String
  sourceNode : String
  targetNode : String

namespace TransitionSnapshot

def contractJson (edge : TransitionSnapshot) : Json :=
  Json.mkObj [
    ("edgeId", toJson edge.edgeId),
    ("constructor", toJson edge.constructor.toString),
    ("constructorType", toJson edge.constructorType),
    ("sourceNode", toJson edge.sourceNode),
    ("targetNode", toJson edge.targetNode)
  ]

def json (edge : TransitionSnapshot) : Json :=
  Json.mkObj [
    ("ordinal", toJson edge.ordinal),
    ("edgeId", toJson edge.edgeId),
    ("constructor", toJson edge.constructor.toString),
    ("constructorType", toJson edge.constructorType),
    ("sourceNode", toJson edge.sourceNode),
    ("targetNode", toJson edge.targetNode),
    ("provision", toJson Core.Provision.generatedAudit.key)
  ]

end TransitionSnapshot

private structure TerminalSnapshot where
  ordinal : Nat
  caseName : String
  nodeId : String
  constructor : Name

namespace TerminalSnapshot

def json (terminal : TerminalSnapshot) : Json :=
  Json.mkObj [
    ("ordinal", toJson terminal.ordinal),
    ("case", toJson terminal.caseName),
    ("nodeId", toJson terminal.nodeId),
    ("constructor", toJson terminal.constructor.toString)
  ]

end TerminalSnapshot

private def terminalAutomationContract
    (tactic : TacticDescriptor) (code : String)
    (incoming : Array TransitionSnapshot) : Core.NodeAutomationContract :=
  let predecessor := incoming.toList.map fun edge =>
    Core.ProvisionedRef.mk edge.constructor.toString .derivedFromPredecessor
  let theoremName := tactic.namespaceName.toString ++ ".run_trace_valid"
  let output := Core.ProvisionedRef.mk
    (tactic.namespaceName.toString ++ ".ExecutionResult@" ++ code) .generatedAudit
  {
    nodeId := code
    executionClass := .genericTheorem
    authorInputs := []
    derivedInputs := predecessor
    frameworkTheorems := [theoremName]
    generatedOutputs := [output]
    manualObligations := []
  }

private def validateCapabilityConcepts
    (env : Environment) (tactic : TacticDescriptor) : CommandElabM Unit := do
  let requirements := distinctStrings <|
    (tactic.capabilityContract.requiredDefinitions ++
      tactic.capabilityProfiles.flatMap (·.requiredDefinitions)).map (·.ref)
  let conceptIds := tactic.capabilityConcepts.map (·.conceptId)
  let conceptRefs := tactic.capabilityConcepts.map (·.requirementRef)
  let declarationNames := tactic.capabilityConcepts.map
    (·.declarationName.toString)
  if let some duplicate := duplicate? conceptIds then
    throwError
      "automation-first export: {tactic.tacticId} duplicates capability concept id {duplicate}"
  if let some duplicate := duplicate? conceptRefs then
    throwError
      "automation-first export: {tactic.tacticId} duplicates concept requirement {duplicate}"
  if let some duplicate := duplicate? declarationNames then
    throwError
      "automation-first export: {tactic.tacticId} maps multiple concepts to declaration {duplicate}"
  for requirement in requirements do
    unless conceptRefs.contains requirement do
      throwError
        "automation-first export: {tactic.tacticId} requirement {requirement} has no capability concept"
  for concept in tactic.capabilityConcepts do
    unless requirements.contains concept.requirementRef do
      throwError
        "automation-first export: {tactic.tacticId} capability concept {concept.conceptId} is orphaned from {concept.requirementRef}"
    let expectedDeclaration :=
      if concept.requirementRef.startsWith "StructuralExhaustion." then
        dottedName concept.requirementRef
      else
        (concept.requirementRef.splitOn ".").foldl
          (fun name component => name.str component) tactic.namespaceName
    unless concept.declarationName == expectedDeclaration do
      throwError
        "automation-first export: capability concept {concept.conceptId} binds {concept.requirementRef} to {concept.declarationName}, expected {expectedDeclaration}"
    if concept.conceptId.isEmpty then
      throwError
        "automation-first export: {tactic.tacticId} has an empty capability concept id"
    if concept.presentation.label.isEmpty ||
        concept.presentation.mathematicalDefinition.isEmpty ||
        concept.presentation.plainExplanation.isEmpty then
      throwError
        "automation-first export: capability concept {concept.conceptId} has incomplete presentation metadata"
    unless env.find? concept.declarationName |>.isSome do
      throwError
        "automation-first export: capability concept {concept.conceptId} has unknown declaration {concept.declarationName}"

private def tacticJson
    (env : Environment) (tactic : TacticDescriptor) : CommandElabM Json := do
  unless tactic.capabilityContract.tacticId == tactic.tacticId do
    throwError
      "automation-first export: {tactic.tacticId} capability has tacticId {tactic.capabilityContract.tacticId}"
  for profile in tactic.capabilityProfiles do
    unless profile.tacticId == tactic.tacticId do
      throwError
        "automation-first export: {profile.capabilityId} has tacticId {profile.tacticId}, expected {tactic.tacticId}"
  validateCapabilityConcepts env tactic

  let graphNamespace := tactic.namespaceName.str "Graph"
  let nodeType := graphNamespace.str "NodeId"
  let codeDeclaration := nodeType.str "code"
  let edgeType := graphNamespace.str "Edge"
  let terminalType := graphNamespace.str "Terminal"
  let terminalNodeId := terminalType.str "nodeId"

  let edgeConstructors ← inductiveConstructors env edgeType
  let transitions ← edgeConstructors.mapIdxM fun index constructor => do
    let some info := env.find? constructor
      | throwError "automation-first export: missing edge constructor {constructor}"
    let (sourceExpression, targetExpression) ← edgeEndpoints info
    let sourceNode ← expressionNodeCode codeDeclaration sourceExpression
    let targetNode ← expressionNodeCode codeDeclaration targetExpression
    pure ({
      ordinal := index + 1
      edgeId := s!"{tactic.tacticId}.edge.{constructor.getString!}"
      constructor := constructor
      constructorType := ← declarationType info
      sourceNode := sourceNode
      targetNode := targetNode
    } : TransitionSnapshot)

  let terminalConstructors ← inductiveConstructors env terminalType
  let terminals ← terminalConstructors.mapIdxM fun index constructor => do
    let nodeExpression ← liftTermElabM do
      whnf (mkApp (mkConst terminalNodeId) (mkConst constructor))
    let code ← expressionNodeCode codeDeclaration nodeExpression
    let caseName ← terminalCase code tactic.tacticId
    pure ({
      ordinal := index + 1
      caseName := caseName
      nodeId := code
      constructor := constructor
    } : TerminalSnapshot)

  let terminalCodes := terminals.toList.map (·.nodeId)
  let nodeConstructors ← inductiveConstructors env nodeType
  let nodes ← nodeConstructors.mapIdxM fun index constructor => do
    let code ← nodeCode codeDeclaration constructor
    let incoming := transitions.filter fun edge => edge.targetNode == code
    let outgoing := transitions.filter fun edge => edge.sourceNode == code
    let isTerminal := terminalCodes.contains code
    let kind := nodeKind code isTerminal
      (incoming.toList.map (·.constructorType))
    let matchingContracts := tactic.nodeAutomationContracts.filter fun contract =>
      contract.nodeId == code
    let contract ← match isTerminal, matchingContracts with
      | true, [] => pure (terminalAutomationContract tactic code incoming)
      | true, _ =>
          throwError
            "automation-first export: terminal {code} has an executable node contract"
      | false, [contract] => do
          if contract.generatedOutputs.isEmpty then
            throwError "automation-first export: {code} has no generated outputs"
          unless contract.manualObligations.isEmpty do
            throwError "automation-first export: {code} retains manual obligations"
          unless contract.authorInputs.all fun input => input.provision.isAuthorProvided do
            throwError "automation-first export: {code} misclassifies an author input"
          unless contract.derivedInputs.all fun input => input.provision.isFrameworkDerived do
            throwError "automation-first export: {code} misclassifies a derived input"
          pure contract
      | false, [] =>
          throwError "automation-first export: nonterminal {code} has no node contract"
      | false, _ =>
          throwError "automation-first export: nonterminal {code} has duplicate contracts"
    let flow ← if isTerminal then
        pure (NodeInternalFlowDescriptor.ofContract contract)
      else
        match tactic.nodeInternalFlows.filter fun candidate => candidate.nodeId == code with
        | [candidate] => pure candidate
        | [] => throwError
            "automation-first export: nonterminal {code} has no internal flow"
        | _ => throwError
            "automation-first export: nonterminal {code} has duplicate internal flows"
    validateInternalFlow contract flow
    let automation := automationJson contract
    let internalFlow ← internalFlowJson env tactic flow
    let formalContract := Json.mkObj [
      ("predecessorIndexed", toJson true),
      ("incomingEdges", Json.arr (incoming.map (·.contractJson))),
      ("outgoingEdges", Json.arr (outgoing.map (·.contractJson)))
    ]
    let presentation := Json.mkObj [
      ("label", toJson code),
      ("summary", toJson s!"Compiled {kind} node with an explicit automation contract.")
    ]
    pure <| Json.mkObj [
      ("ordinal", toJson (index + 1)),
      ("nodeId", toJson code),
      ("semanticId", toJson code),
      ("nodeKind", toJson kind),
      ("constructor", toJson constructor.toString),
      ("sourceFile", toJson (sourcePath graphNamespace)),
      ("formalContract", formalContract),
      ("automation", automation),
      ("internalFlow", internalFlow),
      ("presentation", presentation)
    ]

  let nodeCodes ← nodeConstructors.mapM (nodeCode codeDeclaration)
  let nonterminalCodes := nodeCodes.toList.filter fun code =>
    !(terminalCodes.contains code)
  for contract in tactic.nodeAutomationContracts do
    unless nonterminalCodes.contains contract.nodeId do
      throwError
        "automation-first export: node contract {contract.nodeId} is not a nonterminal constructor"
  for flow in tactic.nodeInternalFlows do
    unless nonterminalCodes.contains flow.nodeId do
      throwError
        "automation-first export: internal flow {flow.nodeId} is not a nonterminal constructor"

  let terminalFlows := terminalCodes.map fun code =>
    let incoming := transitions.filter fun edge => edge.targetNode == code
    NodeInternalFlowDescriptor.ofContract
      (terminalAutomationContract tactic code incoming)
  let allInternalFlows := tactic.nodeInternalFlows ++ terminalFlows
  let internalRoots := allInternalFlows.flatMap (·.steps) |>.filterMap fun step =>
    internalStepDeclaration? env tactic step
  let internalNames := projectDeclarationClosure env internalRoots []
  let internalDeclarations ← internalNames.mapM (internalDeclarationJson env)

  for residual in tactic.residualKindContracts do
    if residual.semanticFields.isEmpty then
      throwError
        "automation-first export: residual {residual.residualKindId} has no semantic fields"

  let apiNames := [
    nodeType,
    codeDeclaration,
    edgeType,
    terminalType,
    terminalNodeId,
    graphNamespace.str "Path",
    graphNamespace.str "ValidTrace",
    tactic.namespaceName.str "Capability",
    tactic.namespaceName.str "Input",
    tactic.namespaceName.str "ExecutionResult",
    tactic.namespaceName.str "RawOutcome",
    tactic.namespaceName.str "Outcome",
    tactic.namespaceName.str "CoreOutcome",
    tactic.namespaceName.str "run",
    tactic.namespaceName.str "runCore",
    tactic.namespaceName.str "runReference",
    tactic.namespaceName.str "run_verified",
    tactic.namespaceName.str "run_trace_valid",
    tactic.namespaceName.str "run_total",
    tactic.namespaceName.str "run_deterministic",
    tactic.namespaceName.str "outcome_exhaustive",
    tactic.namespaceName.str "capabilityContract",
    tactic.namespaceName.str "nodeAutomationContracts",
    tactic.namespaceName.str "residualKindContracts"
  ]
  let apiDeclarations ← apiNames.filterMapM (optionalDeclarationJson env)
  for required in ["run", "run_verified", "run_trace_valid", "run_total",
      "run_deterministic"] do
    let name := tactic.namespaceName.str required
    unless env.find? name |>.isSome do
      throwError "automation-first export: {tactic.tacticId} lacks {name}"

  let decreaseCandidates := [
    graphNamespace.str "Edge" |>.str "loopBack_decreases",
    graphNamespace.str "Edge" |>.str "loop_decreases",
    tactic.namespaceName.str "run_iterations_bounded"
  ]
  let decreaseDeclarations ← decreaseCandidates.filterMapM
    (optionalDeclarationJson env)
  let loopDecrease := decreaseDeclarations.head?.getD Json.null
  let capability ← capabilityJson tactic.capabilityConcepts
    tactic.capabilityContract
  let capabilityProfiles ← tactic.capabilityProfiles.mapM
    (capabilityJson tactic.capabilityConcepts)
  let capabilityConcepts ← tactic.capabilityConcepts.mapM
    (capabilityConceptJson env)

  pure <| Json.mkObj [
    ("tacticId", toJson tactic.tacticId),
    ("title", toJson tactic.title),
    ("apiVersion", toJson tactic.apiVersion),
    ("namespace", toJson tactic.namespaceName.toString),
    ("capability", capability),
    ("capabilityProfiles", Json.arr capabilityProfiles.toArray),
    ("capabilityConcepts", Json.arr capabilityConcepts.toArray),
    ("nodes", Json.arr nodes),
    ("transitions", Json.arr (transitions.map TransitionSnapshot.json)),
    ("terminals", Json.arr (terminals.map TerminalSnapshot.json)),
    ("residualKinds", Json.arr
      (tactic.residualKindContracts.map residualKindJson).toArray),
    ("apiDeclarations", Json.arr apiDeclarations.toArray),
    ("internalDeclarations", Json.arr internalDeclarations.toArray),
    ("loopDecrease", loopDecrease)
  ]

private def exportCatalog : CommandElabM Unit := do
  let env ← getEnv
  let tacticIds := Canonical.tactics.toList.map (·.tacticId)
  if let some duplicate := duplicate? tacticIds then
    throwError "automation-first export: duplicate tactic id {duplicate}"
  let conceptIds := Canonical.tactics.toList.flatMap fun tactic =>
    tactic.capabilityConcepts.map (·.conceptId)
  if let some duplicate := duplicate? conceptIds then
    throwError "automation-first export: duplicate capability concept id {duplicate}"
  let residualIds := Canonical.tactics.toList.flatMap fun tactic =>
    tactic.residualKindContracts.map (·.residualKindId)
  if let some duplicate := duplicate? residualIds then
    throwError "automation-first export: duplicate residual id {duplicate}"
  let profileIds := Canonical.transitionProfiles.map (·.contract.profileId)
  if let some duplicate := duplicate? profileIds then
    throwError
      "automation-first export: duplicate transition profile id {duplicate}"
  let familyIds := Canonical.transitionFamilies.map (·.familyId)
  if let some duplicate := duplicate? familyIds then
    throwError
      "automation-first export: duplicate transition family id {duplicate}"
  for descriptor in Canonical.transitionProfiles do
    let profile := descriptor.contract
    unless residualIds.contains profile.sourceResidualKind do
      throwError
        "automation-first export: transition {profile.profileId} has unknown source residual"
    unless tacticIds.contains profile.sourceTacticId do
      throwError
        "automation-first export: transition {profile.profileId} has unknown source tactic"
    unless tacticIds.contains profile.targetTacticId do
      throwError
        "automation-first export: transition {profile.profileId} has unknown target tactic"
    unless descriptor.transitionDeclaration.toString ==
        profile.transitionConstructor do
      throwError
        "automation-first export: transition {profile.profileId} constructor metadata disagrees with registry"
    unless descriptor.advanceDeclaration.toString == profile.advanceExecutor do
      throwError
        "automation-first export: transition {profile.profileId} executor metadata disagrees with registry"
    let problemInputs := profile.problemSpecificInputs
    unless problemInputs.contains .targetCapability do
      throwError
        "automation-first export: transition {profile.profileId} lacks its target capability input"
    let problemInputKeys := problemInputs.map Core.TransitionProblemInput.key
    if let some duplicate := duplicate? problemInputKeys then
      throwError
        "automation-first export: transition {profile.profileId} duplicates problem input {duplicate}"
    match profile.semanticDiscovery with
    | .capabilityDiscovery =>
        if problemInputs.contains .semanticDiscoveryAdapter then
          throwError
            "automation-first export: capability transition {profile.profileId} lists an adapter input"
    | .problemSemanticAdapter adapterType =>
        if adapterType.isEmpty then
          throwError
            "automation-first export: transition {profile.profileId} has an empty adapter type"
        unless problemInputs.contains .semanticDiscoveryAdapter do
          throwError
            "automation-first export: adapter transition {profile.profileId} lacks its adapter input"
        unless env.find? (dottedName adapterType) |>.isSome do
          throwError
            "automation-first export: transition {profile.profileId} has unknown adapter type {adapterType}"
    let targetPrefix := s!"StructuralExhaustion.{profile.targetTacticId}."
    unless profile.targetExecutableInterface.startsWith targetPrefix &&
        profile.targetExecutableInterface.endsWith "executableInterface" do
      throwError
        "automation-first export: transition {profile.profileId} does not name its target CT executable interface"
    for reference in [profile.targetExecutableInterface,
        profile.transitionConstructor, profile.advanceExecutor] do
      unless env.find? (dottedName reference) |>.isSome do
        throwError
          "automation-first export: transition {profile.profileId} has unknown declaration {reference}"
  for family in Canonical.transitionFamilies do
    if family.profiles.isEmpty then
      throwError
        "automation-first export: transition family {family.familyId} has no profiles"
    for profile in family.profiles do
      unless profile.contract.sourceTacticId == family.sourceTacticId &&
          profile.contract.targetTacticId == family.targetTacticId do
        throwError
          "automation-first export: profile {profile.contract.profileId} is in the wrong transition family"

  let tactics ← Canonical.tactics.mapM (tacticJson env)
  let catalog := Json.mkObj [
    ("artifactType", toJson "automationFirstLeanCatalog"),
    ("schemaVersion", toJson "9.0.0"),
    ("sourceOfTruth", Json.mkObj [
      ("kind", toJson "compiledLeanEnvironment"),
      ("rootModule", toJson "StructuralExhaustion"),
      ("registry", toJson "StructuralExhaustion.Canonical.tactics")
    ]),
    ("provisionTaxonomy", Json.arr
      (Core.Provision.all.map fun provision => toJson provision.key).toArray),
    ("tactics", Json.arr tactics),
    ("transitionFamilies", Json.arr
      (Canonical.transitionFamilies.map transitionFamilyJson).toArray),
    ("transitionProfiles", Json.arr
      (Canonical.transitionProfiles.map fun profile =>
        transitionProfileJson profile.contract).toArray)
  ]
  let output := (← IO.getEnv "STRUCTURAL_EXHAUSTION_EXPORT").getD
    "../generated/lean-machines.json"
  let outputPath := System.FilePath.mk output
  if let some parent := outputPath.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile outputPath (catalog.pretty 100 ++ "\n")
  logInfo m!"Exported automation-first Lean catalog to {output}"

private def audienceCopyJson
    (copy : Canonical.Documentation.AudienceCopy) : Json :=
  Json.mkObj [
    ("summary", toJson copy.summary),
    ("inputs", toJson copy.inputs),
    ("result", toJson copy.result)
  ]

private def exampleRefJson
    (reference : Canonical.Documentation.ExampleRef) : Json :=
  Json.mkObj [
    ("exampleId", toJson reference.exampleId),
    ("workflowId", toJson reference.workflowId),
    ("title", toJson reference.title)
  ]

private def capabilityDocumentationJson
    (descriptor : Canonical.Documentation.CapabilityDescriptor) : Json :=
  Json.mkObj [
    ("capabilityId", toJson descriptor.capabilityId),
    ("layer", toJson descriptor.layer.key),
    ("category", toJson descriptor.category),
    ("title", toJson descriptor.title),
    ("depth", toJson descriptor.depth.key),
    ("mathematician", audienceCopyJson descriptor.mathematician),
    ("leanUser", audienceCopyJson descriptor.leanUser),
    ("declarations", toJson (descriptor.declarations.map Name.toString)),
    ("relatedTacticIds", toJson descriptor.relatedTacticIds),
    ("relatedCapabilityIds", toJson descriptor.relatedCapabilityIds),
    ("examples", Json.arr (descriptor.examples.map exampleRefJson).toArray)
  ]

private def tacticGuideJson
    (guide : Canonical.Documentation.TacticGuide) : Json :=
  Json.mkObj [
    ("tacticId", toJson guide.tacticId),
    ("role", toJson guide.role),
    ("useWhen", toJson guide.useWhen),
    ("leanEntry", toJson guide.leanEntry)
  ]

private def exportDocumentation : CommandElabM Unit := do
  let env ← getEnv
  let capabilityIds := Canonical.Documentation.capabilities.map (·.capabilityId)
  if let some duplicate := duplicate? capabilityIds then
    throwError "framework documentation export: duplicate capability id {duplicate}"
  let tacticIds := Canonical.tactics.toList.map (·.tacticId)
  let guideIds := Canonical.Documentation.tacticGuides.map (·.tacticId)
  if let some duplicate := duplicate? guideIds then
    throwError "framework documentation export: duplicate tactic guide {duplicate}"
  unless guideIds.length == tacticIds.length &&
      tacticIds.all (fun tacticId => guideIds.contains tacticId) do
    throwError "framework documentation export: tactic guides do not cover the compiled CT registry"
  for descriptor in Canonical.Documentation.capabilities do
    if descriptor.capabilityId.isEmpty || descriptor.category.isEmpty ||
        descriptor.title.isEmpty then
      throwError "framework documentation export: incomplete capability descriptor"
    if descriptor.mathematician.summary.isEmpty ||
        descriptor.mathematician.inputs.isEmpty ||
        descriptor.mathematician.result.isEmpty ||
        descriptor.leanUser.summary.isEmpty || descriptor.leanUser.inputs.isEmpty ||
        descriptor.leanUser.result.isEmpty then
      throwError
        "framework documentation export: {descriptor.capabilityId} lacks an audience presentation"
    if descriptor.declarations.isEmpty then
      throwError
        "framework documentation export: {descriptor.capabilityId} has no compiled declarations"
    for declaration in descriptor.declarations do
      unless env.find? declaration |>.isSome do
        throwError
          "framework documentation export: {descriptor.capabilityId} references unknown declaration {declaration}"
    for tacticId in descriptor.relatedTacticIds do
      unless tacticIds.contains tacticId do
        throwError
          "framework documentation export: {descriptor.capabilityId} references unknown tactic {tacticId}"
    for relatedId in descriptor.relatedCapabilityIds do
      unless capabilityIds.contains relatedId do
        throwError
          "framework documentation export: {descriptor.capabilityId} references unknown capability {relatedId}"
    for reference in descriptor.examples do
      if reference.exampleId.isEmpty || reference.workflowId.isEmpty || reference.title.isEmpty then
        throwError
          "framework documentation export: {descriptor.capabilityId} has an incomplete example reference"
  let documentation := Json.mkObj [
    ("artifactType", toJson "structuralExhaustionFrameworkDocumentation"),
    ("schemaVersion", toJson "1.0.0"),
    ("sourceOfTruth", Json.mkObj [
      ("kind", toJson "compiledLeanEnvironment"),
      ("registry", toJson "StructuralExhaustion.Canonical.Documentation.capabilities")
    ]),
    ("capabilities", Json.arr
      (Canonical.Documentation.capabilities.map capabilityDocumentationJson).toArray),
    ("tacticGuides", Json.arr
      (Canonical.Documentation.tacticGuides.map tacticGuideJson).toArray)
  ]
  let output := (← IO.getEnv "STRUCTURAL_EXHAUSTION_DOCUMENTATION_EXPORT").getD
    "../generated/framework-documentation.json"
  let outputPath := System.FilePath.mk output
  if let some parent := outputPath.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile outputPath (documentation.pretty 100 ++ "\n")
  logInfo m!"Exported framework documentation to {output}"

run_cmd exportCatalog
run_cmd exportDocumentation

end StructuralExhaustion.Canonical.Export
