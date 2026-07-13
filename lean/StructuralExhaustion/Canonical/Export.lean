import StructuralExhaustion
import StructuralExhaustion.Canonical.Registry
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

private def capabilityJson (contract : Core.CapabilityContract) : Json :=
  let requiredInstances := contract.requiredInstances.map fun reference =>
    Core.ProvisionedRef.mk reference .typeclassInferred
  let derivedOperations := contract.derivedOperations.map fun reference =>
    Core.ProvisionedRef.mk reference .frameworkConstant
  Json.mkObj [
    ("capabilityId", toJson contract.capabilityId),
    ("tacticId", toJson contract.tacticId),
    ("requiredDefinitions", provisionedRefsJson contract.requiredDefinitions),
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

private def routeSemanticDiscoveryJson
    (discovery : Core.RouteSemanticDiscovery) : Json :=
  Json.mkObj [
    ("kind", toJson discovery.key),
    ("adapterType", match discovery.adapterType? with
      | none => Json.null
      | some adapterType => toJson adapterType)
  ]

private def routeAuthoringBoundaryJson
    (contract : Core.RouteContract) : Json :=
  Json.mkObj [
    ("semanticDiscovery", routeSemanticDiscoveryJson contract.semanticDiscovery),
    ("problemSpecificInputs", stringListJson
      (contract.problemSpecificInputs.map Core.RouteProblemInput.key)),
    ("frameworkOwnedResponsibilities", stringListJson
      (Core.RouteFrameworkResponsibility.all.map
        Core.RouteFrameworkResponsibility.key))
  ]

private def routeJson (contract : Core.RouteContract) : Json :=
  Json.mkObj [
    ("routeId", toJson contract.routeId),
    ("sourceResidualKind", toJson contract.sourceResidualKind),
    ("targetTacticId", toJson contract.targetTacticId),
    ("discovery", toJson contract.discovery),
    ("triggerConstructor", toJson contract.triggerConstructor),
    ("soundnessTheorem", toJson contract.soundnessTheorem),
    ("contextPreservationTheorem", toJson contract.contextPreservationTheorem),
    ("provenanceTheorem", toJson contract.provenanceTheorem),
    ("selectionClass", toJson contract.selectionClass.key),
    ("authoringBoundary", routeAuthoringBoundaryJson contract)
  ]

private def dottedName (reference : String) : Name :=
  (reference.splitOn ".").foldl (fun name component => name.str component)
    .anonymous

private def sourcePath (namespaceName : Name) : String :=
  String.intercalate "/" (namespaceName.toString.splitOn ".") ++ ".lean"

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

private def terminalAutomationJson
    (tactic : TacticDescriptor) (code : String)
    (incoming : Array TransitionSnapshot) : Json :=
  let predecessor := incoming.toList.map fun edge =>
    Core.ProvisionedRef.mk edge.constructor.toString .derivedFromPredecessor
  let theoremName := tactic.namespaceName.toString ++ ".run_trace_valid"
  let theorems := [Core.ProvisionedRef.mk theoremName .derivedByGenericTheorem]
  let output := Core.ProvisionedRef.mk
    (tactic.namespaceName.toString ++ ".ExecutionResult@" ++ code) .generatedAudit
  Json.mkObj [
    ("executionClass", toJson Core.ExecutionClass.genericTheorem.key),
    ("authorInputs", Json.arr #[]),
    ("inferredInputs", Json.arr #[]),
    ("predecessorInputs", provisionedRefsJson predecessor),
    ("derivedInputs", Json.arr #[]),
    ("transitiveDependencies", provisionedRefsJson (predecessor ++ theorems)),
    ("frameworkTheorems", provisionedRefsJson theorems),
    ("generatedOutputs", provisionedRefsJson [output]),
    ("manualObligations", Json.arr #[])
  ]

private def tacticJson
    (env : Environment) (tactic : TacticDescriptor) : CommandElabM Json := do
  unless tactic.capabilityContract.tacticId == tactic.tacticId do
    throwError
      "automation-first export: {tactic.tacticId} capability has tacticId {tactic.capabilityContract.tacticId}"
  for profile in tactic.capabilityProfiles do
    unless profile.tacticId == tactic.tacticId do
      throwError
        "automation-first export: {profile.capabilityId} has tacticId {profile.tacticId}, expected {tactic.tacticId}"

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
    let automation ← match isTerminal, matchingContracts with
      | true, [] => pure (terminalAutomationJson tactic code incoming)
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
          pure (automationJson contract)
      | false, [] =>
          throwError "automation-first export: nonterminal {code} has no node contract"
      | false, _ =>
          throwError "automation-first export: nonterminal {code} has duplicate contracts"
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
      ("presentation", presentation)
    ]

  let nodeCodes ← nodeConstructors.mapM (nodeCode codeDeclaration)
  let nonterminalCodes := nodeCodes.toList.filter fun code =>
    !(terminalCodes.contains code)
  for contract in tactic.nodeAutomationContracts do
    unless nonterminalCodes.contains contract.nodeId do
      throwError
        "automation-first export: node contract {contract.nodeId} is not a nonterminal constructor"

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

  pure <| Json.mkObj [
    ("tacticId", toJson tactic.tacticId),
    ("title", toJson tactic.title),
    ("apiVersion", toJson tactic.apiVersion),
    ("namespace", toJson tactic.namespaceName.toString),
    ("capability", capabilityJson tactic.capabilityContract),
    ("capabilityProfiles", Json.arr
      (tactic.capabilityProfiles.map capabilityJson).toArray),
    ("nodes", Json.arr nodes),
    ("transitions", Json.arr (transitions.map TransitionSnapshot.json)),
    ("terminals", Json.arr (terminals.map TerminalSnapshot.json)),
    ("residualKinds", Json.arr
      (tactic.residualKindContracts.map residualKindJson).toArray),
    ("apiDeclarations", Json.arr apiDeclarations.toArray),
    ("loopDecrease", loopDecrease)
  ]

private def duplicate? (values : List String) : Option String :=
  match values with
  | [] => none
  | value :: rest =>
      if rest.contains value then some value else duplicate? rest

private def exportCatalog : CommandElabM Unit := do
  let env ← getEnv
  let tacticIds := Canonical.tactics.toList.map (·.tacticId)
  if let some duplicate := duplicate? tacticIds then
    throwError "automation-first export: duplicate tactic id {duplicate}"
  let residualIds := Canonical.tactics.toList.flatMap fun tactic =>
    tactic.residualKindContracts.map (·.residualKindId)
  if let some duplicate := duplicate? residualIds then
    throwError "automation-first export: duplicate residual id {duplicate}"
  let routeIds := Canonical.routes.map (·.routeId)
  if let some duplicate := duplicate? routeIds then
    throwError "automation-first export: duplicate route id {duplicate}"
  for route in Canonical.routes do
    unless residualIds.contains route.sourceResidualKind do
      throwError
        "automation-first export: route {route.routeId} has unknown source residual"
    unless tacticIds.contains route.targetTacticId do
      throwError
        "automation-first export: route {route.routeId} has unknown target tactic"
    let problemInputs := route.problemSpecificInputs
    unless problemInputs.contains .targetCapability do
      throwError
        "automation-first export: route {route.routeId} lacks its target capability input"
    let problemInputKeys := problemInputs.map Core.RouteProblemInput.key
    if let some duplicate := duplicate? problemInputKeys then
      throwError
        "automation-first export: route {route.routeId} duplicates problem input {duplicate}"
    match route.semanticDiscovery with
    | .capabilityDiscovery =>
        if problemInputs.contains .semanticDiscoveryAdapter then
          throwError
            "automation-first export: capability-discovery route {route.routeId} lists an adapter input"
        let expectedDiscovery :=
          s!"StructuralExhaustion.{route.targetTacticId}.Capability.discover"
        unless route.discovery == expectedDiscovery do
          throwError
            "automation-first export: capability-discovery route {route.routeId} must use {expectedDiscovery}"
    | .problemSemanticAdapter adapterType =>
        if adapterType.isEmpty then
          throwError
            "automation-first export: route {route.routeId} has an empty adapter type"
        unless problemInputs.contains .semanticDiscoveryAdapter do
          throwError
            "automation-first export: adapter route {route.routeId} lacks its adapter input"
        unless route.discovery == adapterType ++ ".discover" do
          throwError
            "automation-first export: route {route.routeId} discovery is not the adapter projection"
        unless env.find? (dottedName adapterType) |>.isSome do
          throwError
            "automation-first export: route {route.routeId} has unknown adapter type {adapterType}"
    for reference in [route.discovery, route.triggerConstructor,
        route.soundnessTheorem, route.contextPreservationTheorem,
        route.provenanceTheorem] do
      unless env.find? (dottedName reference) |>.isSome do
        throwError
          "automation-first export: route {route.routeId} has unknown declaration {reference}"

  let tactics ← Canonical.tactics.mapM (tacticJson env)
  let catalog := Json.mkObj [
    ("artifactType", toJson "automationFirstLeanCatalog"),
    ("schemaVersion", toJson "6.0.0"),
    ("sourceOfTruth", Json.mkObj [
      ("kind", toJson "compiledLeanEnvironment"),
      ("rootModule", toJson "StructuralExhaustion"),
      ("registry", toJson "StructuralExhaustion.Canonical.tactics")
    ]),
    ("provisionTaxonomy", Json.arr
      (Core.Provision.all.map fun provision => toJson provision.key).toArray),
    ("tactics", Json.arr tactics),
    ("routes", Json.arr (Canonical.routes.map routeJson).toArray)
  ]
  let output := (← IO.getEnv "STRUCTURAL_EXHAUSTION_EXPORT").getD
    "../generated/lean-machines.json"
  let outputPath := System.FilePath.mk output
  if let some parent := outputPath.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile outputPath (catalog.pretty 100 ++ "\n")
  logInfo m!"Exported automation-first Lean catalog to {output}"

run_cmd exportCatalog

end StructuralExhaustion.Canonical.Export
