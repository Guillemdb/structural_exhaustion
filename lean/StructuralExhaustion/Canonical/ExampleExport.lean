import StructuralExhaustion.Canonical.ExampleRegistry
import StructuralExhaustion.Canonical.Registry
import Lean

open Lean Meta Elab Command

namespace StructuralExhaustion.Canonical.ExampleExport

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def declarationType (info : ConstantInfo) : CommandElabM String :=
  liftTermElabM do pure (toString (← ppExpr info.type))

private def sourcePath (moduleName : Name) : String :=
  String.intercalate "/" (moduleName.toString.splitOn ".") ++ ".lean"

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

private def declarationJson
    (env : Environment) (name : Name) : CommandElabM Json := do
  let some info := env.find? name
    | throwError "example export: missing declaration {name}"
  let some moduleIdx := env.getModuleIdxFor? name
    | throwError "example export: declaration {name} is not imported from a source module"
  let moduleName := env.header.moduleNames[moduleIdx.toNat]!
  let some ranges ← findDeclarationRanges? name
    | throwError "example export: declaration {name} has no compiled source range"
  pure <| Json.mkObj [
    ("name", toJson name.toString),
    ("kind", toJson (declarationKind info)),
    ("type", toJson (← declarationType info)),
    ("module", toJson moduleName.toString),
    ("sourceFile", toJson (sourcePath moduleName)),
    ("range", rangeJson ranges.range),
    ("selectionRange", rangeJson ranges.selectionRange)
  ]

private def declarationsJson
    (env : Environment) (names : List Name) : CommandElabM Json := do
  pure <| Json.arr (← names.mapM (declarationJson env)).toArray

private def duplicate? (values : List String) : Option String :=
  match values with
  | [] => none
  | value :: rest =>
      if rest.contains value then some value else duplicate? rest

private def ensureNonempty (field value : String) : CommandElabM Unit := do
  if value.isEmpty then
    throwError "example export: {field} must not be empty"

private def tacticIds : List String :=
  Canonical.tactics.toList.map (·.tacticId)

private def findRoute? (routeId : String) : Option Core.RouteContract :=
  Canonical.routes.find? fun route => route.routeId == routeId

private def sourceTacticId (route : Core.RouteContract) : String :=
  route.sourceResidualKind.splitOn "." |>.head?.getD ""

private def findStage?
    (workflow : ExampleWorkflowDescriptor) (stageId : String) :
    Option ExampleStageDescriptor :=
  workflow.stages.find? fun stage => stage.stageId == stageId

private def validateDeclaration (env : Environment) (name : Name) : CommandElabM Unit := do
  let _ ← declarationJson env name

private def validateStage
    (env : Environment) (stage : ExampleStageDescriptor) : CommandElabM Unit := do
  ensureNonempty "stageId" stage.stageId
  ensureNonempty s!"stage {stage.stageId} title" stage.title
  ensureNonempty s!"stage {stage.stageId} summary" stage.summary
  match stage.tacticId? with
  | none =>
      if stage.kind == .tactic then
        throwError "example export: tactic stage {stage.stageId} has no tacticId"
  | some tacticId =>
      unless tacticIds.contains tacticId do
        throwError "example export: stage {stage.stageId} references unknown tactic {tacticId}"
  validateDeclaration env stage.primaryDeclaration
  for declaration in stage.evidenceDeclarations do
    validateDeclaration env declaration

private def validateLink
    (env : Environment) (workflow : ExampleWorkflowDescriptor)
    (link : ExampleLinkDescriptor) : CommandElabM Unit := do
  ensureNonempty "linkId" link.linkId
  ensureNonempty s!"link {link.linkId} label" link.label
  ensureNonempty s!"link {link.linkId} description" link.description
  let some source := findStage? workflow link.sourceStageId
    | throwError
        "example export: link {link.linkId} has unknown source stage {link.sourceStageId}"
  let some target := findStage? workflow link.targetStageId
    | throwError
        "example export: link {link.linkId} has unknown target stage {link.targetStageId}"
  match link.kind, link.routeId? with
  | .registeredRoute, some routeId =>
      let some route := findRoute? routeId
        | throwError "example export: link {link.linkId} references unknown route {routeId}"
      unless source.tacticId? == some (sourceTacticId route) do
        throwError
          "example export: route {routeId} source does not match stage {source.stageId}"
      unless target.tacticId? == some route.targetTacticId do
        throwError
          "example export: route {routeId} target does not match stage {target.stageId}"
  | .registeredRoute, none =>
      throwError "example export: registered route link {link.linkId} has no routeId"
  | _, some routeId =>
      throwError
        "example export: non-route link {link.linkId} unexpectedly names route {routeId}"
  | _, none => pure ()
  for declaration in link.evidenceDeclarations do
    validateDeclaration env declaration

private def validateWorkflow
    (env : Environment) (workflow : ExampleWorkflowDescriptor) : CommandElabM Unit := do
  ensureNonempty "workflowId" workflow.workflowId
  ensureNonempty s!"workflow {workflow.workflowId} title" workflow.title
  ensureNonempty s!"workflow {workflow.workflowId} purpose" workflow.purpose
  if workflow.stages.isEmpty then
    throwError "example export: workflow {workflow.workflowId} has no stages"
  if let some duplicate := duplicate? (workflow.stages.map (·.stageId)) then
    throwError
      "example export: workflow {workflow.workflowId} duplicates stage id {duplicate}"
  if let some duplicate := duplicate? (workflow.links.map (·.linkId)) then
    throwError
      "example export: workflow {workflow.workflowId} duplicates link id {duplicate}"
  for stage in workflow.stages do validateStage env stage
  for link in workflow.links do validateLink env workflow link

private def allStages (description : ExampleDescriptor) : List ExampleStageDescriptor :=
  description.workflows.flatMap (·.stages)

private def allLinks (description : ExampleDescriptor) : List ExampleLinkDescriptor :=
  description.workflows.flatMap (·.links)

private def findExampleStage?
    (description : ExampleDescriptor) (stageId : String) : Option ExampleStageDescriptor :=
  (allStages description).find? fun stage => stage.stageId == stageId

private def validateBinding
    (env : Environment) (description : ExampleDescriptor)
    (binding : ExampleInterfaceBinding) : CommandElabM Unit := do
  ensureNonempty "bindingId" binding.bindingId
  ensureNonempty s!"binding {binding.bindingId} role" binding.role
  ensureNonempty s!"binding {binding.bindingId} description" binding.description
  unless tacticIds.contains binding.tacticId do
    throwError
      "example export: binding {binding.bindingId} references unknown tactic {binding.tacticId}"
  let some stage := findExampleStage? description binding.stageId
    | throwError
        "example export: binding {binding.bindingId} has unknown stage {binding.stageId}"
  unless stage.tacticId? == some binding.tacticId do
    throwError
      "example export: binding {binding.bindingId} tactic does not match stage {stage.stageId}"
  validateDeclaration env binding.problemDeclaration
  validateDeclaration env binding.frameworkDeclaration

private def validateExample
    (env : Environment) (description : ExampleDescriptor) : CommandElabM Unit := do
  ensureNonempty "exampleId" description.exampleId
  ensureNonempty "example title" description.title
  ensureNonempty "example summary" description.summary
  if description.workflows.isEmpty then
    throwError "example export: example {description.exampleId} has no workflows"
  if let some duplicate := duplicate? (description.workflows.map (·.workflowId)) then
    throwError "example export: duplicate workflow id {duplicate}"
  if let some duplicate := duplicate? ((allStages description).map (·.stageId)) then
    throwError "example export: duplicate example-wide stage id {duplicate}"
  if let some duplicate := duplicate? ((allLinks description).map (·.linkId)) then
    throwError "example export: duplicate example-wide link id {duplicate}"
  if let some duplicate := duplicate? (description.interfaceBindings.map (·.bindingId)) then
    throwError "example export: duplicate interface binding id {duplicate}"
  if description.proofStatus == .complete &&
      description.workflows.any fun workflow => workflow.completion == .partialProof then
    throwError
      "example export: complete example {description.exampleId} contains a partial workflow"
  for workflow in description.workflows do validateWorkflow env workflow
  for binding in description.interfaceBindings do validateBinding env description binding

private def stageJson
    (env : Environment) (stage : ExampleStageDescriptor) : CommandElabM Json := do
  pure <| Json.mkObj [
    ("stageId", toJson stage.stageId),
    ("title", toJson stage.title),
    ("summary", toJson stage.summary),
    ("kind", toJson stage.kind.key),
    ("tacticId", match stage.tacticId? with
      | none => Json.null
      | some tacticId => toJson tacticId),
    ("primaryDeclaration", ← declarationJson env stage.primaryDeclaration),
    ("evidenceDeclarations", ← declarationsJson env stage.evidenceDeclarations)
  ]

private def linkJson
    (env : Environment) (link : ExampleLinkDescriptor) : CommandElabM Json := do
  pure <| Json.mkObj [
    ("linkId", toJson link.linkId),
    ("sourceStageId", toJson link.sourceStageId),
    ("targetStageId", toJson link.targetStageId),
    ("kind", toJson link.kind.key),
    ("label", toJson link.label),
    ("description", toJson link.description),
    ("routeId", match link.routeId? with
      | none => Json.null
      | some routeId => toJson routeId),
    ("evidenceDeclarations", ← declarationsJson env link.evidenceDeclarations)
  ]

private def workflowJson
    (env : Environment) (workflow : ExampleWorkflowDescriptor) : CommandElabM Json := do
  pure <| Json.mkObj [
    ("workflowId", toJson workflow.workflowId),
    ("title", toJson workflow.title),
    ("purpose", toJson workflow.purpose),
    ("completion", toJson workflow.completion.key),
    ("stages", Json.arr (← workflow.stages.mapM (stageJson env)).toArray),
    ("links", Json.arr (← workflow.links.mapM (linkJson env)).toArray)
  ]

private def bindingJson
    (env : Environment) (binding : ExampleInterfaceBinding) : CommandElabM Json := do
  pure <| Json.mkObj [
    ("bindingId", toJson binding.bindingId),
    ("stageId", toJson binding.stageId),
    ("tacticId", toJson binding.tacticId),
    ("role", toJson binding.role),
    ("description", toJson binding.description),
    ("problemDeclaration", ← declarationJson env binding.problemDeclaration),
    ("frameworkDeclaration", ← declarationJson env binding.frameworkDeclaration)
  ]

/-- Validate and export one package-local example descriptor as raw JSON. -/
def exportExample
    (rootModule descriptorDeclaration : Name)
    (description : ExampleDescriptor) : CommandElabM Unit := do
  let env ← getEnv
  unless env.getModuleIdx? rootModule |>.isSome do
    throwError "example export: root module {rootModule} is not imported"
  unless env.find? descriptorDeclaration |>.isSome do
    throwError
      "example export: descriptor declaration {descriptorDeclaration} is missing"
  validateExample env description
  let catalog := Json.mkObj [
    ("artifactType", toJson "structuralExhaustionExample"),
    ("schemaVersion", toJson "1.0.0"),
    ("sourceOfTruth", Json.mkObj [
      ("kind", toJson "compiledLeanEnvironment"),
      ("rootModule", toJson rootModule.toString),
      ("descriptor", toJson descriptorDeclaration.toString)
    ]),
    ("example", Json.mkObj [
      ("exampleId", toJson description.exampleId),
      ("title", toJson description.title),
      ("summary", toJson description.summary),
      ("proofStatus", toJson description.proofStatus.key),
      ("workflows", Json.arr (← description.workflows.mapM (workflowJson env)).toArray),
      ("interfaceBindings", Json.arr
        (← description.interfaceBindings.mapM (bindingJson env)).toArray)
    ])
  ]
  let output := (← IO.getEnv "STRUCTURAL_EXHAUSTION_EXAMPLE_EXPORT").getD
    s!"../generated/examples/{description.exampleId}.raw.json"
  let outputPath := System.FilePath.mk output
  if let some parent := outputPath.parent then IO.FS.createDirAll parent
  IO.FS.writeFile outputPath (catalog.pretty 100 ++ "\n")
  logInfo m!"Exported Lean example {description.exampleId} to {output}"

end StructuralExhaustion.Canonical.ExampleExport
