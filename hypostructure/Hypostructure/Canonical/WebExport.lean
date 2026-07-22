import Hypostructure
import Hypostructure.PDE
import Hypostructure.PDE.NavierStokes
import Lean

/-!
# Hypostructure web declaration export

This build-time exporter is the compiled-environment boundary for the
documentation application.  It deliberately exports facts about Lean
declarations only.  Editorial copy, examples, and navigation are assembled by
the deterministic Python web-data build, while declaration names, types,
documentation strings, source locations, and dependency edges come from Lean.
-/

open Lean Meta Elab Command

namespace Hypostructure.Canonical.WebExport

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

private def projectName (name : Name) : Bool :=
  (`Hypostructure).isPrefixOf name

private def declarationModule?
    (env : Environment) (name : Name) : Option Name := do
  let moduleIdx ← env.getModuleIdxFor? name
  pure env.header.moduleNames[moduleIdx.toNat]!

private def exportedModule (moduleName : Name) : Bool :=
  let text := moduleName.toString
  text.startsWith "Hypostructure" &&
    !text.startsWith "Hypostructure.Fixtures" &&
    !text.startsWith "Hypostructure.Canonical"

private def layer (moduleName : Name) : String :=
  let text := moduleName.toString
  if text.startsWith "Hypostructure.Core" then "core"
  else if text.startsWith "Hypostructure.Routes" then "routes"
  else if text.startsWith "Hypostructure.Graph" then "graph"
  else if text.startsWith "Hypostructure.PDE" then "pde"
  else if text.startsWith "Hypostructure.CT" then "ct"
  else "framework"

private def routeOwner : Routes.Registry.Owner → String
  | .sourceRegistry => "framework"
  | .erdosGyarf64 => "erdos"
  | .pdeArchitecture => "pde"

private def routeKind : Routes.Registry.Kind → String
  | .specializedDiscovery => "specialized_discovery"
  | .genericAccumulated => "generic_accumulated"
  | .profileRequirement => "profile_requirement"
  | .familyRequirement => "family_requirement"

private def routeStatus : Routes.Registry.Status → String
  | .baseline => "baseline"
  | .planned => "planned"

private def routeJson (entry : Routes.Registry.Entry) : Json :=
  Json.mkObj [
    ("route_id", toJson entry.edgeKey),
    ("source_ct", toJson entry.source.key),
    ("target_ct", toJson entry.target.key),
    ("family_id", toJson entry.familyKey),
    ("profile_id", toJson entry.profileId),
    ("owner", toJson (routeOwner entry.owner)),
    ("kind", toJson (routeKind entry.kind)),
    ("catalog_status", toJson (routeStatus entry.status)),
    ("executable_evidence", Json.null)
  ]

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
    (env : Environment) (name moduleName : Name) : CommandElabM Json := do
  let some info := env.find? name
    | throwError "Hypostructure web export: missing declaration {name}"
  let typeDeps := typeDependencies info |>.filter fun dependency =>
    projectName dependency && dependency != name
  let bodyDeps := valueDependencies info |>.filter fun dependency =>
    projectName dependency && dependency != name && !typeDeps.contains dependency
  let ranges? ← findDeclarationRanges? name
  let rangeValue := match ranges? with
    | none => Json.null
    | some ranges => rangeJson ranges.range
  let selectionRangeValue := match ranges? with
    | none => Json.null
    | some ranges => rangeJson ranges.selectionRange
  let docValue := match ← findDocString? env name with
    | none => Json.null
    | some doc => toJson doc
  pure <| Json.mkObj [
    ("declaration_id", toJson name.toString),
    ("name", toJson name.toString),
    ("kind", toJson (declarationKind info)),
    ("type", toJson (← declarationType info)),
    ("doc_string", docValue),
    ("module", toJson moduleName.toString),
    ("source_file", toJson (sourcePath moduleName)),
    ("range", rangeValue),
    ("selection_range", selectionRangeValue),
    ("body_available", toJson (hasBody info)),
    ("type_dependencies", toJson (typeDeps.map (·.toString))),
    ("body_dependencies", toJson (bodyDeps.map (·.toString))),
    ("layer", toJson (layer moduleName))
  ]

private def exportCatalog : CommandElabM Unit := do
  let env ← getEnv
  let declarationsUnsorted : List (Name × Name) := env.constants.toList.filterMap fun (name, _) => do
      guard (projectName name)
      let moduleName ← declarationModule? env name
      guard (exportedModule moduleName)
      pure (name, moduleName)
  let declarations := declarationsUnsorted.mergeSort fun first second =>
    first.1.toString < second.1.toString
  let declarationValues ← declarations.mapM fun (name, moduleName) =>
    declarationJson env name moduleName
  let catalog := Json.mkObj [
    ("artifact_type", toJson "hypostructure_declaration_catalog"),
    ("schema_version", toJson "1.0.0"),
    ("framework", Json.mkObj [
      ("name", toJson "Hypostructure"),
      ("namespace", toJson "Hypostructure"),
      ("source_of_truth", toJson "compiled_lean_environment")
    ]),
    ("ct_catalog", Json.arr
      (Routes.Registry.ctIds.map fun id => toJson id.key).toArray),
    ("route_registry", Json.arr
      (Routes.Registry.all.map routeJson).toArray),
    ("declarations", Json.arr declarationValues.toArray)
  ]
  let output := (← IO.getEnv "HYPOSTRUCTURE_WEB_DECLARATIONS_EXPORT").getD
    "../generated/hypostructure/web/declarations.raw.json"
  let outputPath := System.FilePath.mk output
  if let some parent := outputPath.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile outputPath (catalog.pretty 100 ++ "\n")
  logInfo m!"Exported {declarationValues.length} Hypostructure declarations to {output}"

run_cmd exportCatalog

end Hypostructure.Canonical.WebExport
