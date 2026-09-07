import Lean
import Lean.Util.CollectAxioms
import Lean.Util.Sorry

set_option autoImplicit false

/-!
Portable pre-submission inventory. This is an external audit program, not a proof module.
It imports the manifest roots at private level and selects declarations by their origin module,
including private and generated declarations. It does not recheck the kernel.
The only allowed transitive axioms are propext, Classical.choice, and Quot.sound.
-/

open Lean

namespace SubmissionInventory

private def fromExcept {α : Type} (label : String) (x : Except String α) : IO α :=
  match x with
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{label}: {e}")

private def canonicalName (label spelling : String) : IO Name := do
  let some name := Syntax.decodeNameLit ("`" ++ spelling)
    | throw (IO.userError s!"Invalid {label}: {spelling}")
  unless name.toString == spelling do
    throw (IO.userError s!"Non-roundtripping {label}: {spelling}")
  return name

private def strField (j : Json) (key : String) : Except String String :=
  j.getObjVal? key >>= Json.getStr?

private def jsonStrings (xs : Array String) : Json :=
  Json.arr (xs.map Json.str)

private def sortedStrings (xs : Array String) : Array String :=
  xs.qsort (fun a b => compare a b == .lt)

private def countJson (m : Std.HashMap String Nat) : Json :=
  Json.mkObj <| (m.toArray.qsort (fun a b => compare a.1 b.1 == .lt)).toList.map
    (fun (k, v) => (k, Lean.toJson v))

private def bump (m : Std.HashMap String Nat) (k : String) : Std.HashMap String Nat :=
  m.insert k (m[k]?.getD 0 + 1)

private structure Inputs where
  roots : Array Name := #[]
  primary : Std.HashMap Name String := {}
  repaired : Std.HashSet Name := {}
  paths : Std.HashMap Name String := {}
  ownerModuleCounts : Std.HashMap String Nat := {}
  manifestPath : String

private def readInputs (manifestPath : String) : IO Inputs := do
  let manifest ← fromExcept "manifest JSON" (Json.parse (← IO.FS.readFile manifestPath))
  let rootRows ← fromExcept "roots" (manifest.getObjVal? "roots" >>= Json.getArr?)
  let moduleRows ← fromExcept "moduleRows" (manifest.getObjVal? "moduleRows" >>= Json.getObj?)
  let moduleRows := moduleRows.toList
  let mut inputs : Inputs := { manifestPath }
  let mut seenRoots : Std.HashSet Name := {}
  for row in rootRows do
    let spelling ← fromExcept "root module" row.getStr?
    let name ← canonicalName "root module" spelling
    if seenRoots.contains name then
      throw (IO.userError s!"Duplicate root module: {name}")
    seenRoots := seenRoots.insert name
    inputs := { inputs with roots := inputs.roots.push name }
  if inputs.roots.isEmpty then
    throw (IO.userError "The roots array must not be empty.")
  for (spelling, row) in moduleRows do
    let name ← canonicalName "primary module" spelling
    let owner ← fromExcept s!"owner of {spelling}" (strField row "owner")
    -- Owner names become selector basenames: keep them portable and prevent output collisions.
    unless !owner.isEmpty &&
        owner.toList.all (fun c => c.isAlphanum || c == '_' || c == '-' || c == '.') &&
        owner != "." && owner != ".." &&
        !(#["all-selected", "primary", "repaired", "repaired-outside-primary"]).contains owner do
      throw (IO.userError s!"Invalid or reserved owner label: {owner}")
    let path ← fromExcept s!"path of {spelling}" (strField row "path")
    unless path.endsWith ".lean" do
      throw (IO.userError s!"Expected a Lean source path for {spelling}: {path}")
    if inputs.primary.contains name then
      throw (IO.userError s!"Duplicate primary module: {name}")
    inputs := { inputs with
      primary := inputs.primary.insert name owner
      paths := inputs.paths.insert name path
      ownerModuleCounts := bump inputs.ownerModuleCounts owner }
  if inputs.primary.isEmpty then
    throw (IO.userError "moduleRows must not be empty; no whole-environment fallback is allowed.")
  unless inputs.primary.size == moduleRows.length do
    throw (IO.userError "Primary module cardinality differs from the manifest rows.")
  let repairRows ← match manifest.getObjVal? "repairedModules" with
    | .error _ => pure #[]
    | .ok value => fromExcept "repairedModules" value.getArr?
  for row in repairRows do
    let spelling ← fromExcept "repaired module" row.getStr?
    let name ← canonicalName "repaired module" spelling
    if inputs.repaired.contains name then
      throw (IO.userError s!"Duplicate repaired module: {name}")
    inputs := { inputs with repaired := inputs.repaired.insert name }
  return inputs

private def constantKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotientPrimitive"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def allowedAxiom (name : Name) : Bool :=
  name == ``propext || name == ``Classical.choice || name == ``Quot.sound

private def axiomClass (name : Name) : String :=
  if allowedAxiom name then "allowed"
  else if name == ``sorryAx then "sorry"
  else if name.toString == "Lean.trustCompiler" ||
      name.toString == "Lean.ofReduceBool" || name.toString == "Lean.ofReduceNat" then
    "nonstandardCompilerTrust"
  else "nonstandardOther"

/-- Preserve the raw str/num distinction as well as the human-readable declaration name. -/
private def nameParts : Name → List Json
  | .anonymous => []
  | .str parent s => nameParts parent ++ [Json.mkObj [("str", Json.str s)]]
  | .num parent n => nameParts parent ++ [Json.mkObj [("num", Lean.toJson n)]]

private structure Finding where
  name : Name
  nameRoundTrip : Bool
  origin : Name
  owner? : Option String
  repaired : Bool
  kind : String
  privateName : Bool
  unsafeDecl : Bool
  partialDecl : Bool
  typeHasSorry : Bool
  valueHasSorry : Bool
  syntheticSorry : Bool
  nonSyntheticSorry : Bool
  axioms : Array Name
  nonstandardAxioms : Array Name

private def Finding.isSafe (r : Finding) : Bool := !r.unsafeDecl && !r.partialDecl

private def Finding.hasTransitiveSorry (r : Finding) : Bool := r.axioms.contains ``sorryAx

private def Finding.hasDirectSorry (r : Finding) : Bool := r.typeHasSorry || r.valueHasSorry

private def Finding.toJson (r : Finding) : Json :=
  Json.mkObj [
    ("name", Json.str r.name.toString),
    ("nameParts", Json.arr (nameParts r.name).toArray),
    ("nameToStringRoundTrip", Json.bool r.nameRoundTrip),
    ("originModule", Json.str r.origin.toString),
    ("primaryOwner", r.owner?.map Json.str |>.getD Json.null),
    ("isPrimary", Json.bool r.owner?.isSome),
    ("isRepairedModule", Json.bool r.repaired),
    ("kind", Json.str r.kind),
    ("isPrivateName", Json.bool r.privateName),
    ("isUnsafe", Json.bool r.unsafeDecl),
    ("isPartial", Json.bool r.partialDecl),
    ("isSafeKernelRoot", Json.bool r.isSafe),
    ("typeHasSorry", Json.bool r.typeHasSorry),
    ("valueHasSorry", Json.bool r.valueHasSorry),
    ("hasSyntheticSorry", Json.bool r.syntheticSorry),
    ("hasNonSyntheticSorry", Json.bool r.nonSyntheticSorry),
    ("hasTransitiveSorry", Json.bool r.hasTransitiveSorry),
    ("axioms", Json.arr (r.axioms.map (fun n => Json.str n.toString))),
    ("nonstandardAxioms", Json.arr (r.nonstandardAxioms.map (fun n =>
      Json.mkObj [("name", Json.str n.toString), ("classification", Json.str (axiomClass n))])))]

private structure Stats where
  names : Array String := #[]
  safeNames : Array String := #[]
  unsafeNames : Array String := #[]
  partialNames : Array String := #[]
  nameRoundTripFailures : Array String := #[]
  privateCount : Nat := 0
  directSorryCount : Nat := 0
  transitiveSorryCount : Nat := 0
  nonstandardCount : Nat := 0
  safeNonstandardCount : Nat := 0
  kinds : Std.HashMap String Nat := {}
  axiomDependencies : Std.HashMap String Nat := {}
  nonstandardDependencies : Std.HashMap String Nat := {}
  deriving Inhabited

private def Stats.add (s : Stats) (r : Finding) : Stats := Id.run do
  let mut s := { s with
    names := s.names.push r.name.toString
    kinds := bump s.kinds r.kind
    privateCount := s.privateCount + if r.privateName then 1 else 0
    directSorryCount := s.directSorryCount + if r.hasDirectSorry then 1 else 0
    transitiveSorryCount := s.transitiveSorryCount + if r.hasTransitiveSorry then 1 else 0
    nonstandardCount := s.nonstandardCount + if r.nonstandardAxioms.isEmpty then 0 else 1
    safeNonstandardCount := s.safeNonstandardCount +
      if r.isSafe && !r.nonstandardAxioms.isEmpty then 1 else 0 }
  if !r.nameRoundTrip then
    s := { s with nameRoundTripFailures := s.nameRoundTripFailures.push r.name.toString }
  if r.isSafe then s := { s with safeNames := s.safeNames.push r.name.toString }
  if r.unsafeDecl then s := { s with unsafeNames := s.unsafeNames.push r.name.toString }
  if r.partialDecl then s := { s with partialNames := s.partialNames.push r.name.toString }
  for a in r.axioms do
    s := { s with axiomDependencies := bump s.axiomDependencies a.toString }
  for a in r.nonstandardAxioms do
    s := { s with nonstandardDependencies := bump s.nonstandardDependencies a.toString }
  return s

private def Stats.toJson (s : Stats) : Json :=
  Json.mkObj [
    ("declarations", Lean.toJson s.names.size), ("privateDeclarations", Lean.toJson s.privateCount),
    ("nameToStringRoundTripFailures", jsonStrings s.nameRoundTripFailures),
    ("safeDeclarations", Lean.toJson s.safeNames.size),
    ("unsafeDeclarations", Lean.toJson s.unsafeNames.size),
    ("partialDeclarations", Lean.toJson s.partialNames.size),
    ("declarationKinds", countJson s.kinds),
    ("directSorryDeclarations", Lean.toJson s.directSorryCount),
    ("transitiveSorryDeclarations", Lean.toJson s.transitiveSorryCount),
    ("nonstandardAxiomDeclarations", Lean.toJson s.nonstandardCount),
    ("safeNonstandardAxiomDeclarations", Lean.toJson s.safeNonstandardCount),
    ("axiomDependencyRootCounts", countJson s.axiomDependencies),
    ("nonstandardAxiomDependencyRootCounts", countJson s.nonstandardDependencies)]

private def writeNames (base : System.FilePath) (names : Array String) : IO Unit := do
  IO.FS.writeFile (base.toString ++ ".json") (jsonStrings names).pretty
  IO.FS.writeFile (base.toString ++ ".txt")
    (if names.isEmpty then "" else String.intercalate "\n" names.toList ++ "\n")

private def writeSelectors (dir : System.FilePath) (label : String) (s : Stats) : IO Unit := do
  writeNames (dir / s!"{label}.all") s.names
  writeNames (dir / s!"{label}.safe") s.safeNames
  writeNames (dir / s!"{label}.unsafe") s.unsafeNames
  writeNames (dir / s!"{label}.partial") s.partialNames

private def originOf (env : Environment) (name : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? name
  env.header.moduleNames[idx.toNat]?

private structure AuditResult where
  allSelected : Stats := {}
  primary : Stats := {}
  repaired : Stats := {}
  repairedOnly : Stats := {}
  owners : Std.HashMap String Stats := {}
  moduleCounts : Std.HashMap String Nat := {}

private def audit (inputs : Inputs) (outputDir : System.FilePath) : CoreM AuditResult := do
  let env ← getEnv
  let selected := env.constants.fold (init := (#[] : Array (Name × ConstantInfo × Name)))
    fun acc name info =>
      match originOf env name with
      | some origin =>
        if inputs.primary.contains origin || inputs.repaired.contains origin then
          acc.push (name, info, origin)
        else acc
      | none => acc
  let selected := selected.qsort (fun a b => compare a.1.toString b.1.toString == .lt)
  liftM <| IO.eprintln s!"Selected {selected.size} declarations; collecting axioms once per root."
  let out ← liftM <| IO.FS.Handle.mk (outputDir / "declarations.jsonl") .write
  let findingsOut ← liftM <| IO.FS.Handle.mk (outputDir / "exceptional-declarations.jsonl") .write
  let mut result : AuditResult := {}
  let mut processed : Nat := 0
  for (name, info, origin) in selected do
    -- Lean 4.33's public API consults imported precomputed axiom dependencies before recursing.
    -- Reuse this single result for the primary, owner, and repaired-subset counters.
    let axioms ← Lean.collectAxioms name
    let value := info.value? (allowOpaque := true)
    let typeHasSorry := info.type.hasSorry
    let valueHasSorry := value.any Expr.hasSorry
    let directSorry := typeHasSorry || valueHasSorry
    let finding : Finding := {
      name, origin
      nameRoundTrip := Syntax.decodeNameLit ("`" ++ name.toString) == some name
      owner? := inputs.primary[origin]?
      repaired := inputs.repaired.contains origin
      kind := constantKind info
      privateName := Lean.isPrivateName name
      unsafeDecl := info.isUnsafe
      partialDecl := info.isPartial
      typeHasSorry, valueHasSorry
      syntheticSorry := directSorry &&
        (info.type.hasSyntheticSorry || value.any Expr.hasSyntheticSorry)
      nonSyntheticSorry := directSorry &&
        (info.type.hasNonSyntheticSorry || value.any Expr.hasNonSyntheticSorry)
      axioms := axioms.qsort Name.lt
      nonstandardAxioms := axioms.filter (fun n => !allowedAxiom n) }
    liftM <| out.putStrLn finding.toJson.compress
    if !finding.nameRoundTrip || finding.hasDirectSorry || finding.hasTransitiveSorry ||
        !finding.nonstandardAxioms.isEmpty then
      liftM <| findingsOut.putStrLn finding.toJson.compress
    result := { result with
      allSelected := result.allSelected.add finding
      moduleCounts := bump result.moduleCounts origin.toString }
    if let some owner := finding.owner? then
      result := { result with
        primary := result.primary.add finding
        owners := result.owners.insert owner ((result.owners[owner]?.getD {}).add finding) }
    if finding.repaired then
      result := { result with repaired := result.repaired.add finding }
      if finding.owner?.isNone then
        result := { result with repairedOnly := result.repairedOnly.add finding }
    processed := processed + 1
    if processed % 1000 == 0 then
      liftM <| IO.eprintln s!"Inventory progress {processed}/{selected.size}"
  liftM out.flush
  liftM findingsOut.flush
  return result

private def writeResults (inputs : Inputs) (env : Environment)
    (outDir : System.FilePath) (result : AuditResult) : IO UInt32 := do
  let selectorDir := outDir / "selectors"
  IO.FS.createDirAll selectorDir
  writeSelectors selectorDir "all-selected" result.allSelected
  writeSelectors selectorDir "primary" result.primary
  writeSelectors selectorDir "repaired" result.repaired
  writeSelectors selectorDir "repaired-outside-primary" result.repairedOnly
  let loaded : Std.HashSet Name := env.header.moduleNames.foldl
    (fun acc name => acc.insert name) {}
  let requested := (inputs.primary.fold (init := inputs.repaired)
    (fun acc name _ => acc.insert name)).toArray.qsort Name.lt
  let expectedOwners := inputs.ownerModuleCounts.toArray.qsort
    (fun a b => compare a.1 b.1 == .lt)
  let mut modules : Array Json := #[]
  let mut missing : Array String := #[]
  let mut zeroDeclarations : Array String := #[]
  let mut loadedPrimaryCount : Nat := 0
  let mut loadedRepairedCount : Nat := 0
  let mut loadedOwnerCounts : Std.HashMap String Nat := {}
  for name in requested do
    let count := result.moduleCounts[name.toString]?.getD 0
    let isLoaded := loaded.contains name
    if !isLoaded then missing := missing.push name.toString
    if count == 0 then zeroDeclarations := zeroDeclarations.push name.toString
    if isLoaded then
      if let some owner := inputs.primary[name]? then
        loadedPrimaryCount := loadedPrimaryCount + 1
        loadedOwnerCounts := bump loadedOwnerCounts owner
      if inputs.repaired.contains name then
        loadedRepairedCount := loadedRepairedCount + 1
    modules := modules.push <| Json.mkObj [
      ("module", Json.str name.toString),
      ("path", inputs.paths[name]?.map Json.str |>.getD Json.null),
      ("isLoaded", Json.bool isLoaded),
      ("primaryOwner", inputs.primary[name]?.map Json.str |>.getD Json.null),
      ("isRepaired", Json.bool (inputs.repaired.contains name)),
      ("declarationCount", Lean.toJson count)]
  IO.FS.writeFile (outDir / "modules.json") (Json.arr modules).pretty
  let mut owners : List (String × Json) := []
  for (owner, expectedModules) in expectedOwners do
    let stats := result.owners[owner]?.getD {}
    let loadedModules := loadedOwnerCounts[owner]?.getD 0
    writeSelectors selectorDir owner stats
    owners := owners ++ [(owner, Json.mkObj [
      ("requestedModules", Lean.toJson expectedModules),
      ("loadedModules", Lean.toJson loadedModules),
      ("moduleCoverageExact", Json.bool (loadedModules == expectedModules)),
      ("statistics", stats.toJson)])]
  let missingRoots := inputs.roots.filter (fun name => !loaded.contains name)
  let moduleCoverageExact := missing.isEmpty && missingRoots.isEmpty &&
    loadedPrimaryCount == inputs.primary.size && loadedRepairedCount == inputs.repaired.size &&
    expectedOwners.all (fun p => loadedOwnerCounts[p.1]?.getD 0 == p.2)
  let passed := moduleCoverageExact && !result.primary.names.isEmpty &&
    result.allSelected.nameRoundTripFailures.isEmpty &&
    result.allSelected.directSorryCount == 0 &&
    result.allSelected.transitiveSorryCount == 0 && result.allSelected.nonstandardCount == 0
  let summary := Json.mkObj [
    ("schemaVersion", Lean.toJson (1 : Nat)),
    ("tool", Json.str "Lean 4.33 portable public-API declaration inventory"),
    ("auditPassed", Json.bool passed),
    ("kernelRecheckPerformed", Json.bool false),
    ("independentKernelCheckPerformed", Json.bool false),
    ("inputModuleManifest", Json.str inputs.manifestPath),
    ("importLevel", Json.str "private"), ("importTrustLevel", Lean.toJson (0 : Nat)),
    ("importRoots", jsonStrings (inputs.roots.map (fun name => name.toString))),
    ("selectionMethod", Json.str "origin module via getModuleIdxFor?; no declaration-name prefix filtering"),
    ("primaryModuleCount", Lean.toJson inputs.primary.size),
    ("loadedPrimaryModuleCount", Lean.toJson loadedPrimaryCount),
    ("repairedModuleCount", Lean.toJson inputs.repaired.size),
    ("loadedRepairedModuleCount", Lean.toJson loadedRepairedCount),
    ("importedModuleCount", Lean.toJson env.header.moduleNames.size),
    ("moduleCoverageExact", Json.bool moduleCoverageExact),
    ("missingRequestedModules", jsonStrings (sortedStrings missing)),
    ("missingRootModules", jsonStrings (missingRoots.map (fun name => name.toString))),
    ("zeroDeclarationModules", jsonStrings (sortedStrings zeroDeclarations)),
    ("zeroDeclarationModulesNote", Json.str "Aggregates may legitimately introduce no declarations."),
    ("allowedAxioms", jsonStrings #["propext", "Classical.choice", "Quot.sound"]),
    ("allSelected", result.allSelected.toJson), ("primary", result.primary.toJson),
    ("owners", Json.mkObj owners), ("repairedSubset", result.repaired.toJson),
    ("repairedOutsidePrimary", result.repairedOnly.toJson),
    ("declarationInventory", Json.str "declarations.jsonl"),
    ("exceptionalDeclarations", Json.str "exceptional-declarations.jsonl"),
    ("moduleInventory", Json.str "modules.json"),
    ("selectorDirectory", Json.str "selectors"),
    ("nameRoundTripMethod", Json.str "Syntax.decodeNameLit (backtick ++ Name.toString) must equal the original Name; raw str/num components are also included per declaration"),
    ("selectorSemantics", Json.str "all includes private/generated/unsafe/partial; safe excludes unsafe and partial; neither selector grants permission to nonstandard axioms"),
    ("axiomCollectionMethod", Json.str "Lean.collectAxioms once per selected declaration; Lean 4.33 imported precomputed dependencies avoid repeated closure walks; private roots may use its fallback traversal"),
    ("sorryMethod", Json.str "Expr.hasSorry plus synthetic/non-synthetic checks on types and all available definition/theorem/opaque bodies, and transitive sorryAx via collectAxioms"),
    ("safetyNote", Json.str "unsafe and partial are separately inventoried; no axiom beyond the three-item allowlist is silently accepted")]
  IO.FS.writeFile (outDir / "summary.json") summary.pretty
  IO.println summary.compress
  return if passed then 0 else 1

unsafe def run (manifestPath outputPath : String) : IO UInt32 := do
  let inputs ← readInputs manifestPath
  let outputDir : System.FilePath := outputPath
  IO.FS.createDirAll outputDir
  Lean.initSearchPath (← Lean.findSysroot)
  -- Needed for imported collectAxioms caches; affects this audit process only.
  Lean.enableInitializersExecution
  IO.eprintln s!"Importing {inputs.roots.size} explicit roots at private level (trustLevel = 0)."
  let imports : Array Import := inputs.roots.map (fun name => { module := name })
  let env ← Lean.importModules imports {} (trustLevel := 0) (loadExts := true)
    (level := .private)
  let env := env.setExporting false
  let result ← Lean.Core.CoreM.toIO' (audit inputs outputDir)
    { fileName := "<submission-inventory>", fileMap := default } { env := env }
  writeResults inputs env outputDir result

end SubmissionInventory

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [manifestPath, outputPath] =>
    try
      SubmissionInventory.run manifestPath outputPath
    catch e =>
      IO.eprintln s!"Inventory failed: {e}"
      return 2
  | _ =>
    IO.eprintln "Usage: lake env lean --run Inventory.lean MODULE_MANIFEST_JSON OUTPUT_DIR"
    return 2
