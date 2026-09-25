/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Export

set_option autoImplicit false

open Lean

/-!
A file-fed entry point for the unchanged lean4export library.
Usage: ExportSelected.lean SELECTOR_TEXT MODULE [MODULE ...]
Only explicitly selected safe declarations are roots. Dependencies are handled by dumpConstant.
-/

private def canonicalName (label spelling : String) : IO Name := do
  let some name := Syntax.decodeNameLit ("`" ++ spelling)
    | throw (IO.userError s!"Invalid {label}: {spelling}")
  unless name.toString == spelling do
    throw (IO.userError s!"Non-roundtripping {label}: {spelling}")
  unless Syntax.decodeNameLit ("`" ++ name.toString) == some name do
    throw (IO.userError s!"Name roundtrip failed for {label}: {spelling}")
  return name

private def readSelectors (path : String) : IO (Array Name) := do
  let contents ← IO.FS.readFile path
  let lines := contents.splitOn "\n"
  let lineCount := lines.length
  let mut names : Array Name := #[]
  let mut seen : Std.HashSet Name := {}
  for (line, index) in lines.zipIdx do
    if line.isEmpty then
      -- Permit one terminal newline, but reject silently omitted interior entries.
      unless index + 1 == lineCount do
        throw (IO.userError s!"Blank selector at line {index + 1}")
    else
      let name ← canonicalName s!"selector at line {index + 1}" line
      if seen.contains name then
        throw (IO.userError s!"Duplicate selector at line {index + 1}: {name}")
      seen := seen.insert name
      names := names.push name
  if names.isEmpty then
    throw (IO.userError "Selector file is empty; exporting the whole environment is forbidden.")
  return names

private def exportSelected (selectorPath : String) (moduleSpellings : List String) : IO Unit := do
  if moduleSpellings.isEmpty then
    throw (IO.userError "At least one explicit import module is required.")
  let constants ← readSelectors selectorPath
  let imports ← moduleSpellings.toArray.mapM fun spelling => do
    let name ← canonicalName "import module" spelling
    pure ({ module := name } : Import)
  initSearchPath (← findSysroot)
  -- These are exactly the original Main's import defaults; no initializer execution is enabled.
  let env ← importModules imports {} (trustLevel := 0) (loadExts := false) (level := .private)
  for name in constants do
    let some info := env.find? name
      | throw (IO.userError s!"Selected declaration is absent from the imported environment: {name}")
    if info.isUnsafe || info.isPartial then
      throw (IO.userError s!"Selector is unsafe or partial, not a safe kernel root: {name}")
  IO.eprintln s!"Exporting {constants.size} explicit safe roots through unchanged lean4export."
  -- Preserve one shared exporter state, metadata, constants loop, and per-root mdata cache reset.
  M.run env do
    initState env []
    dumpMetadata
    for name in constants do
      modify (fun st => { st with noMDataExprs := {} })
      dumpConstant name

def main (args : List String) : IO UInt32 := do
  match args with
  | selectorPath :: moduleSpellings =>
    try
      exportSelected selectorPath moduleSpellings
      return 0
    catch e =>
      IO.eprintln s!"ExportSelected failed: {e}"
      return 2
  | [] =>
    IO.eprintln "Usage: lean --run ExportSelected.lean SELECTOR_TEXT MODULE [MODULE ...]"
    return 2
