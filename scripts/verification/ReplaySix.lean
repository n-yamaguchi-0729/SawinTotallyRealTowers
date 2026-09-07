import Lean
import Lean.Replay
import Lean.Util.FoldConsts

set_option autoImplicit false

open Lean

/-- Inventory is separate from the kernel-replay result: replay accepts axioms. -/
private def reportInventory (env : Environment) (roots : Array String) : IO Unit := do
  let constants := env.constants.map₁
  let mut unsafeCount := 0
  let mut partialCount := 0
  let mut axiomNames : Array String := #[]
  let mut directSorryUsers : Array String := #[]
  for (name, info) in constants do
    if info.isUnsafe then
      unsafeCount := unsafeCount + 1
    if info.isPartial then
      partialCount := partialCount + 1
    if let .axiomInfo _ := info then
      axiomNames := axiomNames.push name.toString
    if info.getUsedConstantsAsSet.contains "sorryAx".toName then
      directSorryUsers := directSorryUsers.push name.toString
  IO.println <| Json.compress <| Json.mkObj [
    ("phase", toJson "inventory"),
    ("roots", toJson roots),
    ("loaded_modules", toJson (env.header.moduleNames.map Name.toString)),
    ("constant_count", toJson constants.size),
    ("unsafe_skipped_count", toJson unsafeCount),
    ("partial_skipped_count", toJson partialCount),
    ("axiom_names", toJson axiomNames),
    ("direct_sorry_users", toJson directSorryUsers),
    ("axiom_policy_enforced", toJson false)
  ]
  (← IO.getStdout).flush

/--
Read existing oleans once at private level, then use the unchanged official
Lean 4.33 kernel replay in a fresh trust-level-zero environment.
No imported initializers or environment extensions are executed.
-/
unsafe def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    throw <| IO.userError "Supply one or more exact module names, e.g. the six Library.All roots."
  initSearchPath (← findSysroot)
  let imports ← args.toArray.mapM fun arg => do
    let moduleName := arg.toName
    if moduleName.isAnonymous then
      throw <| IO.userError s!"Invalid module name: {arg}"
    pure ({ module := moduleName } : Import)
  let env ← importModules imports {} (trustLevel := 0)
    (loadExts := false) (level := .private)
  try
    reportInventory env args.toArray
    IO.println "REPLAY_START official_Lean_4_33_Environment_replay trustLevel=0"
    (← IO.getStdout).flush
    discard <| Lean.Environment.replay env.constants.map₁
      (← mkEmptyEnvironment (trustLevel := 0))
    IO.println <| Json.compress <| Json.mkObj [
      ("phase", toJson "replay"),
      ("result", toJson "PASS"),
      ("kernel", toJson "official Lean 4.33.0"),
      ("axiom_policy_enforced", toJson false)
    ]
    return 0
  finally
    env.freeRegions
