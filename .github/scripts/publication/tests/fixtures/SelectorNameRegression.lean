import Lean

open Lean

/-! Exact macro-scoped failure from ClassFieldTheory CI and distinct string/numeric names. -/

def expectRoundTrip (name : Name) : IO Unit := do
  let spelling := Name.toStringWithSep "." true name
  unless Syntax.decodeNameLit ("`" ++ spelling) == some name do
    throw (IO.userError s!"Structural name changed: {spelling}")

def main : IO Unit := do
  let failedName : Name := Name.num (Name.str (Name.str (Name.num (Name.str (Name.str (Name.str (Name.str (Name.str (Name.str (Name.str (Name.str (Name.str (Name.anonymous) "AlgebraicGeometry") "FiniteEtale") "hint") "_@") "Nyll") "EtaleFundamentalGroups") "Pi1") "GeometricFiber") "FieldPoints") 2250177116) "_hygCtx") "_hyg") 3
  unless Syntax.decodeNameLit ("`" ++ failedName.toString) != some failedName do
    throw (IO.userError "Expected the original display-name bug to reproduce")
  expectRoundTrip failedName
  for name in [Name.str .anonymous "a.b", Name.str (.str .anonymous "a") "3",
               Name.num (.str .anonymous "a") 3, Name.str .anonymous "_@",
               Name.num (.str (.str .anonymous "_private") "Module") 7] do
    expectRoundTrip name
  IO.println "PASS: original CI failure reproduced; all 6 structural selector round trips preserved"
