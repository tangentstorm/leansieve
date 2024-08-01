import Lean
import Mathlib.Data.Nat.Prime

open Lean Meta Elab Command

def isPrefix (pfx : Name) (n : Name) : Bool :=
  n.components.take pfx.components.length == pfx.components

def listTheoremsInNamespace (ns : Name) : MetaM (List Name) := do
  let env ← getEnv
  let declNames := env.constants.toList.map Prod.fst
  let nsDecls := declNames.filter (isPrefix ns)
  let theorems ← nsDecls.filterM fun declName => do
    match env.find? declName with
    | some (ConstantInfo.thmInfo _) => pure true
    | _ => pure false
  return theorems

def getTheoremStatement (declName : Name) : MetaM (Option String) := do
  match (← getEnv).find? declName with
  | some (ConstantInfo.thmInfo thm) =>
    let type ← Meta.ppExpr thm.type
    pure (some s!"{declName} : {type}")
  | _ => pure none

elab "listTheorems " ns:ident : command => do
  let nsName := ns.getId
  liftTermElabM do
    let theorems ← listTheoremsInNamespace nsName
    for thm in theorems do
      if let some stmt ← getTheoremStatement thm then
        IO.println stmt

#print Prime



-- listTheorems


elab "#listElabs" : command => do
  let env ← getEnv
  let elabs := env.constants.toList.filter fun (name, _) =>
    name.toString.startsWith "Lean.Elab.Command.elabCommand"
  for (name, _) in elabs do
    IO.println s!"{name.toString.dropWhile (· != '_')}"

#listElabs
