import Mathlib.Lean.CoreM
import Mathlib.Tactic.ITauto
import Lean
import HamiltonToItauto.Formula

elab "explore" : tactic => do
  -- get the definition of the function which implements ipc_formula
  let ipcFormulaConstInfo ← Lean.getConstInfo `ipc_formula
  let ipcExpr := Lean.ConstantInfo.value! ipcFormulaConstInfo
  IO.println ipcExpr

theorem _c : true := by
  explore
  sorry

def getIPCExpr : Lean.Meta.MetaM Lean.Expr := do
  -- let formula := ipc_formula
  let ipcFormulaConstInfo ← Lean.getConstInfo `example_tauto
  return Lean.ConstantInfo.value! ipcFormulaConstInfo

def main : IO Unit := do
  let ipcExprCoreM := Lean.Meta.MetaM.run' getIPCExpr
  let emptyModules := Array.mkEmpty 0
  let ipcExpr <- CoreM.withImportModules emptyModules ipcExprCoreM
  IO.println ipcExpr

-- import Lean

-- import HamiltonToItauto.Formula
-- open Lean Lean.Elab Lean.Elab.Tactic Lean.Elab.Term

-- elab "explore" : tactic => do
--   -- get the definition of the function which implements ipc_formula
--   let ipcFormulaConstInfo ← getConstInfo `ipc_formula
--   let ipcExpr := Lean.ConstantInfo.value! ipcFormulaConstInfo
--   IO.println ipcExpr

--   let mvarId : MVarId ← Lean.Elab.Tactic.getMainGoal
--   let metavarDecl : MetavarDecl ← mvarId.getDecl

--   IO.println "Our metavariable"
--   -- [anonymous] : 2 = 2
--   IO.println s!"\n{metavarDecl.userName} : {metavarDecl.type}"

--   IO.println "\nAll of its local declarations"
--   let localContext : LocalContext := metavarDecl.lctx
--   for (localDecl : LocalDecl) in localContext do
--     if localDecl.isImplementationDetail then
--       -- (implementation detail) red : 1 = 1 → 2 = 2 → 2 = 2
--       IO.println s!"\n(implementation detail) {localDecl.userName} : {localDecl.type}"
--     else
--       -- hA : 1 = 1
--       -- hB : 2 = 2
--       IO.println s!"\n{localDecl.userName} : {localDecl.type}"

-- theorem red (hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
--   explore
--   sorry

-- import Lean
-- import Aesop

-- import HamiltonToItauto.Basic
-- import HamiltonToItauto.Formula

-- open Lean Lean.Meta

-- def getPropProof (prop : Name) : MetaM Expr := do
--   let propType := mkConst prop
--   let proof ← mkFreshExprMVar propType
--   return proof

-- def getTypeString (prop : Name) : MetaM String := do
--   let proof ← getPropProof prop
--   return toString proof

-- def main : IO Unit := do
--   let typeStr := getTypeString `ipc_formula
--   IO.println typeStr
--   return ()
