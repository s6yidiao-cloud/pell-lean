import Pell.UniformDoubledParameterEstimate
import Lean

open Lean Elab Command

private def projectConstant (n : Name) : Bool :=
  n.toString.startsWith "PellPaper." || n.toString.startsWith "_private.Pell."

private partial def collectProjectRoute (env : Environment) (n : Name) :
    StateM NameSet Unit := do
  if !projectConstant n || (← get).contains n then return
  modify fun s => s.insert n
  if let some info := env.find? n then
    for dep in info.type.getUsedConstants do
      collectProjectRoute env dep
    if let some value := info.value? (allowOpaque := true) then
      for dep in value.getUsedConstants do
        collectProjectRoute env dep

run_cmd do
  let env := (← getEnv).setExporting false
  let target := ``PellPaper.uniform_exceptional_doubled_parameter
  let deps := ((collectProjectRoute env target).run {}).2.toArray.qsort Name.lt
  let forbidden := deps.filter fun n =>
    let s := n.toString
    !s.startsWith target.toString &&
      (s.contains "uniformExceptionalEstimate" ||
       s.contains "uniformDyadicAllRadicandEstimate" ||
       s.contains "final_uniform_exceptional" ||
       s.contains "PellPaper.uniform_exceptional")
  logInfo m!"Project proof/type route contains {deps.size} project constants."
  logInfo m!"Old arbitrary-radicand endpoint matches: {forbidden}"
  unless forbidden.isEmpty do
    throwError "Dependency route audit found an old arbitrary-radicand endpoint."
