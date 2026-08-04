import LeanCondensedMatter
import Mathlib.Lean.Name
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Meta Elab

elab "assert_project_no_sorry" : command =>
  Command.runTermElabM fun _ => do
    let namesByModule ← allNamesByModule (fun _ => true)
    let namesByModule := namesByModule.filter fun moduleName _ =>
      moduleName.getRoot.toString = "LeanCondensedMatter"
    let mut offenders : Array Name := #[]
    for (_, names) in namesByModule.toList do
      for name in names do
        let axioms ← Lean.collectAxioms name
        if axioms.contains ``sorryAx then
          offenders := offenders.push name
    unless offenders.isEmpty do
      for name in offenders do
        logError m!"{.ofConstName name} depends on sorryAx"
      throwError "found {offenders.size} LeanCondensedMatter declarations depending on sorryAx"
    logInfo "All declarations reachable from LeanCondensedMatter are sorry-free."

assert_project_no_sorry
