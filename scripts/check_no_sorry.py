from __future__ import annotations

import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE_ROOT = ROOT / "LeanCondensedMatter"
CHECK_FILE = ROOT / ".lake" / "CheckNoSorry.lean"


def module_name(path: Path) -> str:
    relative = path.relative_to(ROOT).with_suffix("")
    return ".".join(relative.parts)


def generated_source() -> str:
    modules = sorted(module_name(path) for path in SOURCE_ROOT.rglob("*.lean"))
    if not modules:
        raise RuntimeError(f"no Lean modules found under {SOURCE_ROOT}")

    imports = "\n".join(f"import {module}" for module in modules)
    check = r'''
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
    logInfo "All LeanCondensedMatter declarations are sorry-free."

assert_project_no_sorry
'''
    return imports + "\n" + check


def main() -> int:
    CHECK_FILE.parent.mkdir(parents=True, exist_ok=True)
    CHECK_FILE.write_text(generated_source(), encoding="utf-8")
    try:
        subprocess.run(
            ["lake", "env", "lean", str(CHECK_FILE)],
            cwd=ROOT,
            check=True,
        )
    finally:
        CHECK_FILE.unlink(missing_ok=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
