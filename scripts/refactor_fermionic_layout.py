#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import re
import subprocess

REPO = Path.cwd()
FERMIONIC = REPO / "LeanCondensedMatter/SecondQuantization/Fermionic"
WORKFLOW = REPO / ".github/workflows/lean_action_ci.yml"
SELF = REPO / "scripts/refactor_fermionic_layout.py"
MODULE_PREFIX = "LeanCondensedMatter.SecondQuantization.Fermionic"

GROUPS: dict[str, list[str]] = {
    "Algebra": [
        "Occupation",
        "FockSpace",
        "CreationAnnihilation",
        "ParticleNumberCharge",
        "CanonicalAnticommutationRelations",
        "ExchangeAlgebra",
        "NumberOperator",
        "Hamiltonian",
        "WeightedNumberOperator",
    ],
    "ImaginaryTime": [
        "ImaginaryTimeEvolution",
        "InteractionPicture",
    ],
    "Thermal": [
        "WeightedFreeTwoPointFunction",
        "FreeBoltzmannWeight",
        "FreePartitionFunction",
        "FreeTwoPointFunction",
        "WeightedContraction",
        "QuantumLinkedCluster",
    ],
    "Perturbation": [
        "FormalLogPartitionFunction",
        "DysonExpansion",
        "DysonExpansionVerification",
        "DysonPartitionSeries",
        "DysonVertexMoment",
    ],
    "Diagrammatics": [
        "QuarticInteraction",
        "QuarticLocalLeg",
        "DysonDiagramExpansion",
    ],
}


def run(*args: str) -> None:
    subprocess.run(args, check=True)


def git_mv(src: Path, dst: Path) -> None:
    if not src.exists():
        raise SystemExit(f"expected source path is missing: {src}")
    if dst.exists():
        raise SystemExit(f"destination already exists: {dst}")
    dst.parent.mkdir(parents=True, exist_ok=True)
    run("git", "mv", str(src), str(dst))


# Move the ordinary root implementation files into their responsibility directories.
module_replacements: dict[str, str] = {}
for group, modules in GROUPS.items():
    for module in modules:
        src = FERMIONIC / f"{module}.lean"
        dst = FERMIONIC / group / f"{module}.lean"
        git_mv(src, dst)
        module_replacements[f"{MODULE_PREFIX}.{module}"] = f"{MODULE_PREFIX}.{group}.{module}"

# Move the complete Wick-diagram implementation tree under Diagrammatics.
git_mv(FERMIONIC / "WickDiagram", FERMIONIC / "Diagrammatics/WickDiagram")
git_mv(FERMIONIC / "WickDiagram.lean", FERMIONIC / "Diagrammatics/WickDiagram.lean")
git_mv(
    FERMIONIC / "WickDiagramConnected.lean",
    FERMIONIC / "Diagrammatics/WickDiagram/Connected.lean",
)
module_replacements[f"{MODULE_PREFIX}.WickDiagramConnected"] = (
    f"{MODULE_PREFIX}.Diagrammatics.WickDiagram.Connected"
)
module_replacements[f"{MODULE_PREFIX}.WickDiagram"] = (
    f"{MODULE_PREFIX}.Diagrammatics.WickDiagram"
)

# Rewrite Lean module references. Longest names go first so subtree imports are handled safely.
for path in REPO.rglob("*.lean"):
    text = path.read_text(encoding="utf-8")
    updated = text
    for old, new in sorted(module_replacements.items(), key=lambda item: len(item[0]), reverse=True):
        updated = updated.replace(old, new)
    if updated != text:
        path.write_text(updated, encoding="utf-8")

# QuantumLinkedCluster is part of the thermal API, so expose it through that umbrella.
thermal_umbrella = FERMIONIC / "Thermal.lean"
thermal_text = thermal_umbrella.read_text(encoding="utf-8")
quantum_import = f"import {MODULE_PREFIX}.Thermal.QuantumLinkedCluster\n"
if quantum_import not in thermal_text:
    anchor = f"import {MODULE_PREFIX}.Thermal.WeightedContraction\n"
    if anchor not in thermal_text:
        raise SystemExit("could not find the Thermal umbrella insertion point")
    thermal_text = thermal_text.replace(anchor, anchor + quantum_import, 1)
    thermal_umbrella.write_text(thermal_text, encoding="utf-8")

# The package root already imports Fermionic, whose Thermal umbrella now exports QuantumLinkedCluster.
package_root = REPO / "LeanCondensedMatter.lean"
package_text = package_root.read_text(encoding="utf-8")
package_text = package_text.replace(quantum_import, "")
package_root.write_text(package_text, encoding="utf-8")

# Root cleanliness: only responsibility umbrellas may remain as .lean files in Fermionic/.
allowed_root_files = {
    "Algebra.lean",
    "ImaginaryTime.lean",
    "Thermal.lean",
    "Perturbation.lean",
    "Diagrammatics.lean",
}
unexpected = sorted(
    path.name for path in FERMIONIC.glob("*.lean") if path.name not in allowed_root_files
)
if unexpected:
    raise SystemExit(f"unclassified Fermionic root modules remain: {unexpected}")

# Verify every project-local Lean import resolves to a source file.
missing_imports: list[tuple[Path, str]] = []
import_re = re.compile(r"^import\s+(LeanCondensedMatter(?:\.[A-Za-z0-9_']+)+)\s*$")
for path in REPO.rglob("*.lean"):
    for line in path.read_text(encoding="utf-8").splitlines():
        match = import_re.match(line)
        if not match:
            continue
        module = match.group(1)
        target = REPO / (module.replace(".", "/") + ".lean")
        if not target.exists():
            missing_imports.append((path, module))
if missing_imports:
    details = "\n".join(f"{path}: {module}" for path, module in missing_imports)
    raise SystemExit(f"project-local imports no longer resolve:\n{details}")

# Remove the temporary workflow hook and restore read-only contents permission.
workflow_text = WORKFLOW.read_text(encoding="utf-8")
workflow_text = workflow_text.replace("  contents: write\n", "  contents: read\n", 1)
workflow_text = re.sub(
    r"\n      # BEGIN TEMP FERMIONIC LAYOUT REFACTOR\n.*?\n      # END TEMP FERMIONIC LAYOUT REFACTOR\n",
    "\n",
    workflow_text,
    flags=re.DOTALL,
)
WORKFLOW.write_text(workflow_text, encoding="utf-8")

SELF.unlink()
print("Fermionic source layout refactor completed successfully.")
