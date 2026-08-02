from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SQ = ROOT / "LeanCondensedMatter" / "SecondQuantization"
OWNERS = {"Common", "Fermionic", "Bosonic"}

REMOVED_FILES = (
    SQ / "Common.lean",
    SQ / "Fermionic.lean",
    SQ / "Bosonic.lean",
    SQ / "Fermionic" / "Perturbation" / "DysonExpansion.lean",
    SQ / "Fermionic" / "Perturbation" / "ContinuousDyson.lean",
    SQ / "Fermionic" / "Diagrammatics" / "WickDiagram" / "ComponentPairs.lean",
    SQ / "Fermionic" / "Diagrammatics" / "WickDiagram" / "ComponentCrossingParity.lean",
    SQ / "Fermionic" / "Diagrammatics" / "WickDiagram" / "ComponentLegInversion.lean",
    SQ / "Fermionic" / "Diagrammatics" / "WickDiagram" / "ComponentOrderDecomposition.lean",
    SQ / "Fermionic" / "Diagrammatics" / "WickDiagram" / "ComponentDecompositionEquiv.lean",
    SQ / "Fermionic" / "Diagrammatics" / "WickDiagram" / "ComponentOrderedSimplex.lean",
    SQ / "Fermionic" / "Diagrammatics" / "WickDiagram" / "ComponentOrder.lean",
    SQ / "Fermionic" / "Diagrammatics" / "WickDiagram" / "ComponentPartition.lean",
    SQ / "Fermionic" / "Diagrammatics" / "WickDiagram" / "ComponentRestriction.lean",
    SQ / "Fermionic" / "Diagrammatics" / "WickDiagram" / "Reassemble.lean",
    SQ / "Fermionic" / "Diagrammatics" / "WickDiagram" / "ReassembleDecompose.lean",
    SQ / "Fermionic" / "Diagrammatics" / "WickDiagram" / "ReassembleComponentPartitionEq.lean",
    SQ / "Fermionic" / "Diagrammatics" / "WickDiagram" / "ReassembleRestrictComponent.lean",
)

REMOVED_DIRECTORIES = (
    SQ / "Bosonic" / "Foundations",
    SQ / "Bosonic" / "OperatorAlgebra",
)

REMOVED_EXACT_IMPORT = re.compile(
    r"^\s*import\s+LeanCondensedMatter\.SecondQuantization\.(Common|Fermionic|Bosonic)\s*$"
)
REMOVED_BOSONIC_PATH = re.compile(
    r"LeanCondensedMatter\.SecondQuantization\.Bosonic\.(Foundations|OperatorAlgebra)(?:\.|\s|$)"
)
STATISTICS_IMPORT = re.compile(
    r"^\s*import\s+LeanCondensedMatter\.SecondQuantization\.(Fermionic|Bosonic)(?:\.|\s|$)"
)
PHYSICS_IMPORT = re.compile(
    r"^\s*import\s+LeanCondensedMatter\.SecondQuantization(?:\.|\s|$)"
)
LEGACY_FERMIONIC_IDENTIFIER = re.compile(
    r"FockSpaceFermionic|FermionOccupation|fermionParticleNumber|fermionVacuum"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z0-9_'.]+)\s*$")
SECTION_RE = re.compile(r"^\s*(?:noncomputable\s+)?section(?:\s+([A-Za-z0-9_'.]+))?\s*$")
END_RE = re.compile(r"^\s*end(?:\s+([A-Za-z0-9_'.]+))?\s*$")
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(abbrev|axiom|class|def|inductive|instance|lemma|opaque|structure|theorem)\b"
    r"\s*([^\s:({\[]+)?"
)
STATISTIC_NAME_RE = re.compile(r"(?:Boson|Bosonic|Fermion|Fermionic)")

REMOVED_IMPORTS = {
    "import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonExpansion":
        "removed fermionic Dyson import",
    "import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.ContinuousDyson":
        "removed fermionic continuous-Dyson import",
    "import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentPairs":
        "removed fermionic ComponentPairs import",
    "import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentCrossingParity":
        "removed fermionic ComponentCrossingParity import",
    "import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentLegInversion":
        "removed fermionic ComponentLegInversion import",
    "import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentOrderDecomposition":
        "removed fermionic ComponentOrderDecomposition import",
    "import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentDecompositionEquiv":
        "removed fermionic ComponentDecompositionEquiv import",
    "import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentOrderedSimplex":
        "removed fermionic ComponentOrderedSimplex import",
    "import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentOrder":
        "removed fermionic ComponentOrder import",
    "import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentPartition":
        "removed fermionic ComponentPartition import",
    "import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentRestriction":
        "removed fermionic ComponentRestriction import",
    "import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.Reassemble":
        "removed fermionic Reassemble import",
    "import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ReassembleDecompose":
        "removed fermionic ReassembleDecompose import",
    "import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ReassembleComponentPartitionEq":
        "removed fermionic ReassembleComponentPartitionEq import",
    "import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ReassembleRestrictComponent":
        "removed fermionic ReassembleRestrictComponent import",
}

ALLOWED_EXTERNAL_DECLARATIONS = {
    (
        "LeanCondensedMatter/SecondQuantization/Common/Thermal/"
        "BlochDeDominicis/PairingWeight.lean",
        "Pairing.weight",
        "Combinatorics",
    ),
}


@dataclass
class Frame:
    kind: str
    name: str | None
    namespace_parts: tuple[str, ...] = ()


@dataclass
class Finding:
    owner: str
    path: Path
    line: int
    kind: str
    name: str
    namespace: str


def lean_files(root: Path):
    yield from sorted(root.rglob("*.lean"))


def relative(path: Path) -> str:
    return str(path.relative_to(ROOT))


def strip_comments(text: str) -> str:
    """Remove Lean line and nested block comments while preserving newlines."""
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    escaped = False

    while i < len(text):
        ch = text[i]
        nxt = text[i + 1] if i + 1 < len(text) else ""

        if depth:
            if ch == "/" and nxt == "-":
                depth += 1
                out.extend("  ")
                i += 2
            elif ch == "-" and nxt == "/":
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if in_string:
            out.append(ch)
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            i += 1
            continue

        if ch == '"':
            in_string = True
            out.append(ch)
            i += 1
        elif ch == "/" and nxt == "-":
            depth = 1
            out.extend("  ")
            i += 2
        elif ch == "-" and nxt == "-":
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
        else:
            out.append(ch)
            i += 1

    return "".join(out)


def current_namespace(stack: list[Frame]) -> tuple[str, ...]:
    parts: list[str] = []
    for frame in stack:
        if frame.kind == "namespace":
            parts.extend(frame.namespace_parts)
    return tuple(parts)


def close_scope(stack: list[Frame], name: str | None, path: Path, line_no: int) -> None:
    if not stack:
        raise RuntimeError(f"unmatched end in {relative(path)}:{line_no}")

    if name is None:
        stack.pop()
        return

    target = tuple(name.split("."))
    if len(target) > 1:
        before = current_namespace(stack)
        if len(before) < len(target) or before[-len(target):] != target:
            raise RuntimeError(
                f"qualified end `{name}` does not match namespace `{'.'.join(before)}` "
                f"in {relative(path)}:{line_no}"
            )
        removed: list[str] = []
        while stack and len(removed) < len(target):
            frame = stack.pop()
            if frame.kind == "namespace":
                removed[0:0] = frame.namespace_parts
        if tuple(removed[-len(target):]) != target:
            raise RuntimeError(
                f"could not close qualified namespace `{name}` in {relative(path)}:{line_no}"
            )
        return

    for index in range(len(stack) - 1, -1, -1):
        frame = stack[index]
        frame_matches = frame.name == name or (
            frame.kind == "namespace" and frame.namespace_parts and frame.namespace_parts[-1] == name
        )
        if frame_matches:
            del stack[index:]
            return

    raise RuntimeError(f"unmatched named end `{name}` in {relative(path)}:{line_no}")


def audit_file(path: Path) -> tuple[list[Finding], list[Finding]]:
    rel = path.relative_to(SQ)
    owner = rel.parts[0] if rel.parts and rel.parts[0] in OWNERS else "Root"
    expected = ("SecondQuantization", owner) if owner in OWNERS else ("SecondQuantization",)
    text = strip_comments(path.read_text(encoding="utf-8"))
    stack: list[Frame] = []
    misplaced: list[Finding] = []
    statistic_names: list[Finding] = []

    for line_no, line in enumerate(text.splitlines(), start=1):
        if match := NAMESPACE_RE.match(line):
            raw = match.group(1)
            stack.append(Frame("namespace", raw, tuple(raw.split("."))))
            continue
        if match := SECTION_RE.match(line):
            stack.append(Frame("section", match.group(1)))
            continue
        if match := END_RE.match(line):
            close_scope(stack, match.group(1), path, line_no)
            continue
        if match := DECL_RE.match(line):
            kind = match.group(1)
            name = match.group(2) or "<anonymous>"
            namespace_parts = current_namespace(stack)
            namespace = ".".join(namespace_parts) or "<root>"
            finding = Finding(owner, path, line_no, kind, name, namespace)
            if namespace_parts[: len(expected)] != expected:
                misplaced.append(finding)
            if STATISTIC_NAME_RE.search(name):
                statistic_names.append(finding)

    if stack:
        scopes = ", ".join(f"{frame.kind}:{frame.name or '<anonymous>'}" for frame in stack)
        raise RuntimeError(f"unclosed scopes in {relative(path)}: {scopes}")

    return misplaced, statistic_names


def collect_namespace_findings() -> tuple[list[Finding], list[Finding]]:
    misplaced: list[Finding] = []
    statistic_names: list[Finding] = []

    for path in lean_files(SQ):
        file_misplaced, file_statistics = audit_file(path)
        misplaced.extend(file_misplaced)
        statistic_names.extend(file_statistics)

    misplaced = [
        finding
        for finding in misplaced
        if (relative(finding.path), finding.name, finding.namespace)
        not in ALLOWED_EXTERNAL_DECLARATIONS
    ]
    return misplaced, statistic_names


def check_removed_paths(errors: list[str]) -> None:
    for path in REMOVED_FILES:
        if path.exists():
            errors.append(f"removed compatibility module exists: {relative(path)}")
    for path in REMOVED_DIRECTORIES:
        if path.exists():
            errors.append(f"removed directory exists: {relative(path)}")

    for path in lean_files(ROOT / "LeanCondensedMatter"):
        for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            stripped = line.strip()
            if REMOVED_EXACT_IMPORT.match(line):
                errors.append(f"removed umbrella import: {relative(path)}:{line_no}: {stripped}")
            if REMOVED_BOSONIC_PATH.search(line):
                errors.append(f"removed bosonic path: {relative(path)}:{line_no}: {stripped}")
            if description := REMOVED_IMPORTS.get(stripped):
                errors.append(f"{description}: {relative(path)}:{line_no}: {stripped}")


def check_dependency_direction(errors: list[str]) -> None:
    for path in lean_files(SQ / "Common"):
        for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            if STATISTICS_IMPORT.match(line):
                errors.append(
                    f"Common imports statistics-specific code: {relative(path)}:{line_no}: {line.strip()}"
                )

    for area in ("Analysis", "Combinatorics"):
        root = ROOT / "LeanCondensedMatter" / area
        for path in lean_files(root):
            for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
                if PHYSICS_IMPORT.match(line):
                    errors.append(
                        f"{area} imports SecondQuantization: {relative(path)}:{line_no}: {line.strip()}"
                    )


def check_legacy_identifiers(errors: list[str]) -> None:
    for path in lean_files(ROOT / "LeanCondensedMatter"):
        text = path.read_text(encoding="utf-8")
        for match in LEGACY_FERMIONIC_IDENTIFIER.finditer(text):
            line_no = text.count("\n", 0, match.start()) + 1
            errors.append(
                f"legacy fermionic identifier: {relative(path)}:{line_no}: {match.group(0)}"
            )


def check_declaration_namespaces(errors: list[str]) -> None:
    misplaced, statistic_names = collect_namespace_findings()
    for finding in misplaced:
        errors.append(
            "declaration outside path-owned namespace: "
            f"{relative(finding.path)}:{finding.line}: "
            f"{finding.kind} {finding.name} in {finding.namespace}"
        )
    for finding in statistic_names:
        errors.append(
            "statistic-encoded declaration name: "
            f"{relative(finding.path)}:{finding.line}: {finding.name}"
        )


def check_entry_point(errors: list[str]) -> None:
    entry = SQ.with_suffix(".lean")
    if not entry.is_file():
        errors.append(f"missing canonical entry point: {relative(entry)}")

    root_module = ROOT / "LeanCondensedMatter.lean"
    expected = "import LeanCondensedMatter.SecondQuantization"
    if expected not in root_module.read_text(encoding="utf-8").splitlines():
        errors.append(f"repository root does not import canonical entry point: {expected}")


def main() -> int:
    errors: list[str] = []
    check_removed_paths(errors)
    check_dependency_direction(errors)
    check_legacy_identifiers(errors)
    check_declaration_namespaces(errors)
    check_entry_point(errors)

    if errors:
        print("SecondQuantization architecture check failed:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("SecondQuantization architecture check passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
