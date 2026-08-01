from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SQ = ROOT / "LeanCondensedMatter" / "SecondQuantization"
FERMIONIC = SQ / "Fermionic"
OLD_MODULE = FERMIONIC / "Perturbation" / "DysonExpansion.lean"
ARCH_CHECK = ROOT / "scripts" / "check_second_quantization_architecture.py"

OLD_IMPORT = (
    "import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonExpansion"
)
COMMON_IMPORT = (
    "import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansion"
)
INTERACTION_IMPORT = (
    "import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.InteractionPicture"
)

IMPORT_REPLACEMENTS = {
    FERMIONIC / "Perturbation" / "DysonExpansionVerification.lean": INTERACTION_IMPORT,
    FERMIONIC / "Perturbation" / "DysonPartitionSeries.lean": COMMON_IMPORT,
    FERMIONIC / "Perturbation" / "ContinuousDyson.lean": INTERACTION_IMPORT,
    FERMIONIC / "Perturbation.lean": "",
}

BARE_THEOREM_REPLACEMENTS = {
    "dysonCoeff_zero": "Common.dysonCoeff_zero",
    "dysonCoeff_succ": "Common.dysonCoeff_succ",
    "continuous_matrixCoeff_dysonCoeff": "Common.continuous_matrixCoeff_dysonCoeff",
}

ROOT_DYSON_CALL = re.compile(r"(?<![\w.])dysonCoeff\s+ε\s+")
BARE_DYSON_CALL = re.compile(r"(?<![\w.])dysonCoeff\s")
BARE_FORWARDING_THEOREM = re.compile(
    r"(?<![\w.])(dysonCoeff_zero|dysonCoeff_succ|continuous_matrixCoeff_dysonCoeff)\b"
)


def parse_argument(text: str, start: int) -> tuple[str, int]:
    index = start
    while index < len(text) and text[index].isspace():
        index += 1
    if index >= len(text):
        raise RuntimeError("missing argument after `dysonCoeff ε`")

    if text[index] == "(":
        depth = 0
        for end in range(index, len(text)):
            char = text[end]
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth == 0:
                    return text[index : end + 1], end + 1
        raise RuntimeError("unbalanced parenthesized argument after `dysonCoeff ε`")

    match = re.match(r"[A-Za-z_][A-Za-z0-9_']*", text[index:])
    if match is None:
        raise RuntimeError(
            "unsupported argument after `dysonCoeff ε`: " + text[index : index + 40]
        )
    end = index + match.end()
    return text[index:end], end


def rewrite_dyson_calls(text: str) -> str:
    output: list[str] = []
    cursor = 0
    while True:
        match = ROOT_DYSON_CALL.search(text, cursor)
        if match is None:
            output.append(text[cursor:])
            return "".join(output)
        argument, end = parse_argument(text, match.end())
        output.append(text[cursor : match.start()])
        output.append(f"Common.dysonCoeff (fermionEnergy ε) {argument}")
        cursor = end


def replace_exact_import(text: str, replacement: str) -> str:
    output: list[str] = []
    replaced = False
    for line in text.splitlines(keepends=True):
        newline = "\n" if line.endswith("\n") else ""
        content = line[:-1] if newline else line
        if content == OLD_IMPORT:
            replaced = True
            if replacement:
                output.append(replacement + newline)
        else:
            output.append(line)
    if not replaced:
        raise RuntimeError("expected exact old import line was not found")
    return "".join(output)


def rewrite_fermionic_files() -> None:
    for path in sorted(FERMIONIC.rglob("*.lean")):
        if path == OLD_MODULE:
            continue
        original = path.read_text(encoding="utf-8")
        updated = original

        if any(line == OLD_IMPORT for line in updated.splitlines()):
            if path not in IMPORT_REPLACEMENTS:
                raise RuntimeError(
                    f"unclassified old import in {path.relative_to(ROOT)}"
                )
            updated = replace_exact_import(updated, IMPORT_REPLACEMENTS[path])

        updated = rewrite_dyson_calls(updated)

        # Calls with explicit fermionic parameters need the energy specialization made explicit.
        updated = updated.replace(
            "continuous_matrixCoeff_dysonCoeff ε V",
            "Common.continuous_matrixCoeff_dysonCoeff (fermionEnergy ε) V",
        )
        updated = updated.replace(
            "dysonCoeff_zero ε V",
            "Common.dysonCoeff_zero (fermionEnergy ε) V",
        )
        updated = updated.replace(
            "dysonCoeff_succ ε V",
            "Common.dysonCoeff_succ (fermionEnergy ε) V",
        )

        for old, new in BARE_THEOREM_REPLACEMENTS.items():
            updated = re.sub(rf"(?<![\w.]){old}\b", new, updated)

        # The Common recursion exposes the Common interaction-picture normal form. Keep the
        # surrounding integrability and rewrite expressions in that same normal form.
        if "Common.dysonCoeff (fermionEnergy ε) V" in updated:
            updated = updated.replace(
                "interactionPicture ε V",
                "Common.interactionPicture (fermionEnergy ε) V",
            )

        if "Common.dysonCoeff" in updated and COMMON_IMPORT not in updated:
            updated = COMMON_IMPORT + "\n" + updated

        if updated != original:
            path.write_text(updated, encoding="utf-8")


def update_architecture_guard() -> None:
    original = ARCH_CHECK.read_text(encoding="utf-8")
    updated = original

    old_tuple = '''REMOVED_FILES = (
    SQ / "Common.lean",
    SQ / "Fermionic.lean",
    SQ / "Bosonic.lean",
)'''
    new_tuple = '''REMOVED_FILES = (
    SQ / "Common.lean",
    SQ / "Fermionic.lean",
    SQ / "Bosonic.lean",
    SQ / "Fermionic" / "Perturbation" / "DysonExpansion.lean",
)'''
    if old_tuple not in updated:
        raise RuntimeError("architecture guard REMOVED_FILES layout changed")
    updated = updated.replace(old_tuple, new_tuple)

    old_check = '''            if REMOVED_BOSONIC_PATH.search(line):
                errors.append(f"removed bosonic path: {relative(path)}:{line_no}: {line.strip()}")'''
    new_check = '''            if REMOVED_BOSONIC_PATH.search(line):
                errors.append(f"removed bosonic path: {relative(path)}:{line_no}: {line.strip()}")
            if line.strip() == "import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonExpansion":
                errors.append(
                    f"removed fermionic Dyson import: {relative(path)}:{line_no}: {line.strip()}"
                )'''
    if old_check not in updated:
        raise RuntimeError("architecture guard removed-path check layout changed")
    updated = updated.replace(old_check, new_check)

    ARCH_CHECK.write_text(updated, encoding="utf-8")


def validate() -> None:
    if OLD_MODULE.exists():
        raise RuntimeError(f"obsolete module remains: {OLD_MODULE.relative_to(ROOT)}")

    errors: list[str] = []
    for path in sorted(FERMIONIC.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        if any(line == OLD_IMPORT for line in text.splitlines()):
            errors.append(f"old import: {path.relative_to(ROOT)}")
        if BARE_DYSON_CALL.search(text):
            errors.append(f"bare root dysonCoeff call: {path.relative_to(ROOT)}")
        if BARE_FORWARDING_THEOREM.search(text):
            errors.append(f"bare forwarding theorem call: {path.relative_to(ROOT)}")
    if errors:
        raise RuntimeError("fermionic Dyson migration incomplete:\n" + "\n".join(errors))


def main() -> None:
    if not OLD_MODULE.is_file():
        raise RuntimeError(f"missing migration source: {OLD_MODULE.relative_to(ROOT)}")
    rewrite_fermionic_files()
    OLD_MODULE.unlink()
    update_architecture_guard()
    validate()


if __name__ == "__main__":
    main()
