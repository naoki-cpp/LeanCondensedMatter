#!/usr/bin/env python3
"""Build changed .lean files, mechanically fix `unused section variable(s)`
warnings by inserting `omit [...] in`, and report any other warnings.

Used by .githooks/pre-push. See notes/conventions.md ("Proof style") for the
project's policy: never disable linter.unusedSectionVars globally; prefer
narrowing the `variable` scope by hand when a warning recurs across many
declarations in the same block (this script only ever applies the mechanical
`omit ... in` fallback and flags that pattern for manual review).
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

UNUSED_VAR_RE = re.compile(
    r"^warning: (?P<file>[^:]+):(?P<line>\d+):(?P<col>\d+): "
    r"automatically included section variable\(s\) unused in theorem "
    r"`(?P<name>[^`]+)`:$"
)
VAR_LIST_RE = re.compile(r"^\s+((\[[^\]]+\]\s*)+)$")


def lean_module_name(lean_file: str) -> str | None:
    """Map a repo-relative .lean path to its Lake module name, or None if it
    is not part of the LeanCondensedMatter library."""
    if not lean_file.endswith(".lean"):
        return None
    if not lean_file.startswith("LeanCondensedMatter/"):
        return None
    return lean_file[: -len(".lean")].replace("/", ".")


def run_lake_build(modules: list[str]) -> str:
    if not modules:
        return ""
    proc = subprocess.run(
        ["lake", "build", *modules],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
    )
    return proc.stdout + proc.stderr


def parse_unused_var_warnings(output: str) -> list[tuple[str, int, str, str]]:
    """Returns (file, decl_line, decl_name, omit_clause) for each
    unused-section-variable warning found."""
    lines = output.splitlines()
    found = []
    for i, line in enumerate(lines):
        m = UNUSED_VAR_RE.match(line)
        if not m:
            continue
        var_list = None
        for j in range(i + 1, min(i + 4, len(lines))):
            vm = VAR_LIST_RE.match(lines[j])
            if vm:
                var_list = vm.group(1).strip()
                break
            if lines[j].strip() and not lines[j].startswith(" "):
                break
        if var_list is None:
            continue
        found.append((m.group("file"), int(m.group("line")), m.group("name"), f"omit {var_list} in"))
    return found


def other_warnings(output: str) -> list[str]:
    lines = output.splitlines()
    consumed = set()
    for i, line in enumerate(lines):
        if UNUSED_VAR_RE.match(line):
            for j in range(i, min(i + 4, len(lines))):
                consumed.add(j)
    return [
        line
        for i, line in enumerate(lines)
        if line.startswith("warning:") and i not in consumed
    ]


def insert_omit(file_path: Path, decl_line_1idx: int, omit_clause: str) -> bool:
    text = file_path.read_text(encoding="utf-8")
    lines = text.splitlines(keepends=True)
    idx = decl_line_1idx - 1
    if idx < 0 or idx >= len(lines):
        return False

    insert_at = idx
    j = idx - 1
    if j >= 0 and lines[j].rstrip("\n").rstrip().endswith("-/"):
        k = j
        while k >= 0 and not lines[k].lstrip().startswith("/--"):
            k -= 1
        if k >= 0:
            insert_at = k

    prev_line = lines[insert_at - 1].strip() if insert_at > 0 else ""
    if prev_line == omit_clause.strip():
        return False

    lines.insert(insert_at, omit_clause + "\n")
    file_path.write_text("".join(lines), encoding="utf-8")
    return True


def fix_unused_var_warnings(warnings: list[tuple[str, int, str, str]]) -> list[str]:
    """Applies fixes bottom-to-top per file so line numbers stay valid.
    Returns the list of files actually modified."""
    by_file: dict[str, list[tuple[int, str, str]]] = {}
    for file, line, name, clause in warnings:
        by_file.setdefault(file, []).append((line, name, clause))

    modified = []
    for file, entries in by_file.items():
        path = REPO_ROOT / file
        if not path.exists():
            continue
        entries.sort(key=lambda e: e[0], reverse=True)
        file_changed = False
        for line, _name, clause in entries:
            if insert_omit(path, line, clause):
                file_changed = True
        if file_changed:
            modified.append(file)

        if len(entries) >= 3 and len({c for _, _, c in entries}) == 1:
            print(
                f"note: {file} has {len(entries)} declarations with the same "
                f"unused section variable(s) ({entries[0][2]}). Consider narrowing "
                "the surrounding `variable` scope instead of relying on "
                "per-declaration `omit ... in` — see notes/conventions.md.",
                file=sys.stderr,
            )
    return modified


def main(changed_files: list[str]) -> int:
    modules = [m for f in changed_files if (m := lean_module_name(f))]
    if not modules:
        return 0

    print(f"Checking {len(modules)} changed Lean module(s) for warnings...", file=sys.stderr)
    output = run_lake_build(modules)

    unused_var_warnings = parse_unused_var_warnings(output)
    modified = fix_unused_var_warnings(unused_var_warnings) if unused_var_warnings else []

    if modified:
        print(
            "\nApplied mechanical `omit ... in` fixes to:\n  "
            + "\n  ".join(modified)
            + "\n\nReview and commit these changes, then push again.",
            file=sys.stderr,
        )
        return 1

    # Re-check for any warnings not handled above (rebuild not needed if
    # nothing was fixed — `output` already reflects the current state).
    remaining = other_warnings(output)
    if remaining:
        print("\nUnresolved warning(s) — fix by hand before pushing:\n", file=sys.stderr)
        for w in remaining:
            print(w, file=sys.stderr)
        return 1

    print("No warnings.", file=sys.stderr)
    return 0


if __name__ == "__main__":
    # Changed .lean file paths (repo-relative) are passed as arguments by
    # .githooks/pre-push, which computes them from `git diff`.
    sys.exit(main(sys.argv[1:]))
