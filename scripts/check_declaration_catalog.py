"""Validate compiled declaration graph and the unchanged theorem audit projection."""
import json
import re
from pathlib import Path
import sys


def validate(declarations, theorems):
    by_name = {row["name"]: row for row in declarations}
    assert declarations and len(by_name) == len(declarations), "empty catalog or duplicate names"
    assert list(by_name) == sorted(by_name), "catalog must be sorted"
    kinds = {"theorem", "def", "abbrev", "opaque", "axiom", "inductive",
             "constructor", "recursor", "quotient"}
    for row in declarations:
        assert row["kind"] in kinds
        assert isinstance(row["generated"], bool)
        assert row["module"] == "LeanCondensedMatter" or row["module"].startswith("LeanCondensedMatter.")
        assert row["sourceFile"] == row["module"].replace(".", "/") + ".lean"
        assert isinstance(row["statement"], str)
        if not row["generated"]:
            assert isinstance(row["sourceLine"], int) and row["sourceLine"] > 0
            assert isinstance(row["sourceColumn"], int) and row["sourceColumn"] >= 0
        for key in ("dependencies", "typeDependencies", "valueDependencies", "dependents"):
            assert row[key] == sorted(set(row[key])), (row["name"], key)
            assert all(name in by_name for name in row[key]), (row["name"], key, "dangling edge")
        assert set(row["dependencies"]) == set(row["typeDependencies"]) | set(row["valueDependencies"])
        assert row["name"] not in row["dependencies"]
        for dependency in row["dependencies"]:
            assert row["name"] in by_name[dependency]["dependents"]
        for consumer in row["dependents"]:
            assert row["name"] in by_name[consumer]["dependencies"]
    for theorem in theorems:
        row = by_name[theorem["name"]]
        assert row["kind"] == "theorem" and not row["generated"]
        for key, value in theorem.items():
            if key not in {"dependencies", "dependents"}:
                assert row[key] == value, (row["name"], key, "audit changed")
        # The audit contains only theorem references in proof terms.
        assert set(theorem["dependencies"]) <= set(row["valueDependencies"])



def validate_retained_catalog(document, declarations, theorems):
    """Check all retained names against compiled declarations, not source-text matches."""
    theorem_header = "## Retained declarations\n"
    other_header = "## Other retained API contracts (not theorem declarations)\n"
    assert document.count(theorem_header) == 1
    assert document.count(other_header) == 1
    theorem_section, other_section = document.split(theorem_header, 1)[1].split(
        other_header, 1
    )

    theorem_lines = [line for line in theorem_section.splitlines()
                     if line.startswith("- ")]
    api_lines = [line for line in other_section.splitlines()
                 if line.startswith("- ")]
    theorem_names = []
    for line in theorem_lines:
        match = re.fullmatch(r"- `([^`]+)`(?: —.*)?", line)
        assert match is not None, ("invalid retained theorem entry", line)
        theorem_names.append(match.group(1))
    api_names = []
    for line in api_lines:
        match = re.fullmatch(r"- \*\*`([^`]+)`\*\* — .+", line)
        assert match is not None, ("invalid non-theorem API entry", line)
        api_names.append(match.group(1))

    names = theorem_names + api_names
    assert len(names) == len(set(names)), "duplicate retained declaration names"
    declared = {row["name"]: row for row in declarations}
    unknown = sorted(set(names) - set(declared))
    assert not unknown, ("stale retained declarations", unknown)

    non_theorems = sorted(name for name in theorem_names
                          if declared[name]["kind"] != "theorem")
    assert not non_theorems, ("non-theorems listed as retained theorems", non_theorems)
    wrong_other = sorted(name for name in api_names
                         if declared[name]["kind"] == "theorem")
    assert not wrong_other, ("theorems listed as other APIs", wrong_other)

    audit_names = {row["name"] for row in theorems if row["retainedMention"]}
    assert audit_names == set(theorem_names), (
        "retainedMention disagrees with the retained theorem list",
        sorted(audit_names - set(theorem_names)),
        sorted(set(theorem_names) - audit_names),
    )


def main():
    directory = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("docs/generated")
    declarations = json.loads((directory / "declarations.json").read_text(encoding="utf-8"))
    theorems = json.loads((directory / "theorems.json").read_text(encoding="utf-8"))
    validate(declarations, theorems)
    retained = Path("docs/theorem-catalog-retained.md").read_text(encoding="utf-8")
    validate_retained_catalog(retained, declarations, theorems)
    # Resolve the module through its source filename so moves do not weaken this acceptance check.
    rows = [row for row in declarations if row["sourceFile"].endswith("/MixedComponentCrossing.lean")
            and not row["generated"]]
    assert len(rows) == 2, "MixedComponentCrossing must contain two source declarations"
    assert {row["name"].split(".")[-1] for row in rows} == {
        "mixedComponentCrossingCount", "mixedComponentWeight"}
    assert all(row["kind"] == "def" for row in rows)
    assert all(row["dependencies"] for row in rows), "definitions must retain dependency edges"
    rows = [row for row in declarations if row["sourceFile"].endswith("/SchwartzTwoLevel1D.lean")
            and not row["generated"]]
    assert any(row["kind"] == "theorem" for row in rows), "missing SchwartzTwoLevel1D theorems"
    assert any(row["kind"] in {"def", "abbrev"} for row in rows), "missing SchwartzTwoLevel1D definitions"
    print(f"Validated {len(declarations)} declarations and {len(theorems)} theorem audit entries")


if __name__ == "__main__":
    main()
