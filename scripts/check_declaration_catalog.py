"""Validate compiled declaration graph and the unchanged theorem audit projection."""
import json
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


def main():
    directory = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("docs/generated")
    declarations = json.loads((directory / "declarations.json").read_text(encoding="utf-8"))
    theorems = json.loads((directory / "theorems.json").read_text(encoding="utf-8"))
    validate(declarations, theorems)
    # Resolve the module through its source filename so moves do not weaken this acceptance check.
    rows = [row for row in declarations if row["sourceFile"].endswith("/MixedComponentCrossing.lean")
            and not row["generated"]]
    assert len(rows) == 2, "MixedComponentCrossing must contain two source declarations"
    assert {row["name"].split(".")[-1] for row in rows} == {
        "mixedComponentCrossingCount", "mixedComponentWeight"}
    assert all(row["kind"] == "def" for row in rows)
    assert all(row["dependencies"] for row in rows), "definitions must retain dependency edges"
    print(f"Validated {len(declarations)} declarations and {len(theorems)} theorem audit entries")


if __name__ == "__main__":
    main()
