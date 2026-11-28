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
        assert isinstance(row["projection"], bool)
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



def validate_completed_catalog(document, declarations):
    """Check completed table declaration names and their owning source files."""
    declared = {row["name"]: row for row in declarations if not row["generated"]}
    header = "| Target | Track | Lean declaration(s) | Source |"
    assert document.count(header) == 1, "missing or duplicate completed table"
    rows = document.split(header, 1)[1].splitlines()[2:]
    count = 0
    for line in rows:
        if not line.startswith("|"):
            break
        columns = line.strip("|").split("|")
        assert len(columns) == 4, ("invalid completed row", line)
        names, sources = (re.findall(r"`([^`]+)`", column) for column in columns[2:])
        assert names and sources, ("missing completed declarations or sources", line)
        assert len(names) == len(set(names)) and len(sources) == len(set(sources)), (
            "duplicate completed declaration or source", line)
        unknown = sorted(set(names) - set(declared))
        assert not unknown, ("stale completed declarations", unknown)
        actual_sources = {declared[name]["sourceFile"] for name in names}
        assert actual_sources == set(sources), (
            "completed declaration source mismatch", names,
            sorted(actual_sources), sorted(sources))
        count += 1
    assert count, "empty completed table"


def validate_retained_catalog(document, declarations, theorems):
    """Check all retained names against compiled declarations, not source-text matches."""
    theorem_header = "## Retained declarations\n"
    other_header = "## Other retained API contracts (outside theorem audit)\n"
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

    invalid_theorems = sorted(name for name in theorem_names
                              if declared[name]["kind"] != "theorem" or
                              declared[name]["projection"])
    assert not invalid_theorems, ("non-auditable retained theorem entries", invalid_theorems)
    # Lean stores proof-valued structure fields as theorem-kind projections. They are
    # structural APIs, not independently audited theorem declarations.
    wrong_other = sorted(name for name in api_names
                         if declared[name]["kind"] == "theorem" and
                         not declared[name]["projection"])
    assert not wrong_other, ("non-projection theorems listed as other APIs", wrong_other)

    audit_names = {row["name"] for row in theorems if row["retainedMention"]}
    assert audit_names == set(theorem_names), (
        "retainedMention disagrees with the retained theorem list",
        sorted(audit_names - set(theorem_names)),
        sorted(set(theorem_names) - audit_names),
    )



def validate_reviewed_definition_bodies(declarations):
    """Check the compiled pilot selection and lexical scope of structured body nodes."""
    expected = {
        "QuantumTheory.Transport.IsSelfEnergy",
        "QuantumTheory.Transport.spectralParameterOfRegulator",
        "QuantumTheory.ConservationLaw.heisenbergScale",
        "Finpartition.partitionProduct",
        "Finpartition.weightedMomentFromCumulant",
    }
    bodies = {
        row["name"]: row for row in declarations
        if (row.get("structuredStatement") or {}).get("definitionBody") is not None
    }
    assert set(bodies) == expected, ("reviewed body selection mismatch",
                                     sorted(expected - set(bodies)),
                                     sorted(set(bodies) - expected))

    def visit(node, scope):
        assert isinstance(node, dict), ("invalid presentation node", node)
        kind = node["kind"]
        if kind == "var":
            assert node["id"] in scope, ("unbound variable in definition body", node)
        elif kind == "lambda":
            binder = node["binder"]
            assert binder["id"] not in scope, ("duplicate lambda ID", binder)
            visit(binder["type"], scope)
            visit(node["body"], scope | {binder["id"]})
        elif kind == "app":
            visit(node["fn"], scope)
            for argument in node["args"]:
                visit(argument, scope)
        else:
            assert kind in {"const", "sort", "text"}, ("unknown presentation node", kind)

    for name, row in bodies.items():
        assert row["kind"] in {"def", "abbrev"} and not row["generated"], name
        presentation = row["structuredStatement"]
        body = presentation["definitionBody"]
        assert isinstance(body.get("text"), str) and body["text"].strip(), name
        visit(body, {binder["id"] for binder in presentation["binders"]})
    print(f"Validated {len(bodies)} reviewed definition bodies")

def main():
    directory = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("docs/generated")
    declarations = json.loads((directory / "declarations.json").read_text(encoding="utf-8"))
    theorems = json.loads((directory / "theorems.json").read_text(encoding="utf-8"))
    validate(declarations, theorems)
    validate_reviewed_definition_bodies(declarations)
    completed = Path("docs/completed.md").read_text(encoding="utf-8")
    validate_completed_catalog(completed, declarations)
    retained = Path("docs/theorem-catalog-retained.md").read_text(encoding="utf-8")
    validate_retained_catalog(retained, declarations, theorems)
    # Check the actual general mixed-component APIs after retiring the two-point-only module.
    expected = {"componentMixedPosition", "componentMixedPositionEquiv"}
    rows = [row for row in declarations
            if row["sourceFile"].endswith("/ExternalInsertion/Components/MixedOrderData.lean")
            and not row["generated"] and row["name"].split(".")[-1] in expected]
    assert len(rows) == len(expected), "missing general mixed-component definitions"
    assert {row["name"].split(".")[-1] for row in rows} == expected
    assert all(row["kind"] == "def" for row in rows)
    assert all(row["dependencies"] for row in rows), "definitions must retain dependency edges"
    rows = [row for row in declarations if row["sourceFile"].endswith("/SchwartzComponents1D.lean")
            and not row["generated"]]
    assert any(row["kind"] == "theorem" for row in rows), "missing SchwartzComponents1D theorems"
    assert any(row["kind"] in {"def", "abbrev"} for row in rows), "missing SchwartzComponents1D definitions"
    print(f"Validated {len(declarations)} declarations and {len(theorems)} theorem audit entries")


if __name__ == "__main__":
    main()
