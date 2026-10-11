import copy
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from check_declaration_catalog import validate
from generate_declaration_catalog import collector_source, generate
from export_module_import_graph import export_modules


def fixture():
    rows = []
    # Both directions across theorem/definition boundaries and both reference categories.
    for name, kind, types, values in [
        ("a", "theorem", ["b"], ["c"]),
        ("b", "def", ["c"], ["d"]),
        ("c", "theorem", [], ["d"]),
        ("d", "def", [], []),
    ]:
        rows.append(dict(name=name, module="LeanCondensedMatter.Fixture", kind=kind,
                         generated=False, sourceFile="LeanCondensedMatter/Fixture.lean",
                         sourceLine=1, sourceColumn=0, statement="Nat",
                         typeDependencies=types, valueDependencies=values,
                         dependencies=sorted(set(types + values)), dependents=[]))
    for row in rows:
        row["dependents"] = sorted(other["name"] for other in rows
                                   if row["name"] in other["dependencies"])
    return rows


class CatalogTests(unittest.TestCase):
    def test_explorer_imports_every_source_module(self):
        root = Path(__file__).resolve().parents[1]
        source = (root / "scripts/TheoremCatalog.lean").read_text(encoding="utf-8")
        modules = [row["name"] for row in export_modules()["modules"]]
        expanded = collector_source(source, modules)
        imports = {line.removeprefix("import ") for line in expanded.splitlines()
                   if line.startswith("import ")}
        self.assertTrue(set(modules) <= imports)
        self.assertIn("LeanCondensedMatter.Analysis.Operator.SchwartzTwoLevel1D", imports)
        # The legacy collector must retain its public-umbrella import boundary.
        self.assertNotIn("import LeanCondensedMatter.Analysis.Operator.SchwartzTwoLevel1D\n", source)

    def test_full_collection_preserves_the_legacy_audit(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "scripts").mkdir()
            (root / "scripts/TheoremCatalog.lean").write_text("import LeanCondensedMatter\n", encoding="utf-8")
            audit = root / "theorems.json"
            audit.write_bytes(b'[{"name":"legacy","terminal":true}]')
            calls = []

            def run(command, **kwargs):
                mode = kwargs.get("env", {}).get("LCM_CATALOG_MODE")
                calls.append((command, mode))
                self.assertTrue(kwargs["check"])
                if mode == "declarations":
                    source = (root / command[-1]).read_text(encoding="utf-8")
                    self.assertIn("import LeanCondensedMatter.Unexported\n", source)
                    self.assertEqual(audit.read_bytes(), b'[{"name":"legacy","terminal":true}]')

            with patch("generate_declaration_catalog.ROOT", root), \
                 patch("generate_declaration_catalog.export_modules", return_value={"modules": [
                     {"name": "LeanCondensedMatter"}, {"name": "LeanCondensedMatter.Unexported"}]}), \
                 patch("generate_declaration_catalog.subprocess.run", side_effect=run):
                generate()
            self.assertEqual([mode for _, mode in calls], ["audit", None, "declarations"])
            self.assertEqual(calls[1][0], ["lake", "build", "+LeanCondensedMatter", "+LeanCondensedMatter.Unexported"])
            self.assertEqual(list((root / "scripts").iterdir()), [root / "scripts/TheoremCatalog.lean"])

    def test_all_four_dependency_directions(self):
        validate(fixture(), [])

    def test_rejects_dangling_and_asymmetric_edges(self):
        for key in ("dependencies", "dependents", "typeDependencies"):
            rows = fixture()
            rows[0][key] = ["missing"]
            with self.assertRaises(AssertionError):
                validate(rows, [])

    def test_audit_attributes_are_preserved(self):
        rows = fixture()
        rows[0]["terminal"] = True
        audit = dict(name="a", kind="theorem", terminal=True,
                     dependencies=["c"], dependents=[])
        validate(rows, [audit])
        changed = copy.deepcopy(rows)
        changed[0]["terminal"] = False
        with self.assertRaises(AssertionError):
            validate(changed, [audit])


if __name__ == "__main__":
    unittest.main()
