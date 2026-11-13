"""Regression checks for source-graph import-footprint accounting."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from export_module_import_graph import project_import_footprint


def entry(name: str, imports: list[str], external_count: int = 0) -> dict[str, object]:
    return {
        "name": name,
        "imports": imports,
        "sourceFile": name.replace(".", "/") + ".lean",
        "externalImportCount": external_count,
    }


class ImportFootprintTests(unittest.TestCase):
    def setUp(self) -> None:
        # A diamond: Root reaches Shared through both A and B, but Shared is
        # counted only once. Leaf is deliberately independent of the root.
        self.modules = [
            entry("L.Root", ["L.A", "L.B"], 1),
            entry("L.A", ["L.Shared"], 2),
            entry("L.B", ["L.Shared"], 3),
            entry("L.Shared", [], 4),
            entry("L.Leaf", [], 5),
        ]

    def test_diamond_counts_distinct_project_modules(self) -> None:
        self.assertEqual(
            project_import_footprint(self.modules, "L.Root"),
            {
                "directProjectImports": 2,
                "projectModules": 4,
                "externalDirectImportEdges": 10,
            },
        )

    def test_focused_entry_is_not_merged_with_baseline(self) -> None:
        self.assertEqual(
            project_import_footprint(self.modules, "L.A"),
            {
                "directProjectImports": 1,
                "projectModules": 2,
                "externalDirectImportEdges": 6,
            },
        )
        self.assertEqual(
            project_import_footprint(self.modules, "L.Leaf"),
            {
                "directProjectImports": 0,
                "projectModules": 1,
                "externalDirectImportEdges": 5,
            },
        )

    def test_unknown_root_is_an_error(self) -> None:
        with self.assertRaisesRegex(ValueError, "unknown project module"):
            project_import_footprint(self.modules, "L.Unknown")

    def test_missing_imported_module_is_an_error(self) -> None:
        with self.assertRaisesRegex(ValueError, "missing imported project module"):
            project_import_footprint([entry("L.Root", ["L.Missing"])], "L.Root")

    def test_visited_set_guards_against_graph_cycle(self) -> None:
        graph = [entry("L.A", ["L.B"]), entry("L.B", ["L.A"])]
        self.assertEqual(project_import_footprint(graph, "L.A")["projectModules"], 2)


if __name__ == "__main__":
    unittest.main()
