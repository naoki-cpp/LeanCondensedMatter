"""Tests for advisory project-local import overlap detection."""

import unittest

from export_module_import_graph import import_overlap_candidates


def entry(name: str, *imports: str) -> dict[str, object]:
    return {
        "name": name,
        "sourceFile": name.replace(".", "/") + ".lean",
        "imports": list(imports),
    }


class ImportOverlapTests(unittest.TestCase):
    def test_diamond_detects_transitive_overlap(self) -> None:
        modules = [
            entry("LCM.A", "LCM.B", "LCM.C"),
            entry("LCM.B", "LCM.C"),
            entry("LCM.C"),
        ]
        self.assertEqual(
            import_overlap_candidates(modules),
            [("LCM/A.lean", "LCM.C", "LCM.B")],
        )

    def test_independent_direct_imports_do_not_overlap(self) -> None:
        modules = [
            entry("LCM.A", "LCM.B", "LCM.C"),
            entry("LCM.B"),
            entry("LCM.C"),
        ]
        self.assertEqual(import_overlap_candidates(modules), [])

    def test_cycles_terminate_without_claiming_removability(self) -> None:
        modules = [
            entry("LCM.A", "LCM.B", "LCM.C"),
            entry("LCM.B", "LCM.C"),
            entry("LCM.C", "LCM.B"),
        ]
        self.assertEqual(
            import_overlap_candidates(modules),
            [
                ("LCM/A.lean", "LCM.B", "LCM.C"),
                ("LCM/A.lean", "LCM.C", "LCM.B"),
            ],
        )


if __name__ == "__main__":
    unittest.main()
