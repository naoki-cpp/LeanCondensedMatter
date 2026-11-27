import tempfile
from pathlib import Path
import unittest

from check_documentation_links import missing_links


class DocumentationLinkTests(unittest.TestCase):
    def test_local_paths_and_external_exclusions(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "docs").mkdir()
            (root / "Lean").mkdir()
            (root / "Lean" / "Owner.lean").touch()
            (root / "docs" / "other file.md").touch()
            document = "\n".join([
                "[owner](../Lean/Owner.lean#L2)",
                "[root](/Lean/Owner.lean)",
                "[folder](../Lean/)",
                "[space](other%20file.md)",
                "[angle](<other file.md>)",
                "[title](../Lean/Owner.lean \"source\")",
                "[gone](../Lean/Old.lean)",
                "[gone reference]: ../Lean/Old.lean",
                "[web](https://example.com/missing)",
                "[mail](mailto:person@example.com)",
                "[anchor](#section)",
                "[escape](../../outside)",
                "![image](missing.png)",
            ])
            self.assertEqual(list(missing_links(root, Path("docs/example.md"), document)),
                             [(7, "../Lean/Old.lean"), (8, "../Lean/Old.lean"),
                              (12, "../../outside"), (13, "missing.png")])

    def test_code_examples_are_not_links(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            document = "\n".join([
                "\x60\x60\x60markdown",
                "[not a link](missing.md)",
                "\x60\x60\x60",
                "~~~",
                "[not a link](missing.md)",
                "~~~",
                "\x60[not a link](missing.md)\x60",
                "[\x60name\x60](missing.md)",
            ])
            self.assertEqual(list(missing_links(root, Path("example.md"), document)),
                             [(8, "missing.md")])


if __name__ == "__main__":
    unittest.main()
