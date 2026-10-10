import copy
import unittest

from check_declaration_catalog import validate


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
