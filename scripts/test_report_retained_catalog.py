import json
import tempfile
import unittest
from pathlib import Path

from report_retained_catalog import compare, load_baseline, markdown


def row(name, retained=True, signal=True, **extra):
    return {"name": name, "retainedMention": retained, "retainedNeedsReview": signal,
            "statement": "P", **extra}


class RetainedDriftTests(unittest.TestCase):
    def test_detects_changes_not_current_queues(self):
        old = [row("a"), row("b"), row("retired")]
        now = [row("a", signal=False, statement="Q"), row("b"), row("new", signal=False)]
        result = compare(now, old)
        self.assertEqual(result["lostStructuralSignal"], ["a"])
        self.assertEqual(result["newlyRetained"], ["new"])
        self.assertEqual(result["noLongerRetained"], ["retired"])
        self.assertEqual(result["changedReviewEvidence"], [{
            "name": "a", "fields": ["statement", "retainedNeedsReview"]}])

    def test_missing_baseline_has_no_fake_deltas(self):
        report = compare([row("a")], None)
        self.assertFalse(report["baselineAvailable"])
        self.assertEqual(report["lostStructuralSignal"], [])
        self.assertIn("No compatible baseline", markdown(report))

    def test_invalid_baseline_is_advisory(self):
        with tempfile.TemporaryDirectory() as temp:
            file = Path(temp) / "theorems.json"
            file.write_text("broken", encoding="utf-8")
            self.assertIsNone(load_baseline(file))
            file.write_text(json.dumps([{"name": "a", "retainedMention": True}]),
                            encoding="utf-8")
            self.assertIsNone(load_baseline(file))
            file.write_text(json.dumps([row("a")]), encoding="utf-8")
            self.assertEqual(load_baseline(file), [row("a")])


if __name__ == "__main__":
    unittest.main()
