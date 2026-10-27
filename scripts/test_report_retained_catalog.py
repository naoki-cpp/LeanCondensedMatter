import json
import tempfile
import unittest
from pathlib import Path

from report_retained_catalog import audit, load_optional_baseline, markdown


def sample(name, **overrides):
    row = dict(
        name=name, retainedMention=True, terminal=False, compiledConsumerCount=1,
        directWrapperOf=None, statement="P", module="LeanCondensedMatter.Test",
        compiledConsumers=["T"], simpLemma=False, projectAxioms=[], externalAxioms=[],
    )
    row.update(overrides)
    row.setdefault(
        "retainedNeedsReview",
        bool(row["retainedMention"] and (
            row["terminal"] or row["compiledConsumerCount"] <= 1 or row["directWrapperOf"]
        )),
    )
    return row


class RetainedReportTests(unittest.TestCase):
    def test_current_queues_are_not_deletion_decisions(self):
        current = [
            sample("a", compiledConsumerCount=3, compiledConsumers=["A", "B", "C"]),
            sample("b", compiledConsumerCount=0, compiledConsumers=[], terminal=True, directWrapperOf="x"),
            sample("c", retainedMention=False),
        ]
        report = audit(current)
        self.assertEqual(report["retainedCount"], 2)
        self.assertEqual(report["withoutStructuralSignal"], ["a"])
        self.assertEqual(report["zeroConsumerDirectWrappers"], ["b"])
        self.assertFalse(report["baselineAvailable"])
        self.assertEqual(report["retainedReplacementCandidates"], [])
        self.assertIn("Snapshot comparison unavailable", markdown(report))

    def test_diff_compares_evidence_and_tracks_retained_changes(self):
        previous = [
            sample("a", compiledConsumerCount=1),
            sample("b", compiledConsumerCount=0, compiledConsumers=[], terminal=True),
            sample("retired"),
        ]
        current = [
            sample("a", compiledConsumerCount=2, compiledConsumers=["T", "U"], simpLemma=True),
            sample("b", compiledConsumerCount=0, compiledConsumers=[], terminal=True),
            sample("new"),
        ]
        report = audit(current, previous)
        self.assertTrue(report["baselineAvailable"])
        self.assertEqual(report["newlyWithoutStructuralSignal"], ["a"])
        self.assertEqual(report["newlyRetained"], ["new"])
        self.assertEqual(report["noLongerRetained"], ["retired"])
        self.assertEqual(report["changedReviewEvidence"], [
            {"name": "a", "fields": ["compiledConsumers", "simpLemma"]},
        ])
        self.assertIn("Since the last published graph-data snapshot", markdown(report))

    def test_retained_mathlib_replacement_candidates_remain_visible(self):
        previous = [sample("a", mathlibReplacementCandidates=[])]
        current = [sample("a", mathlibReplacementCandidates=["Mathlib.foo"])]
        report = audit(current, previous)
        self.assertEqual(report["retainedReplacementCandidates"], [
            {"name": "a", "candidates": {
                "mathlibReplacementCandidates": ["Mathlib.foo"],
            }},
        ])
        self.assertEqual(report["changedReviewEvidence"], [
            {"name": "a", "fields": ["mathlibReplacementCandidates"]},
        ])
        self.assertIn("Mathlib.foo", markdown(report))

    def test_new_retained_is_not_mistaken_for_lost_signal(self):
        previous = [sample("old", compiledConsumerCount=1)]
        current = [
            sample("old", compiledConsumerCount=3),
            sample("new", compiledConsumerCount=3),
        ]
        report = audit(current, previous)
        self.assertEqual(report["newlyRetained"], ["new"])
        self.assertEqual(report["newlyWithoutStructuralSignal"], ["old"])

    def test_structural_signal_uses_compiled_catalog_attribute(self):
        report = audit([sample("a", compiledConsumerCount=0, retainedNeedsReview=False)])
        self.assertEqual(report["withoutStructuralSignal"], ["a"])
        self.assertEqual(report["structuralReauditCount"], 0)

    def test_invalid_baseline_does_not_block_current_report(self):
        with tempfile.TemporaryDirectory() as directory:
            baseline = Path(directory) / "previous.json"
            baseline.write_text("{invalid", encoding="utf-8")
            self.assertIsNone(load_optional_baseline(baseline))
            self.assertFalse(audit([sample("a")], load_optional_baseline(baseline))["baselineAvailable"])
            baseline.write_text(json.dumps([{"name": "a", "retainedMention": True}]),
                                encoding="utf-8")
            self.assertIsNone(load_optional_baseline(baseline))

    def test_current_summary_does_not_claim_historical_change(self):
        self.assertNotIn("No longer carrying", markdown(audit([sample("a")])))

    def test_duplicate_names_rejected(self):
        with self.assertRaisesRegex(ValueError, "duplicate"):
            audit([sample("a"), sample("a")])
        with self.assertRaisesRegex(ValueError, "duplicate"):
            audit([sample("a")], [sample("b"), sample("b")])


if __name__ == "__main__":
    unittest.main()
