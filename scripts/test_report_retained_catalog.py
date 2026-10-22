import unittest
from report_retained_catalog import audit, markdown


def sample(name, **overrides):
    row = dict(
        name=name, retainedMention=True, terminal=False, compiledConsumerCount=1,
        directWrapperOf=None, statement="P", module="LeanCondensedMatter.Test",
        compiledConsumers=["T"], simpLemma=False, projectAxioms=[], externalAxioms=[],
    )
    row.update(overrides)
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

    def test_duplicate_names_rejected(self):
        with self.assertRaisesRegex(ValueError, "duplicate"):
            audit([sample("a"), sample("a")])
        with self.assertRaisesRegex(ValueError, "duplicate"):
            audit([sample("a")], [sample("b"), sample("b")])


if __name__ == "__main__":
    unittest.main()
