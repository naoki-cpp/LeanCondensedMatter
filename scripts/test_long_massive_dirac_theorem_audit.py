"""Focused tests for the advisory long-name MassiveDirac inventory."""
import unittest

from audit_long_massive_dirac_theorems import (
    CONSOLIDATION_REVIEW,
    PRESERVE_ENDPOINTS,
    inventory,
)


def fixture(name, *, module="LeanCondensedMatter.Models.MassiveDirac.Disorder.Fixture",
            consumers=0, simp=False, retained=False):
    return {
        "name": name, "module": module,
        "compiledConsumerCount": consumers,
        "simpLemma": simp,
        "retainedMention": retained,
    }


class MassiveDiracLongNameAuditTests(unittest.TestCase):
    def test_filters_compiled_zero_consumer_and_public_project_scope(self):
        base = "QuantumTheory.Models.MassiveDirac."
        long = base + "long_named_lemma_with_many_components_and_conditions"
        other = base + "other_long_named_lemma_with_many_components_and_conditions"
        result = inventory([
            fixture(long),
            fixture(other, consumers=1),
            fixture("_private.SomePath.0." + long),
            fixture("OtherNamespace." + long),
            fixture(base + "short"),
            fixture(long, module="LeanCondensedMatter.Models.RashbaExchange.Other"),
        ], min_length=60)
        self.assertEqual([row["name"] for row in result], [long])
        self.assertEqual(result[0]["triage"], "semantic_review")

    def test_triage_is_advisory_and_simp_takes_precedence(self):
        endpoint = next(iter(PRESERVE_ENDPOINTS))
        candidate = next(iter(CONSOLIDATION_REVIEW))
        rows = inventory([
            fixture(endpoint),
            fixture(candidate),
            fixture("QuantumTheory.Models.MassiveDirac.long_enough_normalization_lemma",
                    simp=True),
            fixture("QuantumTheory.Models.MassiveDirac.long_enough_retained_lemma",
                    retained=True),
        ], min_length=60)
        dispositions = {row["name"]: row["triage"] for row in rows}
        self.assertEqual(dispositions[endpoint], "preserve_endpoint")
        self.assertEqual(dispositions[candidate], "consolidation_review")
        self.assertEqual(dispositions[
            "QuantumTheory.Models.MassiveDirac.long_enough_normalization_lemma"
        ], "preserve_simp")
        self.assertEqual(dispositions[
            "QuantumTheory.Models.MassiveDirac.long_enough_retained_lemma"
        ], "preserve_registry")

    def test_descending_length_then_name(self):
        base = "QuantumTheory.Models.MassiveDirac."
        names = [base + "z_aa", base + "a_aa", base + "longer"]
        rows = inventory([fixture(name) for name in names], min_length=0)
        self.assertEqual([row["name"] for row in rows],
                         [base + "longer", base + "a_aa", base + "z_aa"])


if __name__ == "__main__":
    unittest.main()
