import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.FreeTwoPointCoefficient
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.ParticleNumberWeightSummable
import LeanCondensedMatter.SecondQuantization.Bosonic.BlochDeDominicis.TwoPoint

set_option linter.style.header false

/-!
# Bosonic thermal theory

Public umbrella for the convergence-aware free bosonic thermal layer:

- one- and multi-mode Boltzmann weights;
- partition-series and particle-number-weighted summability;
- free two-point basis coefficients;
- the uncutoff bosonic two-point specialization of the Common Bloch–de Dominicis framework.

General Gibbs expectations of arbitrary operators and interacting Dyson/Wick expansions remain outside
this module because they require additional summability-aware operator interfaces.
-/
