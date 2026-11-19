# Completed

Selected targets with kernel-checked implementations. See the roadmaps for hypotheses and
unproved generalizations; in particular, the bosonic Dyson endpoint is coefficientwise formal.

| Target | Track | Lean declaration(s) | Source |
|---|---|---|---|
| Continuous functional calculus acts on eigenvectors by evaluation | C | `cfc_apply_eigenvector` | `LeanCondensedMatter/Analysis/FunctionalCalculus/CFC.lean` |
| Canonical density-state purity, maximal-purity characterization, and finite-dimensional `Tr(ρ²)` formula | A/C | `QuantumTheory.purity`, `QuantumTheory.purity_nonneg`, `QuantumTheory.purity_le_one`, `QuantumTheory.purity_pure`, `QuantumTheory.isPureDensity_iff_purity_eq_one`, `QuantumTheory.DensityOperator.linearMap_trace_sq_eq_purity` | `LeanCondensedMatter/QuantumTheory/DensityOperator/Purity.lean`, `LeanCondensedMatter/QuantumTheory/DensityOperator/Finite.lean` |
| Explicit partition-lattice Möbius formula | B | `Finpartition.mu_bot_top_eq_factorial`, `Finpartition.mu_bot_top_eq_factorial_ite`, `Finpartition.mu_to_top_eq_factorial`, `Finpartition.mu_eq_prod_factorial` | `LeanCondensedMatter/Combinatorics/SetPartition/MobiusFormula.lean` |
| Finite-set moment–cumulant inversion | B | `Finpartition.momentFromCumulant_cumulantFromMoment`, `Finpartition.cumulantFromMoment_momentFromCumulant` | `LeanCondensedMatter/Combinatorics/Cumulant/Inversion.lean` |
| Formal-log coefficient / finite-set cumulant bridge | B | `Combinatorics.factorial_mul_coeff_logOf_eq_cumulantFromMoment` | `LeanCondensedMatter/Analysis/PowerSeries/Cumulant.lean` |
| Formal-log coefficient / connected-decomposition bridge | B/C | `Combinatorics.factorial_mul_coeff_logOf_eq_connectedContribution` | `LeanCondensedMatter/Analysis/PowerSeries/Cumulant.lean` |
| Replica-method formal-log / connected-decomposition bridge | B/C | `Combinatorics.factorial_mul_coeff_logOf_eq_connectedContribution_replica` | `LeanCondensedMatter/Analysis/PowerSeries/ReplicaBridge.lean` |
| Infinite-dimensional pure-point Gibbs density | A/C | `QuantumTheory.eigenbasisGibbsDensityOperator` | `LeanCondensedMatter/QuantumTheory/Gibbs/Eigenbasis.lean` |
| Completed free-boson heat-operator trace class under Gibbs summability | C/D | `SecondQuantization.Bosonic.completedFreeHeatOperator_isTraceClass`, `SecondQuantization.Bosonic.completedFreeHeatOperator_trace_eq_grandCanonicalPartitionFunction_zero` | `LeanCondensedMatter/SecondQuantization/Bosonic/Thermal/Completed/FreeGibbs.lean` |
| Bosonic finite-order quartic Dyson formal linked-cluster theorem | D | `SecondQuantization.Bosonic.factorial_mul_coeff_logOf_grandCanonicalGibbsDysonSeries_eq_sum_connectedDysonThermalAmplitude` | `LeanCondensedMatter/SecondQuantization/Bosonic/Diagrammatics/Quartic/Thermal/DysonLinkedCluster.lean` |
| Finite-temperature Bloch–de Dominicis pairing theorem | A/D | `SecondQuantization.Common.BlochDeDominicis.finiteGibbsExpectation_prod_eq_sum_pairing` | `LeanCondensedMatter/SecondQuantization/Common/Thermal/BlochDeDominicis/GibbsExpectation/Recursion.lean` |
| Fermionic quartic Wick-amplitude factorization | D | `SecondQuantization.Fermionic.quarticWickDiagramAmplitude_eq_prod_components` | `LeanCondensedMatter/SecondQuantization/Fermionic/Diagrammatics/Quartic/Wick/AmplitudeFactorization.lean` |
| Fermionic Dyson Linked Cluster Theorem, finite-mode formal/algebraic form via replica bridge | Combined | `SecondQuantization.Fermionic.factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedQuarticWickDiagramAmplitude` | `LeanCondensedMatter/SecondQuantization/Fermionic/Diagrammatics/LinkedCluster/Theorem.lean` |
| Finite-configuration Dyson series equals the interacting partition function | D | `SecondQuantization.Common.hasSum_dysonTraceCoeff_analyticDysonPartitionFunction`, `SecondQuantization.Common.hasFPowerSeriesAt_analyticDysonPartitionFunction` | `LeanCondensedMatter/SecondQuantization/Common/Perturbation/AnalyticDysonPartitionFunction.lean` |
| Analytic finite-dimensional fermionic Linked Cluster Theorem | Combined | `SecondQuantization.Fermionic.iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_sum_connectedQuarticWickDiagramAmplitude` | `LeanCondensedMatter/SecondQuantization/Fermionic/Diagrammatics/LinkedCluster/Analytic.lean` |
| Finite-mode fermionic two-point linked-cluster theorem | D | `SecondQuantization.Fermionic.partitionFunctionNormalizedTwoPointDysonSeries_eq_connectedTwoPointDysonSeries` | `LeanCondensedMatter/SecondQuantization/Fermionic/Diagrammatics/TwoPointDiagramExpansion/Series/CauchySeries.lean` |

For assumptions and open extensions, see the [linked-cluster roadmap](roadmaps/linked-cluster-theorem.md)
and [completed-space boundary](roadmaps/completed-space-and-infinite-mode.md).
