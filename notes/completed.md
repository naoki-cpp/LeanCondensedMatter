# Completed

Major targets that have reached `proved` (compile with no `sorry`). Per-track roadmaps retain the
architectural context and later infinite-dimensional or convergence-aware extensions.

| Target | Track | Lean declaration(s) | Source |
|---|---|---|---|
| Continuous functional calculus acts on eigenvectors by evaluation | C | `Polynomial.aeval_apply_eigenvector`, `cfc_apply_eigenvector` | `LeanCondensedMatter/Analysis/FunctionalCalculus/CFC.lean` |
| Canonical density-state purity and finite-dimensional `Tr(ρ²)` formula | A/C | `QuantumTheory.purity`, `QuantumTheory.purity_nonneg`, `QuantumTheory.purity_le_one`, `QuantumTheory.purity_pure`, `QuantumTheory.DensityOperator.purity_eq_linearMap_trace_sq` | `LeanCondensedMatter/QuantumTheory/DensityOperator/Purity.lean`, `LeanCondensedMatter/QuantumTheory/FiniteDimensional/Purity.lean` |
| Explicit partition-lattice Möbius formula | B | `Finpartition.mu_bot_top_eq_factorial`, `Finpartition.mu_bot_top_eq_factorial_ite`, `Finpartition.mu_to_top_eq_factorial`, `Finpartition.mu_eq_prod_factorial` | `LeanCondensedMatter/Combinatorics/SetPartition/MobiusFormula.lean` |
| Finite-set moment–cumulant inversion | B | `Finpartition.momentFromCumulant_cumulantFromMoment`, `Finpartition.cumulantFromMoment_momentFromCumulant` | `LeanCondensedMatter/Combinatorics/MomentCumulant.lean` |
| Formal-log coefficient / finite-set cumulant bridge | B | `Combinatorics.factorial_mul_coeff_logOf_eq_cumulantFromMoment`, `Combinatorics.factorial_mul_coeff_logOf_eq_cumulantFromMoment_fin` | `LeanCondensedMatter/Combinatorics/PowerSeriesCumulant.lean` |
| Finite-temperature Bloch–de Dominicis pairing theorem | A/D | `SecondQuantization.Common.BlochDeDominicis.gibbsExpectation_prodComp_eq_sum_pairing` | `LeanCondensedMatter/SecondQuantization/Common/Thermal/BlochDeDominicis/Induction.lean` |
| Fermionic quartic Wick-amplitude factorization | D | `SecondQuantization.Fermionic.quarticWickDiagramAmplitude_eq_prod_restrictComponentConnected` | `LeanCondensedMatter/SecondQuantization/Fermionic/Diagrammatics/WickDiagram/AmplitudeFactorization.lean` |
| Connected-diagram formula for fermionic Dyson vertex cumulants | D | `SecondQuantization.Fermionic.dysonVertexCumulant_quarticInteraction_eq_sum_connectedQuarticWickDiagramAmplitude` | `LeanCondensedMatter/SecondQuantization/Fermionic/Diagrammatics/DysonConnectedDiagramExpansion.lean` |
| Fermionic Dyson Linked Cluster Theorem, finite-mode formal/algebraic form | Combined | `SecondQuantization.Fermionic.factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedAmplitude` | `LeanCondensedMatter/SecondQuantization/Fermionic/Diagrammatics/DysonLinkedClusterTheorem.lean` |
| Finite-dimensional fermionic Dyson series equals the interacting partition function | D | `SecondQuantization.Fermionic.hasSum_dysonTraceCoeff_eq_analyticDysonPartitionFunction`, `SecondQuantization.Fermionic.hasFPowerSeriesAt_analyticDysonPartitionFunction` | `LeanCondensedMatter/SecondQuantization/Fermionic/Perturbation/AnalyticDysonPartitionFunction.lean` |
| Analytic finite-dimensional fermionic Linked Cluster Theorem | Combined | `SecondQuantization.Fermionic.iteratedDeriv_log_normalizedAnalyticPartitionFunction_eq_sum_connectedAmplitude` | `LeanCondensedMatter/SecondQuantization/Fermionic/Perturbation/AnalyticLinkedClusterIdentification.lean` |
| Finite-mode fermionic two-point linked-cluster theorem | D | `SecondQuantization.Fermionic.vacuumNormalizedTwoPointDysonSeries_eq_connectedTwoPointDysonSeries` | `LeanCondensedMatter/SecondQuantization/Fermionic/Diagrammatics/TwoPointDiagramExpansion/CauchySeries.lean` |

The finite-mode fermionic line is complete through both the zero-external-leg/partition-function
linked-cluster theorem and the vacuum-normalized two-point series: the latter equals the formal series
formed from externally connected two-point diagrams. The analytic log-partition theorem additionally
identifies logarithmic derivatives of the genuine finite-dimensional interacting partition function
with connected quartic diagram amplitudes.

The completed fermionic free line also contains bounded completed CAR operators, explicit domains and
self-adjointness results for supported unbounded diagonal operators, summability-controlled free Gibbs
specializations, and finite-mode Gibbs convergence against bounded observables. Completed bosonic
operator-domain theory, interacting completed-space perturbation theory, thermodynamic limits, a
general non-self-adjoint trace-class ideal, and the convergence-aware bosonic Dyson line remain
separate targets.
