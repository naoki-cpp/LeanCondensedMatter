# Completed

Major targets that have reached `proved` (compile with no `sorry`). Per-track roadmaps retain the
architectural context and later analytic extensions.

| Target | Track | Lean declaration(s) | Source |
|---|---|---|---|
| Continuous functional calculus acts on eigenvectors by evaluation | C | `Polynomial.aeval_apply_eigenvector`, `cfc_apply_eigenvector` | `LeanCondensedMatter/Analysis/CFC.lean` |
| Finite-set moment–cumulant inversion | B | `Finpartition.momentFromCumulant_cumulantFromMoment`, `Finpartition.cumulantFromMoment_momentFromCumulant` | `LeanCondensedMatter/Combinatorics/MomentCumulant.lean` |
| Formal-log coefficient / finite-set cumulant bridge | B | `Combinatorics.factorial_mul_coeff_logOf_eq_cumulantFromMoment`, `Combinatorics.factorial_mul_coeff_logOf_eq_cumulantFromMoment_fin` | `LeanCondensedMatter/Combinatorics/PowerSeriesCumulant.lean` |
| Finite-temperature Bloch–de Dominicis pairing theorem | A/D | `Common.gibbsExpectation_prodComp_eq_sum_pairing` | `LeanCondensedMatter/SecondQuantization/Common/Thermal/BlochDeDominicis/Induction.lean` |
| Fermionic quartic Wick-amplitude factorization | D | `SecondQuantization.quarticWickDiagramAmplitude_eq_prod_restrictComponentConnected` | `LeanCondensedMatter/SecondQuantization/Fermionic/Diagrammatics/WickDiagram/AmplitudeFactorization.lean` |
| Connected-diagram formula for fermionic Dyson vertex cumulants | D | `SecondQuantization.dysonVertexCumulant_quarticInteraction_eq_sum_connectedQuarticWickDiagramAmplitude` | `LeanCondensedMatter/SecondQuantization/Fermionic/Diagrammatics/DysonConnectedDiagramExpansion.lean` |
| Fermionic Dyson Linked Cluster Theorem, finite-mode formal/algebraic form | Combined | `SecondQuantization.factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedAmplitude` | `LeanCondensedMatter/SecondQuantization/Fermionic/Diagrammatics/DysonLinkedClusterTheorem.lean` |

The completed fermionic LCT is coefficientwise and formal. Convergence, equality with an analytic
interacting partition function, thermodynamic limits, and completed-space unbounded-operator theory
remain separate targets.
