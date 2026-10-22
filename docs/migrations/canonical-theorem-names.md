# Canonical theorem-name migration

Major public theorem names were aligned with their mathematical conclusions. No compatibility aliases are kept; downstream code should migrate directly to the canonical declarations below.

| Previous declaration | Canonical declaration |
|---|---|
| `SecondQuantization.Common.QuarticDiagram.dysonSign_mul_vertexWeight_eq_prod_restrictComponentConnected` | `SecondQuantization.Common.QuarticDiagram.dysonSign_mul_vertexWeight_eq_prod_components` |
| `SecondQuantization.Fermionic.quarticWickDiagramAmplitude_eq_prod_restrictComponentConnected` | `SecondQuantization.Fermionic.quarticWickDiagramAmplitude_eq_prod_components` |
| `SecondQuantization.Fermionic.hasSum_dysonTraceCoeff_eq_analyticDysonPartitionFunction` | `SecondQuantization.Common.hasSum_dysonTraceCoeff_analyticDysonPartitionFunction` |
| `SecondQuantization.Fermionic.factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedAmplitude` | `SecondQuantization.Fermionic.factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedQuarticWickDiagramAmplitude` |
| `SecondQuantization.Fermionic.iteratedDeriv_log_normalizedAnalyticPartitionFunction_eq_sum_connectedAmplitude` | `SecondQuantization.Fermionic.iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_sum_connectedQuarticWickDiagramAmplitude` |
| `SecondQuantization.Fermionic.twoPointDysonCoefficient_eq_sum_connected_mul_normalizedDysonPartitionCoeff` | `SecondQuantization.Fermionic.twoPointDysonCoefficient_eq_sum_connectedTwoPointDysonCoefficient_mul_normalizedDysonPartitionCoeff` |

The changes are naming/API migrations only: they do not introduce alternative mathematical statements. The new names make connected-component factorization, `HasSum` propositions, and the concrete connected Wick amplitude visible from the declaration names themselves.
