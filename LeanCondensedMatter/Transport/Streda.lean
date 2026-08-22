import LeanCondensedMatter.Transport.StredaOperatorKernel
import LeanCondensedMatter.Transport.StredaTraceKernel
import LeanCondensedMatter.Transport.StredaIntegration
import LeanCondensedMatter.Transport.GeneralizedStaticStreda
import LeanCondensedMatter.Transport.StredaTraceSpectral
import LeanCondensedMatter.Transport.StredaTraceRepresentation
import LeanCondensedMatter.Transport.StredaSpectralEnergyIntegral

set_option linter.style.header false

/-!
# Středa transport API

Public umbrella for the generic finite regularized Středa layer: operator and trace kernels,
integration, generalized static decomposition, pure-point spectral expansion, trace representation,
and spectral energy integration.

Concrete anomalous-Hall models are downstream specializations of this API.
-/
