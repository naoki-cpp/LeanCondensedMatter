import LeanCondensedMatter.Transport.Streda.StaticChannelIdentification
import LeanCondensedMatter.Transport.Streda.OperatorKernel
import LeanCondensedMatter.Transport.Streda.TraceKernel
import LeanCondensedMatter.Transport.Streda.RetardedAdvanced
import LeanCondensedMatter.Transport.Streda.Integration
import LeanCondensedMatter.Transport.Streda.GeneralizedStatic
import LeanCondensedMatter.Transport.Streda.ResponseMatrix
import LeanCondensedMatter.Transport.Streda.TraceSpectral
import LeanCondensedMatter.Transport.Streda.TraceRepresentation
import LeanCondensedMatter.Transport.Streda.ResponseMatrixRepresentation
import LeanCondensedMatter.Transport.Streda.SpectralEnergyIntegral
import LeanCondensedMatter.Transport.Streda.ConductivityNormalization
import LeanCondensedMatter.Transport.Streda.InterbandPole
import LeanCondensedMatter.Transport.Streda.FiniteProjectorBastin

set_option linter.style.header false

/-!
# Středa transport

Regularized operator and trace kernels, retarded–advanced algebra, spectral and energy-integral
representations, generalized static response and conductivity tensors, conditional static-channel
identification, and isolated interband pole limits.
-/
