import LeanCondensedMatter.Transport.FiniteVolume
import LeanCondensedMatter.Transport.System
import LeanCondensedMatter.Transport.LinearResponse
import LeanCondensedMatter.Transport.Resolvent
import LeanCondensedMatter.Transport.FiniteKuboBastin
import LeanCondensedMatter.Transport.ResolventEnergyDerivative
import LeanCondensedMatter.Transport.StredaOperatorKernel
import LeanCondensedMatter.Transport.StredaTraceKernel
import LeanCondensedMatter.Transport.OccupationInterpolation
import LeanCondensedMatter.Transport.StredaOccupation
import LeanCondensedMatter.Transport.StredaCommonKernel
import LeanCondensedMatter.Transport.StredaIntegration
import LeanCondensedMatter.Transport.StredaResolventSpectral
import LeanCondensedMatter.Transport.StredaTraceSpectral
import LeanCondensedMatter.Transport.StredaTraceRepresentation
import LeanCondensedMatter.Transport.StredaSpectralEnergyIntegral
import LeanCondensedMatter.Transport.FiniteDisorder
import LeanCondensedMatter.Transport.FiniteDisorderBorn
import LeanCondensedMatter.Transport.FiniteDisorderAdvancedBorn
import LeanCondensedMatter.Transport.FiniteDisorderSCBA
import LeanCondensedMatter.Transport.AnomalousHall

set_option linter.style.header false

/-!
# Transport

Public entry point for generic transport infrastructure: finite-volume normalization, response and
resolvent formulations, finite pure-point, occupation-resolved, and common-energy Kubo–Bastin,
Středa integration/trace theory, occupation interpolation, finite disorder, and concrete
anomalous-Hall benchmarks.

Model-specific fermionic transport adapters remain downstream in `SecondQuantization.Fermionic`.
Implementation modules should import the narrow transport leaves they use rather than this umbrella.
-/
