import LeanCondensedMatter.Transport.FiniteVolume
import LeanCondensedMatter.Transport.ConductivityNormalization
import LeanCondensedMatter.Transport.FiniteConductivityTable
import LeanCondensedMatter.Transport.FiniteTrace
import LeanCondensedMatter.Transport.Resolvent
import LeanCondensedMatter.Transport.ResolventSpectral
import LeanCondensedMatter.Transport.FiniteKuboBastin
import LeanCondensedMatter.Transport.ResolventEnergyDerivative
import LeanCondensedMatter.Transport.StredaOperatorKernel
import LeanCondensedMatter.Transport.StredaTraceKernel
import LeanCondensedMatter.Transport.OccupationInterpolation
import LeanCondensedMatter.Transport.StredaOccupation
import LeanCondensedMatter.Transport.StredaCommonKernel
import LeanCondensedMatter.Transport.StredaIntegration
import LeanCondensedMatter.Transport.GeneralizedStaticStreda
import LeanCondensedMatter.Transport.StredaTraceSpectral
import LeanCondensedMatter.Transport.StredaTraceRepresentation
import LeanCondensedMatter.Transport.StredaSpectralEnergyIntegral
import LeanCondensedMatter.Transport.FiniteDisorder
import LeanCondensedMatter.Transport.FiniteDisorderResolvent
import LeanCondensedMatter.Transport.FiniteDisorderMoments
import LeanCondensedMatter.Transport.FiniteDisorderBorn
import LeanCondensedMatter.Transport.FiniteDisorderAdvancedBorn
import LeanCondensedMatter.Transport.FiniteDisorderSCBA

set_option linter.style.header false

/-!
# Transport

Public entry point for generic transport infrastructure: finite-volume/electric-field normalization,
finite scalar conductivity evaluation, ordinary finite-dimensional trace infrastructure, response and
resolvent formulations, resolvent spectral action, finite pure-point, occupation-resolved,
common-energy, and static Kubo–Bastin/Středa bridges, Středa integration/trace theory, occupation
interpolation, exact finite disorder/resolvent identities, shared finite-disorder moments, and
Born/SCBA approximations.

Concrete statistics-neutral model umbrellas such as `LeanCondensedMatter.Transport.AnomalousHall` are
explicit downstream imports rather than part of this generic umbrella. Model-specific fermionic
transport adapters likewise remain downstream in `SecondQuantization.Fermionic`.
Implementation modules should import the narrow transport leaves they use rather than this umbrella.
-/
