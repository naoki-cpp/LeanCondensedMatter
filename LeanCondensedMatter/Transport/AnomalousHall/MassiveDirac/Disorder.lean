import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.ScalarCovariance
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.ContinuumBornAngularBridge
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.DenominatorFactorization
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.DenominatorEvaluation
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.DenominatorUV
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.DenominatorBroadeningLimit
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.ChannelBroadeningLimit
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.SelfEnergyBroadeningLimit
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.UpperBandDamping
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.SingleParticleRate
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.TransportRate
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.BornPropagator
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.BornPropagatorOperator
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.FiniteBroadeningBornPropagator
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexAngular
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexIntegral
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexInPlane
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.CurrentVertexAngular
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.InPlaneLadder
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.BornCurrentVertexRadial
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.BornCurrentVertexFiniteCutoff
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.BornCurrentVertexWeakDisorder
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.BornCurrentVertexNormalizationBridge
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.BornCurrentVertexTransportBridge
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.BornCurrentVertexIntegral
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.BornCurrentVertexInfiniteCutoff
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.BornLongitudinalKubo
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Propagator
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.PropagatorSymmetry

set_option linter.style.header false

/-!
# Massive-Dirac disorder transport

Public umbrella for the disorder-dependent phases of the massive-Dirac anomalous Hall program.
The completed Phase 4 chain keeps the exact finite scalar-covariance specialization separate from
the model-specific finite-cutoff continuum Born closure, while sharing the clean Pauli-basis
propagator and exact momentum-inversion symmetry.  It evaluates the common finite-cutoff radial
denominator, separates ultraviolet-sensitive real and metallic on-shell imaginary pieces, projects
the damping onto the upper band, derives the microscopic single-particle scattering rate, and
separately derives the Born transport rate from the Fermi-circle current-relaxation weight.

Phase 5 includes the exact finite-broadening angular reduction of the retarded-advanced `x`-current
rung, the zero-external-broadening weak-disorder Born propagator used by the current-rung benchmark,
and a separate finite-cutoff Born-Dyson propagator candidate that retains the external Středa/Kubo
broadening `η` through the existing finite-`η` continuum Born self-energy.  For that finite-`η`
Born-Dyson path, the full-angle `σₓ` and `σᵧ` basis rungs are reduced to the common in-plane
coefficient pair `(X,Y)`, and the induced arbitrary in-plane action is proved to have repository
orientation `[[X,-Y],[Y,X]]`.  Radial integration and scalar-disorder normalization remain
downstream of this angular layer.  The zero-external-broadening angular/radial rung, finite-cutoff
integration, normalization bridge, fixed-cutoff metallic weak-disorder limit, and scalar
`τ_tr / τ_sp` bridge remain separate.  Separately, the common real radial denominator integral is
evaluated in closed arctangent form and its convergent `pMax → +∞` limit is proved before taking
`γ → 0⁺`; this also exposes the leading positive `σᵧ` coefficient in repository orientation
`Gᴿ σₓ Gᴬ`.  The generic supplied-Green RA Fermi-surface trace channel is shared by these paths.

The exact coefficient-level fixed point for any supplied in-plane rung pair `(X,Y)` is also exposed,
including its orientation-sensitive `σᵧ` component and the visible determinant condition for
uniqueness.  Instantiating those coefficients with the normalized finite-`η` Born-Dyson radial
integral, then connecting the solved dressed current to conductivity, remains downstream.  RTA
recovery, SCBA, simultaneous UV / zero-broadening limits, crossed diagrams, and a complete
conductivity theorem remain separate.
-/