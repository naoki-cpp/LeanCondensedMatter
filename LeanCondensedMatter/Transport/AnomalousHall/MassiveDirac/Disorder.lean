import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.ScalarCovariance
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.ContinuumBornAngularBridge
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.DenominatorUV
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexLadder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.BornCurrentVertexTransportBridge
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.BornCurrentVertexInfiniteCutoff

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
Born-Dyson path, a single arbitrary in-plane vertex theorem reduces the full-angle rung to the
coefficient pair `(X,Y)` with repository orientation `[[X,-Y],[Y,X]]`; the `σₓ` and `σᵧ` basis
channels are corollaries rather than separate derivations.  The radial layer integrates those
coefficients with the polar Jacobian and attaches the scalar-disorder line together with
`momentumMeasurePrefactor` exactly once, yielding the normalized finite-cutoff pair consumed by the
canonical in-plane ladder algebra.  That pair is now specialized through the canonical exact ladder
solver, exposing the determinant, solved coefficients, and bounded dimensionless dressed vertex
without introducing a second fixed-point algebra.  The zero-disorder angular basis case regresses to
the clean finite-broadening rung, while the normalized radial rung vanishes and the solved vertex
returns to bare `σₓ` at zero disorder.  The zero-external-broadening angular/radial rung,
finite-cutoff integration, normalization identity, fixed-cutoff metallic weak-disorder limit, and
scalar `τ_tr / τ_sp` bridge remain separate.  Separately, the common real radial denominator integral
is evaluated in closed arctangent form and its convergent `pMax → +∞` limit is proved before taking
`γ → 0⁺`; this also exposes the leading positive `σᵧ` coefficient in repository orientation
`Gᴿ σₓ Gᴬ`.  The generic supplied-Green RA Fermi-surface trace channel is shared by these paths.

The exact coefficient-level fixed point for any supplied in-plane rung pair `(X,Y)` remains the
single algebraic authority.  Physical charge-current conversion and conductivity insertion are
separate downstream boundaries.  RTA recovery, SCBA, simultaneous UV / zero-broadening limits,
crossed diagrams, and a complete conductivity theorem remain separate.
-/
