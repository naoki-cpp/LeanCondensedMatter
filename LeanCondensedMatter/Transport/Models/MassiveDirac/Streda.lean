import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderRadial
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderRadialDenominator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderZeroBroadening
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderLongitudinalZeroBroadeningIntegral
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderHallZeroBroadeningIntegral
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderLongitudinalZeroBroadeningWeakDisorder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderHallZeroBroadeningWeakDisorder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderHallZeroBroadeningProvenance
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.GaussianCrossedTrace
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.GaussianCrossedRealSpace
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.GaussianCrossedRealSpaceIntegral

set_option linter.style.header false

/-!
# Massive-Dirac Středa specialization

Public umbrella for the finite-`η` Born-Dyson RA-dressed/bare-same-side Středa surface response with
bare measured current fixed along `x` and the source direction indexed by `Fin 2`. The generic
path is exposed from the pointwise trace bridge through finite-cutoff polar momentum integration;
the ordered `xy` specialization additionally exposes the explicit Hall radial reduction and common
denominator form. Fixed-cutoff zero-broadening boundaries are exposed for the source-indexed dressed
current and for both the integrated longitudinal and ordered-`xy` responses. Their subsequent
weak-disorder limits remain separate: the longitudinal response is scaled by `W`, while the ordered
transverse response retains the first nonvanishing transverse ladder coefficient before cancelling
the inverse disorder factor. The ordered-`xy` endpoint also exposes a theorem-level expansion of the
canonical `inPlaneLadderAction` component into the concrete `r_y Γ_x` and `r_x Γ_y` products, without
introducing a second public representation or assigning scattering-mechanism labels.

The leading Gaussian crossed sector is a separate Středa-level real-space trace boundary. Its `X` and
`Psi` topologies are represented by one indexed kernel, and the massive-Dirac finite-cutoff finite-`η`
realization supplies the corresponding polar-Fourier real-space Green matrices and Eq. (14)-style
`Gᴬ (F σ_source) Gᴿ` current blocks. Here `F` is the diagonal resummation `(1 - A)⁻¹` built only from
the longitudinal current-rung coefficient, matching the leading crossed-diagram approximation; the
transverse part of the full local RA dressed source-current vertex and its feedback are deliberately
excluded from `J_r`. The crossed kernel is integrated over a finite-radius polar real-space domain,
and a separate boundary attaches the two scalar Gaussian disorder correlators as an explicit `W²`
factor. Infinite-radius and momentum-cutoff removal, zero-broadening and weak-disorder limits,
Bessel-function reduction, and physical crossed conductivity remain downstream.

Although the real-coordinate pattern matches the imaginary part of ordinary complex multiplication,
the in-plane coefficients here are already `ℂ`-valued. Therefore the public API remains the `ℂ²`
ladder action rather than collapsing it to a single complex scalar.

The supplied ladder coefficients are total algebraic values. The shared nonzero in-plane ladder
determinant is required only when they are interpreted as the solved physical fixed point. Generic
shared-provenance response matrices, pointwise trace identities, and finite-energy surface/sea
integration are consumed directly from `Transport.Streda`.

Physical conductivity remains downstream: only `MassiveDirac.Conductivity` attaches the common
Bastin/Středa conductivity prefactor and physical continuum momentum normalization. Bounded-operator
and spectral/resolvent infrastructure is owned by `MassiveDirac.Model`; ladder and Born-Dyson Green
construction remain owned by `MassiveDirac.Disorder`.
-/
