import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderRadial
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderRadialDenominator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderZeroBroadening
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderLongitudinalZeroBroadeningIntegral
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderHallZeroBroadeningIntegral
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderLongitudinalZeroBroadeningWeakDisorder

set_option linter.style.header false

/-!
# Massive-Dirac Středa specialization

Public umbrella for the finite-`η` Born-Dyson RA-dressed/bare-same-side Středa surface response with
bare measured current fixed along `x` and the source direction indexed by `Direction2`. The generic
path is exposed from the pointwise trace bridge through finite-cutoff polar momentum integration;
the ordered `xy` specialization additionally exposes the explicit Hall radial reduction and common
denominator form. Fixed-cutoff zero-broadening boundaries are exposed for the source-indexed dressed
current and for both the integrated longitudinal and ordered-`xy` responses, together with the
separate weak-disorder limit of the disorder-scaled longitudinal momentum boundary.

The supplied ladder coefficients are total algebraic values. The shared nonzero in-plane ladder
determinant is required only when they are interpreted as the solved physical fixed point. Generic
shared-provenance response matrices, pointwise trace identities, and finite-energy surface/sea
integration are consumed directly from `Transport.Streda`.

Physical conductivity remains downstream: only `MassiveDirac.Conductivity` attaches the common
Bastin/Středa conductivity prefactor and physical continuum momentum normalization. Bounded-operator
and spectral/resolvent infrastructure is owned by `MassiveDirac.Model`; ladder and Born-Dyson Green
construction remain owned by `MassiveDirac.Disorder`.
-/
