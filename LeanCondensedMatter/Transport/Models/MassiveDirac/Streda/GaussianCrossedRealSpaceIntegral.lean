import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.GaussianCrossedRealSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.style.header false

/-!
# Finite-radius real-space integration of Gaussian crossed Hall kernels

This module lifts the finite-cutoff finite-broadening crossed trace kernel to the real-space integral
appearing before the closed `X` / `Psi` evaluations. The two-dimensional position integral is kept in
polar form with an explicit finite radial cutoff,

```text
∫ d²r K(r) = ∫₀^{rMax} ρ dρ ∫₀^{2π} dφ K(ρ cos φ, ρ sin φ).
```

A separate weighted boundary multiplies this integral by the two scalar Gaussian disorder
correlators carried by a crossed diagram. In the repository normalization each correlator contributes
one factor of `disorderStrength`, so the crossed pair contributes `disorderStrength²`. This is the
finite-regulator counterpart of the squared disorder factor in Ado et al., EPL 111, 37004 (2015),
Eq. (13), before restoring the remaining physical conductivity normalization.

No infinite-radius limit, momentum-cutoff removal, zero-broadening or weak-disorder limit,
Bessel-function reduction, or closed crossed conductivity is claimed here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open MeasureTheory
open scoped Interval

/-- Cartesian point `(ρ cos φ, ρ sin φ)` used by the finite polar real-space integral. -/
private def gaussianCrossedPolarRealSpacePoint (radius angle : ℝ) : Fin 2 → ℝ :=
  fun i => Fin.cases (radius * Real.cos angle) (fun _ => radius * Real.sin angle) i

/-- Finite-radius polar integral of a complex field over two-dimensional real space. The Jacobian
`ρ` is explicit and there is no momentum-space normalization factor in this position-space measure. -/
private noncomputable def finiteRadiusPolarRealSpaceIntegral
    (rMax : ℝ) (field : (Fin 2 → ℝ) → ℂ) : ℂ :=
  ∫ radius in (0 : ℝ)..rMax,
    ∫ angle in (0 : ℝ)..(2 * Real.pi),
      ((radius : ℂ) * field (gaussianCrossedPolarRealSpacePoint radius angle))

/-- Finite-radius integral of the model-specific finite-cutoff finite-`η` Gaussian crossed trace
kernel. This is the regulated real-space integral underlying Ado et al. Eq. (13), before the two
crossed disorder correlators and the physical conductivity normalization are attached. -/
noncomputable def finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceIntegral
    (diagram : GaussianCrossedDiagram)
    (v m probeEnergy broadening disorderStrength hbar pMax rMax : ℝ) : ℂ :=
  finiteRadiusPolarRealSpaceIntegral rMax
    (finiteCutoffContinuumBornDysonGaussianCrossedTraceKernel
      diagram v m probeEnergy broadening disorderStrength hbar pMax)

/-- Crossed real-space trace integral with the two Gaussian disorder correlators attached.

The Born disorder parameter is the scalar two-point correlator amplitude used throughout the
massive-Dirac disorder stack. A crossed `X` or `Psi` diagram contains two such correlator lines, so
this boundary multiplies the regulated trace integral by `disorderStrength²`. Charge/current and
`e² / h` conductivity normalization remain downstream. -/
noncomputable def finiteCutoffContinuumBornDysonGaussianCrossedWeightedRealSpaceIntegral
    (diagram : GaussianCrossedDiagram)
    (v m probeEnergy broadening disorderStrength hbar pMax rMax : ℝ) : ℂ :=
  (((disorderStrength ^ 2 : ℝ) : ℂ)) *
    finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceIntegral
      diagram v m probeEnergy broadening disorderStrength hbar pMax rMax

/-- With the two crossed disorder correlators explicit, the regulated crossed contribution vanishes
identically at zero disorder strength. -/
@[simp] theorem finiteCutoffContinuumBornDysonGaussianCrossedWeightedRealSpaceIntegral_zero_disorder
    (diagram : GaussianCrossedDiagram)
    (v m probeEnergy broadening hbar pMax rMax : ℝ) :
    finiteCutoffContinuumBornDysonGaussianCrossedWeightedRealSpaceIntegral
      diagram v m probeEnergy broadening 0 hbar pMax rMax = 0 := by
  simp [finiteCutoffContinuumBornDysonGaussianCrossedWeightedRealSpaceIntegral]

end

end QuantumTheory.Transport.Models.MassiveDirac
