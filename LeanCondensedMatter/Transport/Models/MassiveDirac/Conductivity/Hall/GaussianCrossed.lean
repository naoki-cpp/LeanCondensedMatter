import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Normalization
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.GaussianCrossedRealSpaceIntegral

set_option linter.style.header false

/-!
# Physically normalized Gaussian crossed Hall contribution

This module is the conductivity-normalization boundary for the regulated massive-Dirac Gaussian
crossed `X` / `Psi` real-space contributions. The upstream Středa layer already attaches the two
Gaussian disorder correlators and each real-space Fourier block already carries its own physical
momentum measure `d²p / (2πℏ)²`. Consequently this layer restores only

- the two physical charge-current scales, giving `(e v)²`; and
- the trace-only Bastin prefactor `ℏ / (2π)`.

It deliberately does not attach `bastinStredaConductivityNormalization`, which would insert an
additional momentum-measure factor. The result remains the regulated ordered measured-`x`,
source-`y` crossed conductivity contribution. No real-space or momentum-cutoff removal,
zero-broadening or weak-disorder limit, closed `X` value, or `Psi = 0` conductivity evaluation is
claimed here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

/-- Physically normalized finite-cutoff finite-broadening ordered-`xy` Gaussian crossed
conductivity contribution.

The two crossed current blocks are built from dimensionless Pauli current vertices upstream, so the
physical current scale contributes `(e v)²`. Their Fourier transforms already contain the physical
momentum measure, hence only `bastinTraceConductivityPrefactor` is attached here. -/
noncomputable def finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity
    (diagram : GaussianCrossedDiagram)
    (e v m probeEnergy broadening disorderStrength hbar pMax rMax : ℝ) : ℂ :=
  (((bastinTraceConductivityPrefactor hbar * (e * v) ^ 2 : ℝ) : ℂ)) *
    finiteCutoffContinuumBornDysonGaussianCrossedWeightedRealSpaceIntegral
      diagram v m probeEnergy broadening disorderStrength hbar pMax rMax

/-- The regulated crossed conductivity vanishes identically when the Gaussian disorder strength is
zero because the two explicit crossed disorder correlators supply a factor `disorderStrength²`. -/
@[simp] theorem finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_zero_disorder
    (diagram : GaussianCrossedDiagram)
    (e v m probeEnergy broadening hbar pMax rMax : ℝ) :
    finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity
      diagram e v m probeEnergy broadening 0 hbar pMax rMax = 0 := by
  simp [finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity]

/-- The regulated `Psi` conductivity remains real because its trace-level Hermitian-conjugate
partner is included upstream and the remaining physical normalization is real. -/
@[simp] theorem finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_psi_im
    (e v m probeEnergy broadening disorderStrength hbar pMax rMax : ℝ) :
    (finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity
      .psi e v m probeEnergy broadening disorderStrength hbar pMax rMax).im = 0 := by
  unfold finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity
  rw [Complex.mul_im,
    finiteCutoffContinuumBornDysonGaussianCrossedWeightedRealSpaceIntegral_psi_im]
  simp only [Complex.ofReal_im, mul_zero, zero_mul, add_zero]

end

end QuantumTheory.Transport.Models.MassiveDirac
