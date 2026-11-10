import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialUVFinitePart

set_option linter.style.header false

/-!
# Spectral-center parity of the ultraviolet Dirac Fourier kernel

The fixed-spectral radial Fourier UV value is indexed by the quadratic
center `Z = E² - M²`. Its evenness in the spatial Fourier argument follows
from the parity of the finite-cutoff zeroth-harmonic kernel and uniqueness
of its UV limit. The argument assumes a nonreal center and makes no
statement about a running Born self-energy or a regulator limit.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Evenness of the center-indexed Fourier UV boundary. -/
theorem massiveDiracRadialFourierUVCenter_neg
    (v c : ℝ) (center : ℂ)
    (hv : v ≠ 0) (hc : c ≠ 0) (hcenter : center.im ≠ 0) :
    massiveDiracRadialFourierUVCenter v (-c) center =
      massiveDiracRadialFourierUVCenter v c center := by
  have hneg := massiveDiracRadialFourier_tendsto_uvValue_center
    v (-c) center hv (neg_ne_zero.mpr hc) hcenter
  have hpos := massiveDiracRadialFourier_tendsto_uvValue_center
    v c center hv hc hcenter
  have heq (b : ℝ) :
      (∫ p in (0 : ℝ)..b,
        (p : ℂ) * polarFourierZerothAngularKernel (p * -c) *
          (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))⁻¹) =
        (∫ p in (0 : ℝ)..b,
          (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
            (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))⁻¹) := by
    apply intervalIntegral.integral_congr
    intro p _
    dsimp only
    rw [show p * -c = -(p * c) by ring,
      polarFourierZerothAngularKernel_neg]
  exact tendsto_nhds_unique
    (hneg.congr' (Filter.Eventually.of_forall heq))
    hpos

end

end QuantumTheory.Models.MassiveDirac
