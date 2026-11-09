import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialUVFinitePart
import Mathlib.Analysis.RCLike.Sqrt

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

private theorem complex_sqrt_sq_spectral_center (z : ℂ) :
    (Complex.sqrt z) ^ 2 = z := by
  simpa [Complex.sqrt] using (Complex.cpow_ofNat_inv_pow z 2)

/-- Evenness of the center-indexed Fourier UV boundary. -/
theorem massiveDiracRadialFourierUVCenter_neg
    (v c : ℝ) (center : ℂ)
    (hv : v ≠ 0) (hc : c ≠ 0) (hcenter : center.im ≠ 0) :
    massiveDiracRadialFourierUVCenter v (-c) center =
      massiveDiracRadialFourierUVCenter v c center := by
  let energy : ℂ := Complex.sqrt center
  have hcenterEq : energy ^ 2 - (0 : ℂ) ^ 2 = center := by
    simp [energy, complex_sqrt_sq_spectral_center]
  have hnonreal : (energy ^ 2 - (0 : ℂ) ^ 2).im ≠ 0 := by
    rw [hcenterEq]
    exact hcenter
  have hneg := massiveDiracRadialFourier_tendsto_uvValue
    v (-c) energy 0 hv (neg_ne_zero.mpr hc) hnonreal
  have hpos := massiveDiracRadialFourier_tendsto_uvValue
    v c energy 0 hv hc hnonreal
  rw [hcenterEq] at hneg hpos
  have heq (b : ℝ) :
      (∫ p in (0 : ℝ)..b,
        (p : ℂ) * polarFourierZerothAngularKernel (p * -c) *
          (massiveDiracRadialDenominator v p energy 0)⁻¹) =
      (∫ p in (0 : ℝ)..b,
        (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
          (massiveDiracRadialDenominator v p energy 0)⁻¹) := by
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
