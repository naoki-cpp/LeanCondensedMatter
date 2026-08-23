import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.Occupation
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Lorentzian tail control for the massive-Dirac Bastin kernel

The zero-temperature occupation bridge isolates the spectral pole on a fixed symmetric window.
To pass from that local extraction to a larger occupation-weighted energy window, the remaining
Lorentzian mass must be shown to disappear as the broadening tends to zero.

This file records that statement at the scalar spectral-kernel level.  It does not yet bound a
weighted tail or perform the full Bastin energy integration.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter

/-- Lorentzian spectral mass between an inner and outer symmetric window, represented as the
outer-window mass minus the inner-window mass. -/
def lorentzianSpectralTailMass (innerRadius outerRadius broadening : ℝ) : ℝ :=
  (∫ offset in -outerRadius..outerRadius,
      lorentzianSpectralKernel offset broadening) -
    (∫ offset in -innerRadius..innerRadius,
      lorentzianSpectralKernel offset broadening)

/-- Exact arctangent form of the symmetric Lorentzian tail mass. -/
theorem lorentzianSpectralTailMass_eq_two_mul_arctan_sub
    (innerRadius outerRadius broadening : ℝ) :
    lorentzianSpectralTailMass innerRadius outerRadius broadening =
      2 * (Real.arctan (outerRadius / broadening) -
        Real.arctan (innerRadius / broadening)) := by
  rw [lorentzianSpectralTailMass,
    integral_lorentzianSpectralKernel_symmetric,
    integral_lorentzianSpectralKernel_symmetric]
  ring

/-- The outer symmetric mass is the inner mass plus the spectral tail mass. -/
theorem integral_lorentzianSpectralKernel_outer_eq_inner_add_tail
    (innerRadius outerRadius broadening : ℝ) :
    (∫ offset in -outerRadius..outerRadius,
        lorentzianSpectralKernel offset broadening) =
      (∫ offset in -innerRadius..innerRadius,
        lorentzianSpectralKernel offset broadening) +
        lorentzianSpectralTailMass innerRadius outerRadius broadening := by
  unfold lorentzianSpectralTailMass
  ring

/-- For fixed positive nested radii, all Lorentzian mass between the two windows vanishes as the
broadening tends to zero from the positive side. -/
theorem tendsto_lorentzianSpectralTailMass_zero
    (innerRadius outerRadius : ℝ)
    (hinner : 0 < innerRadius) (hnested : innerRadius ≤ outerRadius) :
    Tendsto
      (fun broadening : ℝ =>
        lorentzianSpectralTailMass innerRadius outerRadius broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  have houter : 0 < outerRadius := lt_of_lt_of_le hinner hnested
  have hOuterMass :=
    tendsto_integral_lorentzianSpectralKernel_symmetric outerRadius houter
  have hInnerMass :=
    tendsto_integral_lorentzianSpectralKernel_symmetric innerRadius hinner
  have htail := hOuterMass.sub hInnerMass
  simpa [lorentzianSpectralTailMass] using htail

end

end AnomalousHall.MassiveDirac
