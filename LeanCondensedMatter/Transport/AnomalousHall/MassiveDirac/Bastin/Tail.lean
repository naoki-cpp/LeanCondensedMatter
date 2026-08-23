import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.Occupation
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Lorentzian tail compatibility layer for the massive-Dirac Bastin kernel

The model-independent nested-window Lorentzian tail mass and its zero-broadening limit now live in
`Transport.Analysis.LorentzianKernel`.  This module preserves the historical massive-Dirac names as
thin compatibility wrappers so the downstream Bastin pole-error chain can migrate independently.

No model-specific tail analysis remains here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter

/-- Compatibility alias for the generic Lorentzian spectral tail mass. -/
abbrev lorentzianSpectralTailMass := QuantumTheory.Transport.lorentzianSpectralTailMass

/-- Compatibility wrapper for the generic exact arctangent form of the symmetric tail mass. -/
theorem lorentzianSpectralTailMass_eq_two_mul_arctan_sub
    (innerRadius outerRadius broadening : ℝ) :
    lorentzianSpectralTailMass innerRadius outerRadius broadening =
      2 * (Real.arctan (outerRadius / broadening) -
        Real.arctan (innerRadius / broadening)) :=
  QuantumTheory.Transport.lorentzianSpectralTailMass_eq_two_mul_arctan_sub
    innerRadius outerRadius broadening

/-- Compatibility wrapper for the generic decomposition of outer mass into inner mass plus tail. -/
theorem integral_lorentzianSpectralKernel_outer_eq_inner_add_tail
    (innerRadius outerRadius broadening : ℝ) :
    (∫ offset in -outerRadius..outerRadius,
        lorentzianSpectralKernel offset broadening) =
      (∫ offset in -innerRadius..innerRadius,
        lorentzianSpectralKernel offset broadening) +
        lorentzianSpectralTailMass innerRadius outerRadius broadening :=
  QuantumTheory.Transport.integral_lorentzianSpectralKernel_outer_eq_inner_add_tail
    innerRadius outerRadius broadening

/-- Compatibility wrapper for vanishing Lorentzian mass between fixed nested positive windows. -/
theorem tendsto_lorentzianSpectralTailMass_zero
    (innerRadius outerRadius : ℝ)
    (hinner : 0 < innerRadius) (hnested : innerRadius ≤ outerRadius) :
    Tendsto
      (fun broadening : ℝ =>
        lorentzianSpectralTailMass innerRadius outerRadius broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) :=
  QuantumTheory.Transport.tendsto_lorentzianSpectralTailMass_zero
    innerRadius outerRadius hinner hnested

end

end AnomalousHall.MassiveDirac
