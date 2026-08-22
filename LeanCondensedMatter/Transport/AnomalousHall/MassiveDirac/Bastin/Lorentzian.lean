import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinLimit
import LeanCondensedMatter.Transport.LorentzianSpectralKernel
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Lorentzian spectral weight for the massive-Dirac Bastin kernel

The model-independent Lorentzian kernel, its scalar resolvent identity, finite-window integrals, and
symmetric `η → 0⁺` mass theorem now live in `Transport.LorentzianSpectralKernel`.

This compatibility layer keeps the existing massive-Dirac names available and proves only the
model-specific bridge identifying the selected band spectral difference with that generic kernel.
Downstream AHE modules can therefore migrate incrementally without duplicating the scalar analysis.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- Compatibility alias for the generic Lorentzian spectral kernel. -/
abbrev lorentzianSpectralKernel := QuantumTheory.Transport.lorentzianSpectralKernel

/-- Compatibility theorem for the generic scalar retarded-minus-advanced resolvent identity. -/
theorem inv_add_I_sub_inv_sub_I_eq_lorentzian
    (offset broadening : ℝ) (hbroadening : broadening ≠ 0) :
    ((offset : ℂ) + (broadening : ℂ) * Complex.I)⁻¹ -
        ((offset : ℂ) - (broadening : ℂ) * Complex.I)⁻¹ =
      (-2 * Complex.I) * (lorentzianSpectralKernel offset broadening : ℂ) :=
  QuantumTheory.Transport.inv_add_I_sub_inv_sub_I_eq_lorentzian
    offset broadening hbroadening

/-- The scalar spectral difference in the two-band Bastin decomposition is exactly a Lorentzian
centered at the selected band energy. -/
theorem spectralDifferenceCoefficient_eq_lorentzian
    (band : Band) (v m px py probeEnergy broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    spectralDifferenceCoefficient band v m px py probeEnergy broadening =
      (-2 * Complex.I) *
        (lorentzianSpectralKernel
          (probeEnergy - bandEnergy band v m px py) broadening : ℂ) := by
  unfold spectralDifferenceCoefficient projectorResolventCoefficient
    retardedSpectralParameter advancedSpectralParameter
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    inv_add_I_sub_inv_sub_I_eq_lorentzian
      (probeEnergy - bandEnergy band v m px py) broadening hbroadening

/-- Compatibility theorem for the generic exact finite-interval Lorentzian mass. -/
theorem integral_lorentzianSpectralKernel
    (lower upper broadening : ℝ) :
    (∫ offset in lower..upper, lorentzianSpectralKernel offset broadening) =
      Real.arctan (upper / broadening) - Real.arctan (lower / broadening) :=
  QuantumTheory.Transport.integral_lorentzianSpectralKernel lower upper broadening

/-- Compatibility theorem for the generic symmetric-window Lorentzian mass. -/
theorem integral_lorentzianSpectralKernel_symmetric
    (radius broadening : ℝ) :
    (∫ offset in -radius..radius, lorentzianSpectralKernel offset broadening) =
      2 * Real.arctan (radius / broadening) :=
  QuantumTheory.Transport.integral_lorentzianSpectralKernel_symmetric radius broadening

/-- Compatibility theorem for asymptotic Lorentzian mass `π` on a fixed positive symmetric window. -/
theorem tendsto_integral_lorentzianSpectralKernel_symmetric
    (radius : ℝ) (hradius : 0 < radius) :
    Tendsto
      (fun broadening : ℝ =>
        ∫ offset in -radius..radius, lorentzianSpectralKernel offset broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds Real.pi) :=
  QuantumTheory.Transport.tendsto_integral_lorentzianSpectralKernel_symmetric
    radius hradius

end

end AnomalousHall.MassiveDirac
