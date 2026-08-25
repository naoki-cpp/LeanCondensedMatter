import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.Limit
import LeanCondensedMatter.Transport.Analysis.LorentzianKernel
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Lorentzian spectral bridge for the massive-Dirac Bastin kernel

The model-independent Lorentzian kernel and its scalar analysis live in
`Transport.Analysis.LorentzianKernel`. This file keeps the model-local shorthand used throughout the
massive-Dirac Bastin formulas and the one model-specific bridge identifying the selected-band
spectral difference with that generic kernel.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Model-local shorthand for the generic Lorentzian spectral kernel. -/
abbrev lorentzianSpectralKernel := QuantumTheory.Transport.lorentzianSpectralKernel

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
    QuantumTheory.Transport.inv_add_I_sub_inv_sub_I_eq_lorentzian
      (probeEnergy - bandEnergy band v m px py) broadening hbroadening

end

end AnomalousHall.MassiveDirac
