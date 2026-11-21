import LeanCondensedMatter.Models.MassiveDirac.Propagator.Basic

set_option linter.style.header false

/-!
# Massive-Dirac radial Green-function denominator

Algebraic denominators for arbitrary complex spectral energy and mass, including
the retarded/advanced pair and the single radial Jacobian-weighted resolvent.
These definitions are independent of Born disorder, self-energy, and Fourier
integration. Fourier and impurity modules should import this lightweight core.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

/-- Radial massive-Dirac denominator for arbitrary complex effective energy and mass. -/
def massiveDiracRadialDenominator
    (v p : ℝ) (effectiveEnergy effectiveMass : ℂ) : ℂ :=
  effectiveEnergy ^ 2 - effectiveMass ^ 2 - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)

/-- Retarded-advanced product of two radial massive-Dirac denominators. -/
def massiveDiracRetardedAdvancedRadialDenominatorProduct
    (v p : ℝ)
    (retardedEnergy retardedMass advancedEnergy advancedMass : ℂ) : ℂ :=
  massiveDiracRadialDenominator v p retardedEnergy retardedMass *
    massiveDiracRadialDenominator v p advancedEnergy advancedMass

/-- Polar Jacobian divided by one radial massive-Dirac denominator. -/
def massiveDiracRadialDenominatorKernel
    (v p : ℝ) (effectiveEnergy effectiveMass : ℂ) : ℂ :=
  (p : ℂ) * (massiveDiracRadialDenominator v p effectiveEnergy effectiveMass)⁻¹

end

end QuantumTheory.Models.MassiveDirac
