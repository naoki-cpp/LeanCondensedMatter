import LeanCondensedMatter.Transport.Models.MassiveDirac.Propagator.Basic

set_option linter.style.header false

/-!
# Massive-Dirac radial denominator kernels

This module owns the model-local radial denominator algebra shared by Born self-energy and
retarded-advanced current-rung calculations. It contains only the effective-energy/effective-mass
quadratic denominator, its retarded-advanced product, and the corresponding polar-Jacobian kernels.
No self-energy, damping, disorder prefactor, radial integral, or conductivity statement lives here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

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

/-- Polar Jacobian divided by a retarded-advanced radial denominator product. -/
def massiveDiracRetardedAdvancedRadialDenominatorKernel
    (v p : ℝ)
    (retardedEnergy retardedMass advancedEnergy advancedMass : ℂ) : ℂ :=
  (p : ℂ) *
    (massiveDiracRetardedAdvancedRadialDenominatorProduct
      v p retardedEnergy retardedMass advancedEnergy advancedMass)⁻¹

end

end QuantumTheory.Transport.Models.MassiveDirac
