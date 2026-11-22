import LeanCondensedMatter.Transport.Scattering.IsotropicAngularWeights
import LeanCondensedMatter.Models.MassiveDirac.Model.FermiSurfaceOverlap
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Scalar-disorder Fermi-circle angular weights

Specialize the Hamiltonian-independent angular means to the upper-band
projector overlap. Born rate prefactors and lifetimes remain in `TransportRate`.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Write the model-specific projector overlap as an affine first cosine harmonic. -/
private theorem upperBandFermiSurfaceScalarOverlapWeight_eq_affineCosine
    (v m fermiEnergy : ℝ) :
    upperBandFermiSurfaceScalarOverlapWeight v m fermiEnergy =
      (fun θ : ℝ =>
        (1 + m ^ 2 / fermiEnergy ^ 2) / 2 +
          ((1 - m ^ 2 / fermiEnergy ^ 2) / 2) * Real.cos θ) := by
  funext θ
  unfold upperBandFermiSurfaceScalarOverlapWeight
  ring

/-- Upper-band overlap factor in the single-particle Born rate. -/
def isotropicUpperBandSingleParticleAngularWeight
    (v m fermiEnergy : ℝ) : ℝ :=
  isotropicSingleParticleAngularMean
    (upperBandFermiSurfaceScalarOverlapWeight v m fermiEnergy)

/-- The unweighted scalar-disorder overlap average is `(1 + m²/ε_F²)/2`. -/
theorem isotropicUpperBandSingleParticleAngularWeight_eq
    (v m fermiEnergy : ℝ) :
    isotropicUpperBandSingleParticleAngularWeight v m fermiEnergy =
      (1 + m ^ 2 / fermiEnergy ^ 2) / 2 := by
  unfold isotropicUpperBandSingleParticleAngularWeight
  rw [upperBandFermiSurfaceScalarOverlapWeight_eq_affineCosine,
    isotropicSingleParticleAngularMean_affineCosine]

/-- Upper-band transport mean, weighted by `1 - cos θ`. -/
def isotropicUpperBandTransportAngularWeight
    (v m fermiEnergy : ℝ) : ℝ :=
  isotropicTransportAngularMean
    (upperBandFermiSurfaceScalarOverlapWeight v m fermiEnergy)

/-- The scalar-disorder transport angular weight is `(1 + 3 m²/ε_F²)/4`. -/
theorem isotropicUpperBandTransportAngularWeight_eq
    (v m fermiEnergy : ℝ) :
    isotropicUpperBandTransportAngularWeight v m fermiEnergy =
      (1 + 3 * (m ^ 2 / fermiEnergy ^ 2)) / 4 := by
  unfold isotropicUpperBandTransportAngularWeight
  rw [upperBandFermiSurfaceScalarOverlapWeight_eq_affineCosine,
    isotropicTransportAngularMean_affineCosine]
  ring

end

end QuantumTheory.Models.MassiveDirac
