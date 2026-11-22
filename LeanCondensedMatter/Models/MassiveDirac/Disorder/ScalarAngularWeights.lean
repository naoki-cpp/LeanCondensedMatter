import LeanCondensedMatter.Transport.Scattering.IsotropicAngularWeights
import LeanCondensedMatter.Models.MassiveDirac.Model.FermiSurfaceOverlap
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Scalar-disorder Fermi-circle angular weights

The massive-Dirac upper-band projector overlap specializes the model-independent
full-circle scattering means in `Transport.Scattering.IsotropicAngularWeights`.
The resulting dimensionless angular factors depend on the clean Fermi-circle
overlap, not the Born disorder strength or scattering-rate normalization.

The microscopic Born rate prefactor and resulting lifetimes are downstream
in `Disorder.TransportRate`.
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

/-- Full-circle mean of the upper-band scalar-disorder overlap; the angular factor in the
single-particle Born rate. -/
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

/-- Full-circle transport angular weight. The factor `1 - cos θ` suppresses
forward scattering because it does not relax the current direction. -/
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
