import LeanCondensedMatter.Transport.Analysis.AngularHarmonics
import LeanCondensedMatter.Models.MassiveDirac.Model.FermiSurfaceOverlap
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Scalar-disorder Fermi-circle angular weights

This module evaluates the full-circle upper-band projector-overlap weight and its
current-relaxing counterpart with factor `1 - cos θ`. These dimensionless angular
averages depend on the clean massive-Dirac Fermi-circle overlap and the chosen
scalar-scattering transport weighting, not on the Born disorder strength or
scattering-rate normalization.

The microscopic Born rate prefactor and resulting lifetimes are downstream
in `Disorder.TransportRate`.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Full-circle mean of the upper-band scalar-disorder overlap. This is the angular factor carried
by the single-particle Born rate. -/
def isotropicUpperBandSingleParticleAngularWeight
    (v m fermiEnergy : ℝ) : ℝ :=
  (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      upperBandFermiSurfaceScalarOverlapWeight v m fermiEnergy θ) /
    (2 * Real.pi)

/-- The unweighted scalar-disorder overlap average is `(1 + m²/ε_F²)/2`. -/
theorem isotropicUpperBandSingleParticleAngularWeight_eq
    (v m fermiEnergy : ℝ) :
    isotropicUpperBandSingleParticleAngularWeight v m fermiEnergy =
      (1 + m ^ 2 / fermiEnergy ^ 2) / 2 := by
  rw [isotropicUpperBandSingleParticleAngularWeight]
  have hrewrite :
      (fun θ : ℝ => upperBandFermiSurfaceScalarOverlapWeight v m fermiEnergy θ) =
        fun θ : ℝ =>
          (1 + m ^ 2 / fermiEnergy ^ 2) / 2 +
            ((1 - m ^ 2 / fermiEnergy ^ 2) / 2) * Real.cos θ +
              0 * Real.cos θ ^ 2 := by
    funext θ
    unfold upperBandFermiSurfaceScalarOverlapWeight
    ring
  rw [hrewrite, integral_quadratic_cos_zero_two_pi]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi]
  ring

/-- Full-circle transport angular weight. The factor `1 - cos θ` suppresses forward scattering
because it does not relax the current direction. -/
def isotropicUpperBandTransportAngularWeight
    (v m fermiEnergy : ℝ) : ℝ :=
  (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      upperBandFermiSurfaceScalarOverlapWeight v m fermiEnergy θ *
        (1 - Real.cos θ)) /
    (2 * Real.pi)

/-- The scalar-disorder transport angular weight is `(1 + 3 m²/ε_F²)/4`. -/
theorem isotropicUpperBandTransportAngularWeight_eq
    (v m fermiEnergy : ℝ) :
    isotropicUpperBandTransportAngularWeight v m fermiEnergy =
      (1 + 3 * (m ^ 2 / fermiEnergy ^ 2)) / 4 := by
  rw [isotropicUpperBandTransportAngularWeight]
  have hrewrite :
      (fun θ : ℝ =>
        upperBandFermiSurfaceScalarOverlapWeight v m fermiEnergy θ *
          (1 - Real.cos θ)) =
        fun θ : ℝ =>
          (1 + m ^ 2 / fermiEnergy ^ 2) / 2 +
            (-(m ^ 2 / fermiEnergy ^ 2)) * Real.cos θ +
              (-((1 - m ^ 2 / fermiEnergy ^ 2) / 2)) * Real.cos θ ^ 2 := by
    funext θ
    unfold upperBandFermiSurfaceScalarOverlapWeight
    ring
  rw [hrewrite, integral_quadratic_cos_zero_two_pi]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi]
  ring

end

end QuantumTheory.Models.MassiveDirac
