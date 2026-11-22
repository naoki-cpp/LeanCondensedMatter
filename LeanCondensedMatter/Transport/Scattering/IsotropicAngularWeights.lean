import LeanCondensedMatter.Analysis.Fourier.AngularHarmonics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Isotropic angular scattering means

Normalized full-circle scattering means, with or without the transport factor
`1 - cos θ`. Affine-cosine identities require no Hamiltonian or impurity model.
-/

namespace QuantumTheory.Transport

noncomputable section

open AngularHarmonics MeasureTheory
open scoped Interval

/-- Normalized full-circle angular mean of an arbitrary scattering weight. -/
def isotropicSingleParticleAngularMean (weight : ℝ → ℝ) : ℝ :=
  (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), weight θ) / (2 * Real.pi)

/-- Full-circle current-relaxing mean with factor `1 - cos θ`. -/
def isotropicTransportAngularMean (weight : ℝ → ℝ) : ℝ :=
  (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      weight θ * (1 - Real.cos θ)) / (2 * Real.pi)

/-- The normalized mean of `a + b cos θ` is its constant harmonic. -/
theorem isotropicSingleParticleAngularMean_affineCosine (a b : ℝ) :
    isotropicSingleParticleAngularMean (fun θ => a + b * Real.cos θ) = a := by
  unfold isotropicSingleParticleAngularMean
  have hmean := integral_quadratic_cos_zero_two_pi a b 0
  simp only [zero_mul, add_zero] at hmean
  rw [hmean]
  field_simp [ne_of_gt Real.pi_pos]
  ring

/-- A first cosine harmonic subtracts `b/2` from the transport mean. -/
theorem isotropicTransportAngularMean_affineCosine (a b : ℝ) :
    isotropicTransportAngularMean (fun θ => a + b * Real.cos θ) =
      a - b / 2 := by
  unfold isotropicTransportAngularMean
  have hrewrite :
      (fun θ : ℝ => (a + b * Real.cos θ) * (1 - Real.cos θ)) =
        fun θ : ℝ =>
          a + (b - a) * Real.cos θ + (-b) * Real.cos θ ^ 2 := by
    funext θ
    ring
  rw [hrewrite, integral_quadratic_cos_zero_two_pi]
  field_simp [ne_of_gt Real.pi_pos]
  ring

end

end QuantumTheory.Transport
