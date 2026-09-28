import Mathlib.Analysis.Complex.Exponential
import Mathlib.LinearAlgebra.Matrix.DotProduct

set_option linter.style.header false

/-!
# Finite-dimensional Fourier geometry

This module owns the dimension-independent Euclidean coordinate geometry used by continuum
transport Fourier transforms. Vectors are represented as indexed coordinate families `Fin n → ℝ`,
matching the existing transport model APIs.

The physical Fourier phase is defined as `exp(i p·r / ℏ)` in arbitrary finite dimension.
Radial scaling is also dimension-independent. Polar or spherical coordinate charts, angular
harmonics, Jacobians, and continuum-measure normalizations remain in downstream analysis modules.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

/-- Radial scaling of an arbitrary finite-dimensional direction. No unit-norm condition is bundled
here; a spherical-coordinate layer may supply one when it needs an actual point on a sphere. -/
def radialPoint {n : ℕ} (radius : ℝ) (direction : Fin n → ℝ) : Fin n → ℝ :=
  fun i => radius * direction i

/-- Negating a radial coordinate negates the corresponding Cartesian point. -/
theorem radialPoint_neg_radius {n : ℕ} (radius : ℝ) (direction : Fin n → ℝ) :
    radialPoint (-radius) direction = -radialPoint radius direction := by
  funext i
  simp [radialPoint]

/-- Physical finite-dimensional Fourier phase `exp(i p·r / ℏ)` in Cartesian coordinates. -/
def physicalMomentumFourierPhase {n : ℕ}
    (hbar : ℝ) (momentum position : Fin n → ℝ) : ℂ :=
  Complex.exp
    (Complex.I * ((((dotProduct momentum position) / hbar : ℝ) : ℂ)))

end

end Transport
end QuantumTheory
