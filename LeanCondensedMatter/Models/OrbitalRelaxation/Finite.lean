import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

set_option linter.style.header false

/-!
# A finite orbital-relaxation benchmark

The real Cartesian `p_x,p_y,p_z` representation makes the orbital Hamiltonian
real symmetric. Its angular-momentum generators are `i` times real skew
matrices. This file computes the exact matrix double commutator and an explicit
fourth-moment cubature. The kinetic closure and the identification of the
cubature with continuous spherical integration are separate physical and
analytic steps.

Model provenance: J. Sohn, J. M. Lee, and H.-W. Lee, Phys. Rev. Lett. 132,
246301 (2024), Eq. (2) and supplemental Sec. I.A. We use the unordered-pair
convention for the off-diagonal anticommutator, which reproduces supplemental
Eqs. (15)-(16).
-/

namespace QuantumTheory.Models.OrbitalRelaxation

open scoped Matrix

/-- Real matrices in the Cartesian three-orbital basis. -/
abbrev OrbitalMatrix := Matrix (Fin 3) (Fin 3) ℝ

/-- Real skew generator whose complex physical orbital observable is `i G_z`. -/
def generatorZ : OrbitalMatrix :=
  !![0, -1, 0; 1, 0, 0; 0, 0, 0]

/-- Orbital-momentum part of the centrosymmetric spin-1 Hamiltonian.
The scalar kinetic term is omitted because it drops out of commutators.
The off-diagonal entries encode one anticommutator per unordered pair. -/
def orbitalHamiltonian (c₁ c₂ : ℝ) (k : Fin 3 → ℝ) : OrbitalMatrix :=
  !![c₁ * (k 1 ^ 2 + k 2 ^ 2), -c₂ * k 0 * k 1, -c₂ * k 0 * k 2;
     -c₂ * k 0 * k 1, c₁ * (k 0 ^ 2 + k 2 ^ 2), -c₂ * k 1 * k 2;
     -c₂ * k 0 * k 2, -c₂ * k 1 * k 2, c₁ * (k 0 ^ 2 + k 1 ^ 2)]

theorem orbitalHamiltonian_transpose (c₁ c₂ : ℝ) (k : Fin 3 → ℝ) :
    (orbitalHamiltonian c₁ c₂ k).transpose = orbitalHamiltonian c₁ c₂ k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orbitalHamiltonian, Matrix.transpose_apply]

theorem orbitalHamiltonian_neg (c₁ c₂ : ℝ) (k : Fin 3 → ℝ) :
    orbitalHamiltonian c₁ c₂ (-k) = orbitalHamiltonian c₁ c₂ k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orbitalHamiltonian, Pi.neg_apply]
 
/-- The polynomial multiplying the local `z` polarization in the
double-commutator evolution. -/
def orbitalZPolynomial (c₁ c₂ x y z : ℝ) : ℝ :=
  c₁ ^ 2 * (x ^ 2 - y ^ 2) ^ 2 +
    c₂ ^ 2 * (4 * x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2)

/-- The exact matrix double-commutator coefficient for the `z` generator.
The minus sign compensates for representing the physical Hermitian generator
as `i G_z`. -/
noncomputable def orbitalZDoubleCommutator (c₁ c₂ : ℝ) (k : Fin 3 → ℝ) : ℝ :=
  let H := orbitalHamiltonian c₁ c₂ k
  let G := generatorZ
  (-Matrix.trace ((H * (H * G - G * H) - (H * G - G * H) * H) * G)) / 2

theorem orbitalZDoubleCommutator_eq_polynomial (c₁ c₂ : ℝ)
    (k : Fin 3 → ℝ) :
    orbitalZDoubleCommutator c₁ c₂ k =
      orbitalZPolynomial c₁ c₂ (k 0) (k 1) (k 2) := by
  simp [orbitalZDoubleCommutator, orbitalHamiltonian, generatorZ,
    orbitalZPolynomial, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_three]
  ring

/-- An exact cubature for polynomials even in each coordinate and homogeneous
of degree four. It has the same `xᵢ⁴` and `xᵢ²xⱼ²` moments as the normalized
uniform sphere measure. It is not asserted here to equal sphere integration
for arbitrary functions. -/
noncomputable def evenQuarticCubature (r : ℝ) (f : (Fin 3 → ℝ) → ℝ) : ℝ :=
  (2 / 15 : ℝ) * (f ![r, 0, 0] + f ![0, r, 0] + f ![0, 0, r]) +
    (1 / 15 : ℝ) * f ![r, r, r]

theorem evenQuarticCubature_x_four (r : ℝ) :
    evenQuarticCubature r (fun k => k 0 ^ 4) = r ^ 4 / 5 := by
  simp [evenQuarticCubature]
  ring

theorem evenQuarticCubature_x_sq_y_sq (r : ℝ) :
    evenQuarticCubature r (fun k => k 0 ^ 2 * k 1 ^ 2) = r ^ 4 / 15 := by
  simp [evenQuarticCubature]
  ring

theorem evenQuarticCubature_orbitalZPolynomial
    (c₁ c₂ r : ℝ) :
    evenQuarticCubature r
        (fun k => orbitalZPolynomial c₁ c₂ (k 0) (k 1) (k 2)) =
      (2 * r ^ 4 / 15) * (2 * c₁ ^ 2 + 3 * c₂ ^ 2) := by
  simp [evenQuarticCubature, orbitalZPolynomial]
  ring

theorem evenQuarticCubature_orbitalZDoubleCommutator
    (c₁ c₂ r : ℝ) :
    evenQuarticCubature r (orbitalZDoubleCommutator c₁ c₂) =
      (2 * r ^ 4 / 15) * (2 * c₁ ^ 2 + 3 * c₂ ^ 2) := by
  change evenQuarticCubature r
    (fun k => orbitalZPolynomial c₁ c₂ (k 0) (k 1) (k 2)) = _
  exact evenQuarticCubature_orbitalZPolynomial c₁ c₂ r

/-- Conditional orbital relaxation rate after supplying the degree-two
scattering time and the second-order kinetic closure. -/
noncomputable def orbitalRate (ℏ τ₂ c₁ c₂ r : ℝ) : ℝ :=
  τ₂ / ℏ ^ 2 * evenQuarticCubature r
    (orbitalZDoubleCommutator c₁ c₂)

theorem orbitalRate_eq (ℏ τ₂ c₁ c₂ r : ℝ) :
    orbitalRate ℏ τ₂ c₁ c₂ r =
      (2 * r ^ 4 / (15 * ℏ ^ 2)) * (2 * c₁ ^ 2 + 3 * c₂ ^ 2) * τ₂ := by
  rw [orbitalRate, evenQuarticCubature_orbitalZDoubleCommutator]
  ring

theorem orbitalRate_nonneg (ℏ τ₂ c₁ c₂ r : ℝ)
    (hτ₂ : 0 ≤ τ₂) :
    0 ≤ orbitalRate ℏ τ₂ c₁ c₂ r := by
  rw [orbitalRate_eq]
  positivity

/-- Momentum and degree-two scattering times are reciprocals of distinct
positive collision eigenvalues. -/
noncomputable def momentumTime (I₁ : ℝ) : ℝ := I₁⁻¹
noncomputable def degreeTwoTime (I₂ : ℝ) : ℝ := I₂⁻¹
noncomputable def scatteringRatio (I₁ I₂ : ℝ) : ℝ :=
  momentumTime I₁ / degreeTwoTime I₂

theorem scatteringRatio_eq (I₁ I₂ : ℝ) (hI₁ : I₁ ≠ 0)
    (hI₂ : I₂ ≠ 0) :
    scatteringRatio I₁ I₂ = I₂ / I₁ := by
  simp [scatteringRatio, momentumTime, degreeTwoTime]
  field_simp

end QuantumTheory.Models.OrbitalRelaxation
