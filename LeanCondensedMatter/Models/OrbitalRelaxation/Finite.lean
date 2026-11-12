import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

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

/-- Cartesian orbital-generator components as real skew matrices. The corresponding
Hermitian angular-momentum observables are `i • orbitalGenerator axis`.
Only the three axes of the supplied crystal model are indexed here. -/
def orbitalGenerator (axis : Fin 3) : OrbitalMatrix :=
  ![
    !![0, 0, 0; 0, 0, -1; 0, 1, 0],
    !![0, 0, 1; 0, 0, 0; -1, 0, 0],
    !![0, -1, 0; 1, 0, 0; 0, 0, 0]
  ] axis

/-- Each real Cartesian orbital generator is skew-symmetric. -/
theorem orbitalGenerator_transpose (axis : Fin 3) :
    (orbitalGenerator axis).transpose = -orbitalGenerator axis := by
  fin_cases axis <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [orbitalGenerator, Matrix.transpose_apply]

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
 
/-- Quartic double-commutator coefficient for the selected Cartesian
orbital polarization. The two transverse indices are taken cyclically;
the coefficients retain the crystal anisotropy of `orbitalHamiltonian`. -/
def orbitalPolynomial (axis : Fin 3) (c₁ c₂ : ℝ) (k : Fin 3 → ℝ) : ℝ :=
  let a := k (axis + 1)
  let b := k (axis + 2)
  let d := k axis
  c₁ ^ 2 * (a ^ 2 - b ^ 2) ^ 2 +
    c₂ ^ 2 * (4 * a ^ 2 * b ^ 2 + a ^ 2 * d ^ 2 + b ^ 2 * d ^ 2)

/-- Trace cyclicity converts the nested commutator into the square of
the simple commutator, without choosing matrix coordinates. -/
private theorem trace_double_commutator_eq_commutator_sq
    (H G : OrbitalMatrix) :
    -Matrix.trace ((H * (H * G - G * H) - (H * G - G * H) * H) * G) / 2 =
      Matrix.trace ((H * G - G * H) * (H * G - G * H)) / 2 := by
  let C : OrbitalMatrix := H * G - G * H
  have hcyclic : Matrix.trace (H * (C * G)) =
      Matrix.trace ((C * G) * H) :=
    Matrix.trace_mul_comm H (C * G)
  calc
    _ = -(Matrix.trace (H * (C * G)) - Matrix.trace (C * (H * G))) / 2 := by
      change -Matrix.trace ((H * C - C * H) * G) / 2 = _
      rw [sub_mul, Matrix.trace_sub]
      simp only [mul_assoc]
    _ = -(Matrix.trace (C * (G * H)) - Matrix.trace (C * (H * G))) / 2 := by
      rw [hcyclic]
      simp only [mul_assoc]
    _ = -Matrix.trace (C * (G * H - H * G)) / 2 := by
      simp only [mul_sub, Matrix.trace_sub]
    _ = Matrix.trace (C * C) / 2 := by
      have h : G * H - H * G = -C := by
        dsimp [C]
        abel
      simp [h]

/-- Exact matrix double-commutator coefficient for any Cartesian
polarization axis. The minus sign accounts for the physical generator
being `i G`, whereas `orbitalGenerator` is real and skew. -/
noncomputable def orbitalDoubleCommutator (axis : Fin 3) (c₁ c₂ : ℝ)
    (k : Fin 3 → ℝ) : ℝ :=
  let H := orbitalHamiltonian c₁ c₂ k
  let G := orbitalGenerator axis
  (-Matrix.trace ((H * (H * G - G * H) - (H * G - G * H) * H) * G)) / 2

theorem orbitalDoubleCommutator_eq_polynomial (axis : Fin 3) (c₁ c₂ : ℝ)
    (k : Fin 3 → ℝ) :
    orbitalDoubleCommutator axis c₁ c₂ k = orbitalPolynomial axis c₁ c₂ k := by
  unfold orbitalDoubleCommutator
  dsimp only
  rw [trace_double_commutator_eq_commutator_sq]
  fin_cases axis <;>
    simp [orbitalHamiltonian, orbitalGenerator, orbitalPolynomial,
      Matrix.trace, Fin.sum_univ_three] <;> ring

/-- Exact fourth-moment cubature for coordinate-even homogeneous quartics.
It reproduces the `kᵢ⁴` and `kᵢ²kⱼ²` moments of the normalized uniform
sphere measure, but is not asserted to integrate arbitrary functions on
the sphere. -/
noncomputable def evenQuarticCubature (r : ℝ) (f : (Fin 3 → ℝ) → ℝ) : ℝ :=
  (2 / 15 : ℝ) * (f ![r, 0, 0] + f ![0, r, 0] + f ![0, 0, r]) +
    (1 / 15 : ℝ) * f ![r, r, r]

theorem evenQuarticCubature_coordinate_four (i : Fin 3) (r : ℝ) :
    evenQuarticCubature r (fun k => k i ^ 4) = r ^ 4 / 5 := by
  fin_cases i <;> simp [evenQuarticCubature] <;> ring

theorem evenQuarticCubature_coordinate_sq_mul_coordinate_sq
    (i j : Fin 3) (hij : i ≠ j) (r : ℝ) :
    evenQuarticCubature r (fun k => k i ^ 2 * k j ^ 2) = r ^ 4 / 15 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [evenQuarticCubature] <;> ring

/-- The angular mean of the orbital double-commutator polynomial is the
same for every Cartesian polarization axis, despite the anisotropic
momentum dependence before averaging. -/
/-- Cyclic reindexing of the three momentum coordinates. -/
private def rotateMomentum (k : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![k 1, k 2, k 0]

/-- The model's orbital quartic polynomial transforms covariantly under the
cyclic permutation of Cartesian axes. -/
private theorem orbitalPolynomial_rotate (axis : Fin 3) (c₁ c₂ : ℝ)
    (k : Fin 3 → ℝ) :
    orbitalPolynomial (axis + 1) c₁ c₂ k =
      orbitalPolynomial axis c₁ c₂ (rotateMomentum k) := by
  fin_cases axis <;> simp [orbitalPolynomial, rotateMomentum]

/-- The finite fourth-moment cubature is invariant under cyclic reindexing
of the Cartesian momentum coordinates. -/
private theorem evenQuarticCubature_rotate (r : ℝ) (f : (Fin 3 → ℝ) → ℝ) :
    evenQuarticCubature r (fun k => f (rotateMomentum k)) =
      evenQuarticCubature r f := by
  simp [evenQuarticCubature, rotateMomentum]
  ring

/-- The angular mean agrees for all three Cartesian polarization axes by
cyclic symmetry: only the first axis requires a direct quartic computation. -/
theorem evenQuarticCubature_orbitalPolynomial (axis : Fin 3)
    (c₁ c₂ r : ℝ) :
    evenQuarticCubature r (orbitalPolynomial axis c₁ c₂) =
      (2 * r ^ 4 / 15) * (2 * c₁ ^ 2 + 3 * c₂ ^ 2) := by
  have hzero : evenQuarticCubature r (orbitalPolynomial 0 c₁ c₂) =
      (2 * r ^ 4 / 15) * (2 * c₁ ^ 2 + 3 * c₂ ^ 2) := by
    simp [evenQuarticCubature, orbitalPolynomial]
    ring
  have hstep (i : Fin 3) :
      evenQuarticCubature r (orbitalPolynomial (i + 1) c₁ c₂) =
        evenQuarticCubature r (orbitalPolynomial i c₁ c₂) := by
    have hpoly : orbitalPolynomial (i + 1) c₁ c₂ =
        (fun k => orbitalPolynomial i c₁ c₂ (rotateMomentum k)) := by
      funext k
      exact orbitalPolynomial_rotate i c₁ c₂ k
    rw [hpoly, evenQuarticCubature_rotate]
  fin_cases axis
  · exact hzero
  · simpa using (hstep 0).trans hzero
  · simpa using (hstep 1).trans ((hstep 0).trans hzero)

theorem evenQuarticCubature_orbitalDoubleCommutator (axis : Fin 3)
    (c₁ c₂ r : ℝ) :
    evenQuarticCubature r (orbitalDoubleCommutator axis c₁ c₂) =
      (2 * r ^ 4 / 15) * (2 * c₁ ^ 2 + 3 * c₂ ^ 2) := by
  calc
    _ = evenQuarticCubature r (orbitalPolynomial axis c₁ c₂) := by
          congr 1
          funext k
          exact orbitalDoubleCommutator_eq_polynomial axis c₁ c₂ k
    _ = _ := evenQuarticCubature_orbitalPolynomial axis c₁ c₂ r

/-- Conditional orbital relaxation rate for any Cartesian polarization
axis, given the degree-two scattering time and second-order kinetic
closure. Cubic symmetry gives a common rate for all three axes;
this does not claim full rotational invariance of the Hamiltonian. -/
noncomputable def orbitalRate (axis : Fin 3) (ℏ τ₂ c₁ c₂ r : ℝ) : ℝ :=
  τ₂ / ℏ ^ 2 * evenQuarticCubature r
    (orbitalDoubleCommutator axis c₁ c₂)

theorem orbitalRate_eq (axis : Fin 3) (ℏ τ₂ c₁ c₂ r : ℝ) :
    orbitalRate axis ℏ τ₂ c₁ c₂ r =
      (2 * r ^ 4 / (15 * ℏ ^ 2)) * (2 * c₁ ^ 2 + 3 * c₂ ^ 2) * τ₂ := by
  rw [orbitalRate, evenQuarticCubature_orbitalDoubleCommutator]
  ring

theorem orbitalRate_nonneg (axis : Fin 3) (ℏ τ₂ c₁ c₂ r : ℝ)
    (hτ₂ : 0 ≤ τ₂) :
    0 ≤ orbitalRate axis ℏ τ₂ c₁ c₂ r := by
  rw [orbitalRate_eq]
  positivity

/-- Momentum and degree-two scattering times are reciprocals of distinct
positive collision eigenvalues. -/
noncomputable def momentumTime (I₁ : ℝ) : ℝ := I₁⁻¹

/-- Relaxation time of the degree-two angular collision mode. -/
noncomputable def degreeTwoTime (I₂ : ℝ) : ℝ := momentumTime I₂

/-- Ratio of the momentum and degree-two scattering times. -/
noncomputable def scatteringRatio (I₁ I₂ : ℝ) : ℝ :=
  momentumTime I₁ / degreeTwoTime I₂

theorem scatteringRatio_eq (I₁ I₂ : ℝ) (hI₁ : I₁ ≠ 0)
    (hI₂ : I₂ ≠ 0) :
    scatteringRatio I₁ I₂ = I₂ / I₁ := by
  simp [scatteringRatio, momentumTime, degreeTwoTime]
  field_simp

end QuantumTheory.Models.OrbitalRelaxation
