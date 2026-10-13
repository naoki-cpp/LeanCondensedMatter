import LeanCondensedMatter.Models.OrbitalRelaxation.Finite

set_option linter.style.header false

/-!
# Spectral numerators of the spherical t2g Hamiltonian

For an assumed Cartesian spin-1 matrix representation, `(k · L)^2` is
represented by `|k|² I - k kᵀ`. We use real matrices and keep the spectral
numerators unnormalized, so every statement also holds at `k = 0`. At nonzero momentum,
division by `|k|²` gives the two complementary spectral projectors used in
Manchon et al., arXiv:2512.06355v1, Eq. (4). The paper's `r` band is the
rank-two transverse subspace in this Cartesian representation.

This file proves algebra inside the supplied three-by-three model. It does not
construct atomic `d` orbitals, project physical `l = 2` angular momentum onto
the `t₂g` subspace, or derive the momentum-dependent matrix from a crystal
Hamiltonian. Those identifications are separate prerequisites for a physical
orbital-to-band interpretation.
-/

namespace QuantumTheory.Models.OrbitalRelaxation

open scoped Matrix

/-- Squared momentum in the three-dimensional Cartesian basis. -/
def momentumNormSq (k : Fin 3 → ℝ) : ℝ :=
  k 0 ^ 2 + k 1 ^ 2 + k 2 ^ 2

/-- Outer product of the Cartesian momentum vector with itself. -/
def momentumOuter (k : Fin 3 → ℝ) : OrbitalMatrix :=
  !![k 0 * k 0, k 0 * k 1, k 0 * k 2;
     k 1 * k 0, k 1 * k 1, k 1 * k 2;
     k 2 * k 0, k 2 * k 1, k 2 * k 2]

/-- The unnormalized projector numerator onto the transverse orbital band. -/
def transverseNumerator (k : Fin 3 → ℝ) : OrbitalMatrix :=
  !![k 1 ^ 2 + k 2 ^ 2, -k 0 * k 1, -k 0 * k 2;
     -k 1 * k 0, k 0 ^ 2 + k 2 ^ 2, -k 1 * k 2;
     -k 2 * k 0, -k 2 * k 1, k 0 ^ 2 + k 1 ^ 2]

theorem transverseNumerator_eq_orbitalHamiltonian (k : Fin 3 → ℝ) :
    transverseNumerator k = orbitalHamiltonian 1 1 k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transverseNumerator, orbitalHamiltonian] <;> ring

theorem momentumOuter_add_transverseNumerator (k : Fin 3 → ℝ) :
    momentumOuter k + transverseNumerator k = momentumNormSq k • (1 : OrbitalMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [momentumOuter, transverseNumerator, momentumNormSq, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul] <;> ring

theorem momentumOuter_mul_self (k : Fin 3 → ℝ) :
    momentumOuter k * momentumOuter k = momentumNormSq k • momentumOuter k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [momentumOuter, momentumNormSq, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.smul_apply, smul_eq_mul] <;> ring

theorem transverseNumerator_mul_self (k : Fin 3 → ℝ) :
    transverseNumerator k * transverseNumerator k =
      momentumNormSq k • transverseNumerator k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transverseNumerator, momentumNormSq, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.smul_apply, smul_eq_mul] <;> ring

theorem momentumOuter_mul_transverseNumerator (k : Fin 3 → ℝ) :
    momentumOuter k * transverseNumerator k = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [momentumOuter, transverseNumerator, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem transverseNumerator_mul_momentumOuter (k : Fin 3 → ℝ) :
    transverseNumerator k * momentumOuter k = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [momentumOuter, transverseNumerator, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- Assumed spherical `t₂g` matrix Hamiltonian, with `t` the kinetic coefficient
and `r` the crystal-field splitting in the source model. This definition does
not derive either coefficient or the model from orbital-indexed hopping. -/
def t2gHamiltonian (t r : ℝ) (k : Fin 3 → ℝ) : OrbitalMatrix :=
  (t * momentumNormSq k) • (1 : OrbitalMatrix) + r • transverseNumerator k

theorem t2gHamiltonian_spectral_decomposition (t r : ℝ) (k : Fin 3 → ℝ) :
    momentumNormSq k • t2gHamiltonian t r k =
      (t * momentumNormSq k) • momentumOuter k +
      ((t + r) * momentumNormSq k) • transverseNumerator k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [t2gHamiltonian, momentumNormSq, momentumOuter, transverseNumerator,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] <;> ring_nf

end QuantumTheory.Models.OrbitalRelaxation
