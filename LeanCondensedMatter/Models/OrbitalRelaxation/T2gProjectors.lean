import LeanCondensedMatter.Models.OrbitalRelaxation.Finite
import LeanCondensedMatter.Analysis.Matrix.CartesianProjectors
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Spherical t2g Hamiltonian as a Cartesian outer-product model

The longitudinal and transverse rank-one matrix numerators are imported from
`Analysis.Matrix.CartesianProjectors`, where they are proved in any finite
real dimension. Only the identification with the supplied Cartesian spin-1
orbital Hamiltonian and the model's spectral-parameter specialization live
here. The numerator identities hold even at zero momentum.

The `t₂g` realization is assumed, not derived from crystal orbitals.
-/

namespace QuantumTheory.Models.OrbitalRelaxation

open CartesianProjectors

/-- The transverse numerator coincides with the supplied spherical orbital matrix. -/
theorem transverse_eq_orbitalHamiltonian (k : Fin 3 → ℝ) :
    transverse k = orbitalHamiltonian 1 1 k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transverse, outer, normSq, dotProduct, Matrix.vecMulVec_apply,
      Fin.sum_univ_three, orbitalHamiltonian, pow_two] <;> ring

/-- Assumed spherical `t₂g` matrix Hamiltonian, with `t` the kinetic
coefficient and `r` the band-splitting parameter. -/
def t2gHamiltonian (t r : ℝ) (k : Fin 3 → ℝ) : OrbitalMatrix :=
  (t * normSq k) • (1 : OrbitalMatrix) + r • transverse k

theorem t2gHamiltonian_spectral_decomposition (t r : ℝ) (k : Fin 3 → ℝ) :
    normSq k • t2gHamiltonian t r k =
      (t * normSq k) • outer k +
      ((t + r) * normSq k) • transverse k := by
  have hsplit := CartesianProjectors.outer_add_transverse k
  ext i j
  have hsplit' := congrArg (fun M : OrbitalMatrix => M i j) hsplit
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hsplit'
  simp only [t2gHamiltonian, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  calc
    normSq k * (t * normSq k * (1 : OrbitalMatrix) i j + r * transverse k i j) =
        t * normSq k * (normSq k * (1 : OrbitalMatrix) i j) +
          (r * normSq k) * transverse k i j := by ring
    _ = t * normSq k * (outer k i j + transverse k i j) +
          (r * normSq k) * transverse k i j := by rw [← hsplit']
    _ = t * normSq k * outer k i j +
          ((t + r) * normSq k) * transverse k i j := by ring

end QuantumTheory.Models.OrbitalRelaxation
