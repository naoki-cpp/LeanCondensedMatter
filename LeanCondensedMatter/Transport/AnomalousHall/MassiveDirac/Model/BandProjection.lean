import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.Spectral
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Band projection of diagonal Pauli channels

The continuum Born self-energy of the isotropic massive-Dirac model contains only the identity and
`σ_z` Pauli channels.  This file owns the clean spectral statement needed to project such a diagonal
Pauli operator onto a band without choosing an eigenvector gauge.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

/-- Gauge-independent band expectation of a diagonal Pauli operator `a I + b σ_z`. -/
def bandDiagonalPauliExpectation
    (band : Band) (v m px py : ℝ) (scalarCoeff zCoeff : ℂ) : ℂ :=
  Matrix.trace
    (bandProjector band v m px py *
      (scalarCoeff • (1 : Matrix2) + zCoeff • sigmaZ))

/-- Away from the Dirac degeneracy, the band expectation of `a I + b σ_z` is
`a + s (m/E) b`. -/
theorem bandDiagonalPauliExpectation_eq
    (band : Band) (v m px py : ℝ) (scalarCoeff zCoeff : ℂ)
    (hE : energy v m px py ≠ 0) :
    bandDiagonalPauliExpectation band v m px py scalarCoeff zCoeff =
      scalarCoeff +
        (((bandSign band * m / energy v m px py : ℝ) : ℂ)) * zCoeff := by
  have hEc : (((energy v m px py : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hE
  cases band <;>
    simp [bandDiagonalPauliExpectation, bandProjector, Matrix.trace, Matrix.mul_apply,
      hamiltonian, sigmaX, sigmaY, sigmaZ] <;>
    field_simp [hEc] <;>
    ring

end

end AnomalousHall.MassiveDirac
