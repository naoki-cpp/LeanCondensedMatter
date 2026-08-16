import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac

set_option linter.style.header false

/-!
# Spectral projectors for the two-dimensional massive Dirac model

This file supplies the gauge-independent band-projector layer missing between the concrete
massive-Dirac Hamiltonian and the generic Berry-geometry force-matrix API.

For band sign `s = ±1` and positive-energy magnitude `E`, the spectral projector candidate is

```text
P_s = 1/2 (I + s H₀ / E).
```

The algebraic spectral identities below are stated away from the degeneracy `E = 0`.  No explicit
eigenvector gauge is introduced.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

/-- Gauge-independent spectral projector candidate
`P_s = 1/2 (I + s H₀/E)` for the massive-Dirac band with sign `s`. -/
def bandProjector (band : Band) (v m px py : ℝ) : Matrix2 :=
  (1 / 2 : ℂ) •
    ((1 : Matrix2) +
      (((bandSign band / energy v m px py : ℝ) : ℂ)) • hamiltonian v m px py)

/-- The real dispersion identity, transported to the complex scalars used by the matrices. -/
private theorem energy_sq_complex (v m px py : ℝ) :
    (((energy v m px py : ℝ) : ℂ) ^ 2) =
      (((v : ℝ) : ℂ) ^ 2) *
          ((((px : ℝ) : ℂ) ^ 2) + (((py : ℝ) : ℂ) ^ 2)) +
        (((m : ℝ) : ℂ) ^ 2) := by
  norm_cast
  simpa [energySq] using energy_sq v m px py

/-- The lower- and upper-band projectors resolve the identity, including at the algebraic
`E = 0` value of the definition. -/
theorem bandProjector_lower_add_upper (v m px py : ℝ) :
    bandProjector .lower v m px py + bandProjector .upper v m px py = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bandProjector, hamiltonian, sigmaX, sigmaY, sigmaZ] <;> ring

/-- The two band signs square to one. -/
@[simp] theorem bandSign_sq (band : Band) : bandSign band ^ 2 = 1 := by
  cases band <;> simp

/-- Away from the band degeneracy, `H₀ P_s = E_s P_s`. -/
theorem hamiltonian_mul_bandProjector (band : Band) (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    hamiltonian v m px py * bandProjector band v m px py =
      ((bandEnergy band v m px py : ℝ) : ℂ) • bandProjector band v m px py := by
  have hEc : (((energy v m px py : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hE
  have hsq := energy_sq_complex v m px py
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  cases band <;>
    ext i j <;>
    fin_cases i <;> fin_cases j <;>
    simp [bandProjector, bandEnergy, Matrix.mul_apply, hamiltonian, sigmaX, sigmaY, sigmaZ] <;>
    field_simp [hEc] <;>
    ring_nf <;>
    simp only [hI] <;>
    ring_nf <;>
    linear_combination -2 * hsq

/-- Away from the band degeneracy, each `P_s` is idempotent. -/
theorem bandProjector_mul_self (band : Band) (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    bandProjector band v m px py * bandProjector band v m px py =
      bandProjector band v m px py := by
  have hEc : (((energy v m px py : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hE
  have hsq := energy_sq_complex v m px py
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  cases band <;>
    ext i j <;>
    fin_cases i <;> fin_cases j <;>
    simp [bandProjector, Matrix.mul_apply, hamiltonian, sigmaX, sigmaY, sigmaZ] <;>
    field_simp [hEc] <;>
    ring_nf <;>
    simp only [hI] <;>
    ring_nf <;>
    linear_combination -2 * hsq

/-- Away from the band degeneracy, the lower and upper projectors are orthogonal. -/
theorem bandProjector_lower_mul_upper (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    bandProjector .lower v m px py * bandProjector .upper v m px py = 0 := by
  have hEc : (((energy v m px py : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hE
  have hsq := energy_sq_complex v m px py
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bandProjector, Matrix.mul_apply, hamiltonian, sigmaX, sigmaY, sigmaZ] <;>
    field_simp [hEc] <;>
    ring_nf <;>
    simp only [hI] <;>
    ring_nf <;>
    linear_combination -2 * hsq

/-- Away from the band degeneracy, the upper and lower projectors are orthogonal in the opposite
order as well. -/
theorem bandProjector_upper_mul_lower (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    bandProjector .upper v m px py * bandProjector .lower v m px py = 0 := by
  have hEc : (((energy v m px py : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hE
  have hsq := energy_sq_complex v m px py
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bandProjector, Matrix.mul_apply, hamiltonian, sigmaX, sigmaY, sigmaZ] <;>
    field_simp [hEc] <;>
    ring_nf <;>
    simp only [hI] <;>
    ring_nf <;>
    linear_combination -2 * hsq

end

end AnomalousHall.MassiveDirac
