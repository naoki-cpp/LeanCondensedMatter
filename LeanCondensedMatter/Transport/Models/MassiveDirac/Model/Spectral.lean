import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Basic

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

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

/-- Gauge-independent spectral projector candidate
`P_s = 1/2 (I + s H₀/E)` for the massive-Dirac band with sign `s`. -/
def bandProjector (band : Band) (v m px py : ℝ) : Matrix2 :=
  (1 / 2 : ℂ) •
    ((1 : Matrix2) +
      (((bandSign band / energy v m px py : ℝ) : ℂ)) • hamiltonian v m px py)

/-- The Hamiltonian normalized by the positive Dirac energy. Away from the degeneracy this is an
involution, and the two spectral projectors are its `±1` eigenspace projectors. -/
private noncomputable def normalizedHamiltonian (v m px py : ℝ) : Matrix2 :=
  (((energy v m px py : ℝ) : ℂ)⁻¹) • hamiltonian v m px py

/-- Away from the Dirac degeneracy, the normalized Hamiltonian squares to the identity. -/
private theorem normalizedHamiltonian_mul_self
    (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    normalizedHamiltonian v m px py * normalizedHamiltonian v m px py = 1 := by
  have hEc : (((energy v m px py : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hE
  have hEnergySq :
      (((energySq v m px py : ℝ) : ℂ)) =
        (((energy v m px py : ℝ) : ℂ) ^ 2) := by
    exact_mod_cast (energy_sq v m px py).symm
  unfold normalizedHamiltonian
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hamiltonian_mul_self, hEnergySq, smul_smul]
  have hcoefficient :
      ((((energy v m px py : ℝ) : ℂ)⁻¹ *
          ((energy v m px py : ℝ) : ℂ)⁻¹) *
          ((energy v m px py : ℝ) : ℂ) ^ 2) = 1 := by
    field_simp [hEc]
  rw [hcoefficient, one_smul]

/-- Away from the degeneracy, multiplying the normalized Hamiltonian by the positive energy
recovers the original Hamiltonian. -/
private theorem hamiltonian_eq_energy_smul_normalizedHamiltonian
    (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    hamiltonian v m px py =
      (((energy v m px py : ℝ) : ℂ)) • normalizedHamiltonian v m px py := by
  have hEc : (((energy v m px py : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hE
  unfold normalizedHamiltonian
  rw [smul_smul]
  simp [hEc]

/-- Rewrite the band projector as the `±1` spectral projector of the normalized Hamiltonian. -/
private theorem bandProjector_eq_normalizedHamiltonian
    (band : Band) (v m px py : ℝ) :
    bandProjector band v m px py =
      (1 / 2 : ℂ) •
        ((1 : Matrix2) +
          (((bandSign band : ℝ) : ℂ)) • normalizedHamiltonian v m px py) := by
  simp [bandProjector, normalizedHamiltonian, div_eq_mul_inv, smul_smul]

/-- The lower- and upper-band projectors resolve the identity, including at the algebraic
`E = 0` value of the definition. -/
theorem bandProjector_lower_add_upper (v m px py : ℝ) :
    bandProjector .lower v m px py + bandProjector .upper v m px py = 1 := by
  rw [bandProjector_eq_normalizedHamiltonian, bandProjector_eq_normalizedHamiltonian]
  simp only [bandSign_lower, bandSign_upper]
  push_cast
  module

/-- The two band signs square to one. -/
@[simp] theorem bandSign_sq (band : Band) : bandSign band ^ 2 = 1 := by
  cases band <;> simp

/-- Away from the band degeneracy, `H₀ P_s = E_s P_s`. -/
theorem hamiltonian_mul_bandProjector (band : Band) (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    hamiltonian v m px py * bandProjector band v m px py =
      ((bandEnergy band v m px py : ℝ) : ℂ) • bandProjector band v m px py := by
  let Q := normalizedHamiltonian v m px py
  have hQ : Q * Q = 1 := by
    simpa [Q] using normalizedHamiltonian_mul_self v m px py hE
  have hH :
      hamiltonian v m px py = (((energy v m px py : ℝ) : ℂ)) • Q := by
    simpa [Q] using hamiltonian_eq_energy_smul_normalizedHamiltonian v m px py hE
  have hP (b : Band) :
      bandProjector b v m px py =
        (1 / 2 : ℂ) • ((1 : Matrix2) + (((bandSign b : ℝ) : ℂ)) • Q) := by
    simpa [Q] using bandProjector_eq_normalizedHamiltonian b v m px py
  rw [hH, hP]
  cases band
  · simp only [bandSign_lower, bandEnergy_lower]
    push_cast
    simp only [neg_smul, one_smul]
    have hmul : Q * (1 + -Q) = -(1 + -Q) := by
      calc
        Q * (1 + -Q) = Q - Q * Q := by noncomm_ring
        _ = Q - 1 := by rw [hQ]
        _ = -(1 + -Q) := by abel
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, hmul]
    module
  · simp only [bandSign_upper, bandEnergy_upper]
    push_cast
    simp only [one_smul]
    have hmul : Q * (1 + Q) = 1 + Q := by
      calc
        Q * (1 + Q) = Q + Q * Q := by noncomm_ring
        _ = Q + 1 := by rw [hQ]
        _ = 1 + Q := by abel
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, hmul]
    module

/-- Away from the band degeneracy, each `P_s` is idempotent. -/
theorem bandProjector_mul_self (band : Band) (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    bandProjector band v m px py * bandProjector band v m px py =
      bandProjector band v m px py := by
  let Q := normalizedHamiltonian v m px py
  have hQ : Q * Q = 1 := by
    simpa [Q] using normalizedHamiltonian_mul_self v m px py hE
  have hP (b : Band) :
      bandProjector b v m px py =
        (1 / 2 : ℂ) • ((1 : Matrix2) + (((bandSign b : ℝ) : ℂ)) • Q) := by
    simpa [Q] using bandProjector_eq_normalizedHamiltonian b v m px py
  rw [hP]
  cases band
  · simp only [bandSign_lower]
    push_cast
    simp only [neg_smul, one_smul]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    have hmul : (1 + -Q) * (1 + -Q) = (2 : ℂ) • (1 + -Q) := by
      calc
        (1 + -Q) * (1 + -Q) = 1 - Q - Q + Q * Q := by noncomm_ring
        _ = 1 - Q - Q + 1 := by rw [hQ]
        _ = (2 : ℂ) • (1 + -Q) := by module
    rw [hmul, smul_smul]
    module
  · simp only [bandSign_upper]
    push_cast
    simp only [one_smul]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    have hmul : (1 + Q) * (1 + Q) = (2 : ℂ) • (1 + Q) := by
      calc
        (1 + Q) * (1 + Q) = 1 + Q + Q + Q * Q := by noncomm_ring
        _ = 1 + Q + Q + 1 := by rw [hQ]
        _ = (2 : ℂ) • (1 + Q) := by module
    rw [hmul, smul_smul]
    module

/-- Away from the band degeneracy, the lower and upper projectors are orthogonal. -/
theorem bandProjector_lower_mul_upper (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    bandProjector .lower v m px py * bandProjector .upper v m px py = 0 := by
  let Q := normalizedHamiltonian v m px py
  have hQ : Q * Q = 1 := by
    simpa [Q] using normalizedHamiltonian_mul_self v m px py hE
  have hP (b : Band) :
      bandProjector b v m px py =
        (1 / 2 : ℂ) • ((1 : Matrix2) + (((bandSign b : ℝ) : ℂ)) • Q) := by
    simpa [Q] using bandProjector_eq_normalizedHamiltonian b v m px py
  rw [hP, hP]
  simp only [bandSign_lower, bandSign_upper]
  push_cast
  simp only [neg_smul, one_smul]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have hmul : (1 + -Q) * (1 + Q) = 0 := by
    calc
      (1 + -Q) * (1 + Q) = 1 - Q * Q := by noncomm_ring
      _ = 0 := by rw [hQ]; simp
  rw [hmul, smul_zero]

/-- Away from the band degeneracy, the upper and lower projectors are orthogonal in the opposite
order as well. -/
theorem bandProjector_upper_mul_lower (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    bandProjector .upper v m px py * bandProjector .lower v m px py = 0 := by
  let Q := normalizedHamiltonian v m px py
  have hQ : Q * Q = 1 := by
    simpa [Q] using normalizedHamiltonian_mul_self v m px py hE
  have hP (b : Band) :
      bandProjector b v m px py =
        (1 / 2 : ℂ) • ((1 : Matrix2) + (((bandSign b : ℝ) : ℂ)) • Q) := by
    simpa [Q] using bandProjector_eq_normalizedHamiltonian b v m px py
  rw [hP, hP]
  simp only [bandSign_lower, bandSign_upper]
  push_cast
  simp only [neg_smul, one_smul]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have hmul : (1 + Q) * (1 + -Q) = 0 := by
    calc
      (1 + Q) * (1 + -Q) = 1 - Q * Q := by noncomm_ring
      _ = 0 := by rw [hQ]; simp
  rw [hmul, smul_zero]

end

end QuantumTheory.Transport.Models.MassiveDirac
