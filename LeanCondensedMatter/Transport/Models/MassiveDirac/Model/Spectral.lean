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

/-- Pauli/Bloch form of the massive-Dirac band projector. This is the canonical spectral-layer
bridge from the model Hamiltonian to the shared internal-space Pauli algebra. -/
theorem bandProjector_eq_pauliCombination
    (band : Band) (v m px py : ℝ) :
    bandProjector band v m px py =
      (1 / 2 : ℂ) •
        ((1 : Matrix2) +
          InternalSpace.pauliCombination
            ((((bandSign band / energy v m px py : ℝ) : ℂ)) •
              diracPauliCoefficients v m px py)) := by
  simp [bandProjector, hamiltonian_eq_pauliCombination]

/-- The Hamiltonian normalized by the positive Dirac energy. Away from the degeneracy this is an
involution, and the two spectral projectors are its `±1` eigenspace projectors. -/
private noncomputable def normalizedHamiltonian (v m px py : ℝ) : Matrix2 :=
  (((energy v m px py : ℝ) : ℂ)⁻¹) • hamiltonian v m px py

/-- Away from the band degeneracy, the normalized Hamiltonian squares to the identity. -/
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

/-- The finite sum of massive-Dirac band projectors resolves the identity, including at the
algebraic `E = 0` value of the definition. -/
theorem sum_bandProjector_eq_one (v m px py : ℝ) :
    ∑ band : Band, bandProjector band v m px py = 1 := by
  simp only [sum_band]
  rw [bandProjector_eq_normalizedHamiltonian, bandProjector_eq_normalizedHamiltonian]
  simp only [bandSign_lower, bandSign_upper]
  push_cast
  module

/-- Either band projector and its opposite-band partner resolve the identity. -/
theorem bandProjector_add_oppositeBand (band : Band) (v m px py : ℝ) :
    bandProjector band v m px py + bandProjector (oppositeBand band) v m px py = 1 := by
  cases band
  · simpa only [sum_band, oppositeBand_lower] using sum_bandProjector_eq_one v m px py
  · simpa only [sum_band, oppositeBand_upper, add_comm] using sum_bandProjector_eq_one v m px py

/-- The two band signs square to one. -/
@[simp] theorem bandSign_sq (band : Band) : bandSign band ^ 2 = 1 := by
  cases band <;> simp

/-- Away from the band degeneracy, `H₀ P_s = E_s P_s`. -/
theorem hamiltonian_mul_bandProjector (band : Band) (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    hamiltonian v m px py * bandProjector band v m px py =
      ((bandEnergy band v m px py : ℝ) : ℂ) • bandProjector band v m px py := by
  let Q := normalizedHamiltonian v m px py
  let s : ℂ := ((bandSign band : ℝ) : ℂ)
  have hQ : Q * Q = 1 := by
    simpa [Q] using normalizedHamiltonian_mul_self v m px py hE
  have hs : s ^ 2 = 1 := by
    change (((bandSign band : ℝ) : ℂ) ^ 2) = 1
    exact_mod_cast (bandSign_sq band)
  have hH :
      hamiltonian v m px py = (((energy v m px py : ℝ) : ℂ)) • Q := by
    simpa [Q] using hamiltonian_eq_energy_smul_normalizedHamiltonian v m px py hE
  have hP :
      bandProjector band v m px py = (1 / 2 : ℂ) • ((1 : Matrix2) + s • Q) := by
    simpa [Q, s] using bandProjector_eq_normalizedHamiltonian band v m px py
  have hbandEnergy :
      (((bandEnergy band v m px py : ℝ) : ℂ)) =
        s * (((energy v m px py : ℝ) : ℂ)) := by
    simp [bandEnergy, s]
  have hmul : Q * ((1 : Matrix2) + s • Q) = s • ((1 : Matrix2) + s • Q) := by
    rw [mul_add, mul_one, mul_smul_comm, hQ]
    rw [smul_add, smul_smul]
    rw [show s * s = 1 by simpa [pow_two] using hs, one_smul]
    module
  rw [hH, hP, hbandEnergy]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, hmul, smul_smul]
  module

/-- Away from the band degeneracy, each `P_s` is idempotent. -/
theorem bandProjector_mul_self (band : Band) (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    bandProjector band v m px py * bandProjector band v m px py =
      bandProjector band v m px py := by
  let Q := normalizedHamiltonian v m px py
  let s : ℂ := ((bandSign band : ℝ) : ℂ)
  have hQ : Q * Q = 1 := by
    simpa [Q] using normalizedHamiltonian_mul_self v m px py hE
  have hs : s ^ 2 = 1 := by
    change (((bandSign band : ℝ) : ℂ) ^ 2) = 1
    exact_mod_cast (bandSign_sq band)
  have hP :
      bandProjector band v m px py = (1 / 2 : ℂ) • ((1 : Matrix2) + s • Q) := by
    simpa [Q, s] using bandProjector_eq_normalizedHamiltonian band v m px py
  have hsqmul : (s • Q) * (s • Q) = (s * s) • (Q * Q) := by
    calc
      (s • Q) * (s • Q) = s • (Q * (s • Q)) := by rw [smul_mul_assoc]
      _ = s • (s • (Q * Q)) := by rw [mul_smul_comm]
      _ = (s * s) • (Q * Q) := by rw [smul_smul]
  have hmul :
      ((1 : Matrix2) + s • Q) * ((1 : Matrix2) + s • Q) =
        (2 : ℂ) • ((1 : Matrix2) + s • Q) := by
    calc
      ((1 : Matrix2) + s • Q) * ((1 : Matrix2) + s • Q) =
          1 + s • Q + s • Q + (s • Q) * (s • Q) := by
        rw [add_mul, one_mul, mul_add, mul_one]
        abel
      _ = 1 + s • Q + s • Q + (s * s) • (Q * Q) := by rw [hsqmul]
      _ = 1 + s • Q + s • Q + 1 := by
        rw [hQ, show s * s = 1 by simpa [pow_two] using hs, one_smul]
      _ = (2 : ℂ) • ((1 : Matrix2) + s • Q) := by module
  rw [hP]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, hmul, smul_smul]
  module

/-- Away from the band degeneracy, opposite-band projectors are orthogonal in either order. -/
theorem bandProjector_mul_oppositeBand
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    bandProjector band v m px py * bandProjector (oppositeBand band) v m px py = 0 := by
  have hresolve := bandProjector_add_oppositeBand band v m px py
  have hidem := bandProjector_mul_self band v m px py hE
  calc
    bandProjector band v m px py * bandProjector (oppositeBand band) v m px py =
        bandProjector band v m px py *
            (bandProjector band v m px py + bandProjector (oppositeBand band) v m px py) -
          bandProjector band v m px py * bandProjector band v m px py := by noncomm_ring
    _ = bandProjector band v m px py * 1 - bandProjector band v m px py := by
      rw [hresolve, hidem]
    _ = 0 := by simp

end

end QuantumTheory.Transport.Models.MassiveDirac
