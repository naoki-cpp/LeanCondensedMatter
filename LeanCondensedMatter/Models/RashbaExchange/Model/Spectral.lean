import LeanCondensedMatter.Models.RashbaExchange.Model
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Spectral projectors for the Rashba-exchange model

The scalar parabolic term shifts both bands equally and therefore does not enter the band
projectors.  Writing

```text
H(p) = ε₀(p) I + d(p)·σ,
d(p) = (α p_y, -α p_x, Δ),
E(p) = |d(p)|,
```

the gauge-independent band projectors are

```text
P_s = 1/2 (I + s d·σ / E).
```

All projector identities that require separated bands are stated under `E ≠ 0`.
-/

namespace QuantumTheory.Models.RashbaExchange

noncomputable section

/-- The traceless spin-orbit/exchange part `d·σ` of the Hamiltonian. -/
def spinHamiltonian (params : Parameters) (px py : ℝ) : InternalSpace.PauliMatrix :=
  InternalSpace.pauliCombination (rashbaPauliCoefficients params px py)

/-- The model Hamiltonian is a scalar kinetic shift plus the traceless spin Hamiltonian. -/
theorem hamiltonian_eq_kinetic_add_spinHamiltonian
    (params : Parameters) (px py : ℝ) :
    hamiltonian params px py =
      (((kineticEnergy params px py : ℝ) : ℂ)) • (1 : InternalSpace.PauliMatrix) +
        spinHamiltonian params px py := by
  rfl

/-- The Pauli-vector quadratic invariant is exactly the squared spin-orbit energy. -/
theorem rashbaPauliCoefficients_dot_self
    (params : Parameters) (px py : ℝ) :
    dotProduct (rashbaPauliCoefficients params px py)
        (rashbaPauliCoefficients params px py) =
      ((spinOrbitEnergySq params px py : ℝ) : ℂ) := by
  rw [InternalSpace.dotProduct_pauliAxis]
  simp [rashbaPauliCoefficients, spinOrbitEnergySq, momentumSq2D]
  ring

/-- The squared spin-orbit energy is nonnegative. -/
theorem spinOrbitEnergySq_nonneg (params : Parameters) (px py : ℝ) :
    0 ≤ spinOrbitEnergySq params px py := by
  unfold spinOrbitEnergySq momentumSq2D
  positivity

/-- Squaring the positive spin-orbit energy recovers its defining polynomial. -/
theorem spinOrbitEnergy_sq (params : Parameters) (px py : ℝ) :
    spinOrbitEnergy params px py ^ 2 = spinOrbitEnergySq params px py := by
  exact Real.sq_sqrt (spinOrbitEnergySq_nonneg params px py)

/-- The traceless spin Hamiltonian squares to `E² I`. -/
theorem spinHamiltonian_mul_self (params : Parameters) (px py : ℝ) :
    spinHamiltonian params px py * spinHamiltonian params px py =
      ((spinOrbitEnergySq params px py : ℝ) : ℂ) •
        (1 : InternalSpace.PauliMatrix) := by
  unfold spinHamiltonian
  rw [InternalSpace.pauliCombination_mul_self,
    rashbaPauliCoefficients_dot_self]

/-- Gauge-independent projector onto one Rashba-exchange band. -/
def bandProjector (params : Parameters) (band : Band) (px py : ℝ) :
    InternalSpace.PauliMatrix :=
  (1 / 2 : ℂ) •
    ((1 : InternalSpace.PauliMatrix) +
      (((bandSign band / spinOrbitEnergy params px py : ℝ) : ℂ)) •
        spinHamiltonian params px py)

/-- Pauli/Bloch form of the band projector. -/
theorem bandProjector_eq_pauliCombination
    (params : Parameters) (band : Band) (px py : ℝ) :
    bandProjector params band px py =
      (1 / 2 : ℂ) •
        ((1 : InternalSpace.PauliMatrix) +
          InternalSpace.pauliCombination
            ((((bandSign band / spinOrbitEnergy params px py : ℝ) : ℂ)) •
              rashbaPauliCoefficients params px py)) := by
  simp [bandProjector, spinHamiltonian,
    InternalSpace.pauliCombination_smul]

/-- Every band projector has trace one. -/
@[simp] theorem trace_bandProjector
    (params : Parameters) (band : Band) (px py : ℝ) :
    Matrix.trace (bandProjector params band px py) = 1 := by
  rw [bandProjector_eq_pauliCombination, Matrix.trace_smul, Matrix.trace_add,
    InternalSpace.trace_pauliCombination]
  norm_num [Matrix.trace]

private noncomputable def normalizedSpinHamiltonian
    (params : Parameters) (px py : ℝ) : InternalSpace.PauliMatrix :=
  (((spinOrbitEnergy params px py : ℝ) : ℂ)⁻¹) •
    spinHamiltonian params px py

private theorem normalizedSpinHamiltonian_mul_self
    (params : Parameters) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    normalizedSpinHamiltonian params px py *
        normalizedSpinHamiltonian params px py = 1 := by
  have hEc : (((spinOrbitEnergy params px py : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hE
  have hEnergySq :
      (((spinOrbitEnergySq params px py : ℝ) : ℂ)) =
        (((spinOrbitEnergy params px py : ℝ) : ℂ) ^ 2) := by
    exact_mod_cast (spinOrbitEnergy_sq params px py).symm
  unfold normalizedSpinHamiltonian
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [spinHamiltonian_mul_self, hEnergySq, smul_smul]
  field_simp [hEc]
  simp

private theorem spinHamiltonian_eq_energy_smul_normalized
    (params : Parameters) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    spinHamiltonian params px py =
      (((spinOrbitEnergy params px py : ℝ) : ℂ)) •
        normalizedSpinHamiltonian params px py := by
  have hEc : (((spinOrbitEnergy params px py : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hE
  unfold normalizedSpinHamiltonian
  rw [smul_smul]
  simp [hEc]

private theorem bandProjector_eq_normalized
    (params : Parameters) (band : Band) (px py : ℝ) :
    bandProjector params band px py =
      (1 / 2 : ℂ) •
        ((1 : InternalSpace.PauliMatrix) +
          (((bandSign band : ℝ) : ℂ)) • normalizedSpinHamiltonian params px py) := by
  simp [bandProjector, normalizedSpinHamiltonian, div_eq_mul_inv, smul_smul]

/-- The two band projectors resolve the identity, including at the totalized `E = 0` value. -/
theorem sum_bandProjector_eq_one
    (params : Parameters) (px py : ℝ) :
    ∑ band : Band, bandProjector params band px py = 1 := by
  simp only [sum_band]
  rw [bandProjector_eq_normalized, bandProjector_eq_normalized]
  simp only [bandSign]
  push_cast
  module

/-- Either projector plus its opposite-band partner resolves the identity. -/
theorem bandProjector_add_oppositeBand
    (params : Parameters) (band : Band) (px py : ℝ) :
    bandProjector params band px py +
        bandProjector params (oppositeBand band) px py = 1 := by
  cases band
  · simpa only [sum_band, oppositeBand_lower] using
      sum_bandProjector_eq_one params px py
  · simpa only [sum_band, oppositeBand_upper, add_comm] using
      sum_bandProjector_eq_one params px py

/-- Away from the degeneracy, the two band energies are distinct. -/
theorem bandEnergy_injective
    (params : Parameters) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    Function.Injective (fun band : Band => bandEnergy params band px py) := by
  intro a b hab
  cases a <;> cases b
  · rfl
  · exfalso
    simp [bandEnergy, bandSign] at hab
    apply hE
    linarith
  · exfalso
    simp [bandEnergy, bandSign] at hab
    apply hE
    linarith
  · rfl

/-- Away from the degeneracy, the Hamiltonian acts on `P_s` with the corresponding shifted band
energy `ε₀+sE`. -/
theorem hamiltonian_mul_bandProjector
    (params : Parameters) (band : Band) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    hamiltonian params px py * bandProjector params band px py =
      (((bandEnergy params band px py : ℝ) : ℂ)) •
        bandProjector params band px py := by
  let Q := normalizedSpinHamiltonian params px py
  let s : ℂ := ((bandSign band : ℝ) : ℂ)
  let ε : ℂ := ((kineticEnergy params px py : ℝ) : ℂ)
  let E : ℂ := ((spinOrbitEnergy params px py : ℝ) : ℂ)
  have hQ : Q * Q = 1 := by
    simpa [Q] using normalizedSpinHamiltonian_mul_self params px py hE
  have hs : s ^ 2 = 1 := by
    change (((bandSign band : ℝ) : ℂ) ^ 2) = 1
    exact_mod_cast (bandSign_sq band)
  have hSpin : spinHamiltonian params px py = E • Q := by
    simpa [Q, E] using spinHamiltonian_eq_energy_smul_normalized params px py hE
  have hH :
      hamiltonian params px py = ε • (1 : InternalSpace.PauliMatrix) + E • Q := by
    rw [hamiltonian_eq_kinetic_add_spinHamiltonian, hSpin]
  have hP :
      bandProjector params band px py =
        (1 / 2 : ℂ) • ((1 : InternalSpace.PauliMatrix) + s • Q) := by
    simpa [Q, s] using bandProjector_eq_normalized params band px py
  have hEnergy :
      (((bandEnergy params band px py : ℝ) : ℂ)) = ε + s * E := by
    simp [bandEnergy, ε, s, E]
  have hQmul : Q * ((1 : InternalSpace.PauliMatrix) + s • Q) =
      s • ((1 : InternalSpace.PauliMatrix) + s • Q) := by
    rw [mul_add, mul_one, mul_smul_comm, hQ]
    rw [smul_add, smul_smul]
    rw [show s * s = 1 by simpa [pow_two] using hs, one_smul]
    module
  rw [hH, hP, hEnergy]
  rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc, mul_smul_comm]
  rw [hQmul]
  module

/-- Away from the degeneracy, each band projector is idempotent. -/
theorem bandProjector_mul_self
    (params : Parameters) (band : Band) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    bandProjector params band px py * bandProjector params band px py =
      bandProjector params band px py := by
  let Q := normalizedSpinHamiltonian params px py
  let s : ℂ := ((bandSign band : ℝ) : ℂ)
  have hQ : Q * Q = 1 := by
    simpa [Q] using normalizedSpinHamiltonian_mul_self params px py hE
  have hs : s ^ 2 = 1 := by
    change (((bandSign band : ℝ) : ℂ) ^ 2) = 1
    exact_mod_cast (bandSign_sq band)
  have hP :
      bandProjector params band px py =
        (1 / 2 : ℂ) • ((1 : InternalSpace.PauliMatrix) + s • Q) := by
    simpa [Q, s] using bandProjector_eq_normalized params band px py
  have hsqmul : (s • Q) * (s • Q) = (s * s) • (Q * Q) := by
    calc
      (s • Q) * (s • Q) = s • (Q * (s • Q)) := by rw [smul_mul_assoc]
      _ = s • (s • (Q * Q)) := by rw [mul_smul_comm]
      _ = (s * s) • (Q * Q) := by rw [smul_smul]
  rw [hP]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [add_mul, one_mul, mul_add, mul_one, hsqmul, hQ]
  rw [show s * s = 1 by simpa [pow_two] using hs, one_smul]
  module

/-- Away from the degeneracy, opposite-band projectors are orthogonal. -/
theorem bandProjector_mul_oppositeBand
    (params : Parameters) (band : Band) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    bandProjector params band px py *
        bandProjector params (oppositeBand band) px py = 0 := by
  have hresolve := bandProjector_add_oppositeBand params band px py
  have hidem := bandProjector_mul_self params band px py hE
  calc
    bandProjector params band px py *
        bandProjector params (oppositeBand band) px py =
      bandProjector params band px py *
          (bandProjector params band px py +
            bandProjector params (oppositeBand band) px py) -
        bandProjector params band px py * bandProjector params band px py := by
          noncomm_ring
    _ = bandProjector params band px py * 1 - bandProjector params band px py := by
      rw [hresolve, hidem]
    _ = 0 := by simp

end

end QuantumTheory.Models.RashbaExchange
