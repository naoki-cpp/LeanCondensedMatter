import LeanCondensedMatter.Analysis.Algebra.QuadraticNormalization
import LeanCondensedMatter.QuantumTheory.TwoBand
import LeanCondensedMatter.Models.RashbaExchange.Model
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

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

The spin Hamiltonian, projectors and their spectral identities require only the clean
`HamiltonianParameters`; response and regularization parameters are not used here.
All projector identities that require separated bands are stated under `E ≠ 0`.
-/

namespace QuantumTheory.Models.RashbaExchange


open QuantumTheory.TwoBand
noncomputable section

/-- The traceless spin-orbit/exchange part `d·σ` of the Hamiltonian. -/
def spinHamiltonian (params : HamiltonianParameters) (px py : ℝ) : InternalSpace.PauliMatrix :=
  InternalSpace.pauliCombination (rashbaPauliCoefficients params px py)

/-- The model Hamiltonian is a scalar kinetic shift plus the traceless spin Hamiltonian. -/
theorem hamiltonian_eq_kinetic_add_spinHamiltonian
    (params : HamiltonianParameters) (px py : ℝ) :
    hamiltonian params px py =
      (((kineticEnergy params px py : ℝ) : ℂ)) • (1 : InternalSpace.PauliMatrix) +
        spinHamiltonian params px py := by
  rfl

/-- The Pauli-vector quadratic invariant is exactly the squared spin-orbit energy. -/
theorem rashbaPauliCoefficients_dot_self
    (params : HamiltonianParameters) (px py : ℝ) :
    dotProduct (rashbaPauliCoefficients params px py)
        (rashbaPauliCoefficients params px py) =
      ((spinOrbitEnergySq params px py : ℝ) : ℂ) := by
  rw [InternalSpace.dotProduct_pauliAxis]
  simp [rashbaPauliCoefficients, spinOrbitEnergySq]
  ring

/-- Squaring the positive spin-orbit energy recovers its defining polynomial. -/
theorem spinOrbitEnergy_sq (params : HamiltonianParameters) (px py : ℝ) :
    spinOrbitEnergy params px py ^ 2 = spinOrbitEnergySq params px py := by
  exact Real.sq_sqrt (by
    unfold spinOrbitEnergySq
    positivity)

/-- The traceless spin Hamiltonian squares to `E² I`. -/
theorem spinHamiltonian_mul_self (params : HamiltonianParameters) (px py : ℝ) :
    spinHamiltonian params px py * spinHamiltonian params px py =
      ((spinOrbitEnergySq params px py : ℝ) : ℂ) •
        (1 : InternalSpace.PauliMatrix) := by
  unfold spinHamiltonian
  rw [InternalSpace.pauliCombination_mul_self,
    rashbaPauliCoefficients_dot_self]

/-- Gauge-independent projector onto one Rashba-exchange band. -/
def bandProjector (params : HamiltonianParameters) (band : TwoBand) (px py : ℝ) :
    InternalSpace.PauliMatrix :=
  (1 / 2 : ℂ) •
    ((1 : InternalSpace.PauliMatrix) +
      (((bandSign band / spinOrbitEnergy params px py : ℝ) : ℂ)) •
        spinHamiltonian params px py)

/-- Pauli/Bloch form of the band projector. -/
theorem bandProjector_eq_pauliCombination
    (params : HamiltonianParameters) (band : TwoBand) (px py : ℝ) :
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
    (params : HamiltonianParameters) (band : TwoBand) (px py : ℝ) :
    Matrix.trace (bandProjector params band px py) = 1 := by
  rw [bandProjector_eq_pauliCombination]
  exact InternalSpace.trace_half_one_add_pauliCombination _

/-- The two band projectors resolve the identity, including at the totalized `E = 0` value. -/
theorem sum_bandProjector_eq_one
    (params : HamiltonianParameters) (px py : ℝ) :
    ∑ band : TwoBand, bandProjector params band px py = 1 := by
  simp only [sum_band, bandProjector, bandSign]
  push_cast
  module

/-- Either projector plus its opposite-band partner resolves the identity. -/
theorem bandProjector_add_oppositeBand
    (params : HamiltonianParameters) (band : TwoBand) (px py : ℝ) :
    bandProjector params band px py +
        bandProjector params (oppositeBand band) px py = 1 := by
  cases band <;> simpa only [sum_band, oppositeBand_lower, oppositeBand_upper, add_comm] using
    sum_bandProjector_eq_one params px py

/-- Away from the degeneracy, the two band energies are distinct. -/
theorem bandEnergy_injective
    (params : HamiltonianParameters) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    Function.Injective (fun band : TwoBand => bandEnergy params band px py) := by
  exact TwoBand.shiftedEnergy_injective
    (kineticEnergy params px py) (spinOrbitEnergy params px py) hE

/-- Away from the degeneracy, the Hamiltonian acts on `P_s` with the corresponding shifted band
energy `ε₀+sE`. -/
theorem hamiltonian_mul_bandProjector
    (params : HamiltonianParameters) (band : TwoBand) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    hamiltonian params px py * bandProjector params band px py =
      (((bandEnergy params band px py : ℝ) : ℂ)) •
        bandProjector params band px py := by
  have h := Algebra.quadratic_shift_mul_projector
    (spinHamiltonian params px py) (((spinOrbitEnergy params px py : ℝ) : ℂ))
    (((kineticEnergy params px py : ℝ) : ℂ)) (((bandSign band : ℝ) : ℂ))
    (by exact_mod_cast hE)
    (by simpa only [← spinOrbitEnergy_sq, Complex.ofReal_pow] using
      spinHamiltonian_mul_self params px py)
    (by cases band <;> norm_num [bandSign])
  simpa [hamiltonian_eq_kinetic_add_spinHamiltonian, bandProjector, bandEnergy] using h

/-- Away from the spin-orbit degeneracy, the matrix band projectors are
a complete orthogonal family. Completeness alone remains valid at zero energy. -/
theorem bandProjector_completeOrthogonalIdempotents
    (params : HamiltonianParameters) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    CompleteOrthogonalIdempotents
      (fun band : TwoBand => bandProjector params band px py) := by
  simpa only [bandProjector, Complex.ofReal_div] using
    (Algebra.quadratic_projectors_completeOrthogonalIdempotents
      (spinHamiltonian params px py) ((spinOrbitEnergy params px py : ℝ) : ℂ)
      (fun band : TwoBand => ((bandSign band : ℝ) : ℂ))
      (by exact_mod_cast hE)
      (by simpa only [← spinOrbitEnergy_sq, Complex.ofReal_pow] using
        spinHamiltonian_mul_self params px py)
      (by intro band; cases band <;> norm_num [bandSign])
      (by intro i j hij; cases i <;> cases j <;> simp_all [bandSign])
      (by simpa only [bandProjector, Complex.ofReal_div] using
        sum_bandProjector_eq_one params px py))


end

end QuantumTheory.Models.RashbaExchange
