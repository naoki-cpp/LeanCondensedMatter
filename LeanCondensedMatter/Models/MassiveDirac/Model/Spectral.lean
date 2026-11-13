import Mathlib.RingTheory.Idempotents
import LeanCondensedMatter.Models.MassiveDirac.Model.Basic

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

namespace QuantumTheory.Models.MassiveDirac

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

/-- Each massive-Dirac band projector has trace one. -/
@[simp] theorem trace_bandProjector (band : Band) (v m px py : ℝ) :
    Matrix.trace (bandProjector band v m px py) = 1 := by
  rw [bandProjector_eq_pauliCombination, Matrix.trace_smul, Matrix.trace_add,
    InternalSpace.trace_pauliCombination]
  norm_num [Matrix.trace]

/-- The finite sum of massive-Dirac band projectors resolves the identity, including at the
algebraic `E = 0` value of the definition. -/
theorem sum_bandProjector_eq_one (v m px py : ℝ) :
    ∑ band : Band, bandProjector band v m px py = 1 := by
  simp only [sum_band, bandProjector, bandSign_lower, bandSign_upper]
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

/-- Away from the band degeneracy, the two band energies are distinct. -/
theorem bandEnergy_injective (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    Function.Injective (fun band : Band => bandEnergy band v m px py) := by
  intro a b hab
  cases a <;> cases b <;> try rfl
  all_goals
    exact (hE (by
      simp only [bandEnergy_lower, bandEnergy_upper] at hab
      linarith)).elim

/-- Away from the band degeneracy, `H₀ P_s = E_s P_s`. -/
theorem hamiltonian_mul_bandProjector (band : Band) (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    hamiltonian v m px py * bandProjector band v m px py =
      ((bandEnergy band v m px py : ℝ) : ℂ) • bandProjector band v m px py := by
  have h := InternalSpace.quadratic_shift_mul_projector
    (hamiltonian v m px py) (((energy v m px py : ℝ) : ℂ))
    0 (((bandSign band : ℝ) : ℂ)) (by exact_mod_cast hE)
    (by simpa only [← energy_sq, Complex.ofReal_pow] using hamiltonian_mul_self v m px py)
    (by cases band <;> norm_num [bandSign])
  simpa [bandProjector, bandEnergy] using h

/-- Away from the Dirac degeneracy, the matrix band projectors are a complete
orthogonal family. Their completeness also holds at zero energy by
`sum_bandProjector_eq_one`. -/
theorem bandProjector_completeOrthogonalIdempotents
    (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    CompleteOrthogonalIdempotents
      (fun band : Band => bandProjector band v m px py) := by
  have hLower : IsIdempotentElem (bandProjector .lower v m px py) := by
    simpa [bandProjector, Complex.ofReal_div] using
      (InternalSpace.quadratic_projector_isIdempotent
        (hamiltonian v m px py) (((energy v m px py : ℝ) : ℂ))
        (((bandSign Band.lower : ℝ) : ℂ)) (by exact_mod_cast hE)
        (by simpa only [← energy_sq, Complex.ofReal_pow] using hamiltonian_mul_self v m px py)
        (by norm_num [bandSign]))
  have hUpper : bandProjector .upper v m px py =
      1 - bandProjector .lower v m px py :=
    eq_sub_of_add_eq' (by simpa only [sum_band] using sum_bandProjector_eq_one v m px py)
  refine CompleteOrthogonalIdempotents.iff_ortho_complete.mpr
    ⟨?_, sum_bandProjector_eq_one v m px py⟩
  intro i j hij
  cases i <;> cases j <;>
    simp_all [mul_sub, sub_mul, hLower.eq]

end

end QuantumTheory.Models.MassiveDirac
