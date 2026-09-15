import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Matrix.Diagonal

set_option linter.style.header false

/-!
# Statistics-independent free Boltzmann kernel

For a one-particle label type with energies `ε`, the free Boltzmann weights define the diagonal
complex matrix kernel

`Kᵢⱼ = δᵢⱼ exp(-β εᵢ)`.

This is a Gibbs-level one-particle object. It does not depend on occupation configurations, Fock
space, creation/annihilation operators, or particle statistics, so it lives upstream of second
quantization.
-/

namespace QuantumTheory

variable {Mode : Type*}

/-- The diagonal one-particle Boltzmann kernel. -/
noncomputable def freeBoltzmannModeKernel (ε : Mode → ℝ) (β : ℝ) : Matrix Mode Mode ℂ := by
  classical
  exact Matrix.diagonal fun i => Complex.exp (-(β : ℂ) * (ε i : ℂ))

/-- The free Boltzmann kernel is the diagonal matrix of one-particle Boltzmann weights. -/
theorem freeBoltzmannModeKernel_eq_diagonal [DecidableEq Mode]
    (ε : Mode → ℝ) (β : ℝ) :
    freeBoltzmannModeKernel ε β =
      Matrix.diagonal (fun i => Complex.exp (-(β : ℂ) * (ε i : ℂ))) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [freeBoltzmannModeKernel]
  · simp [freeBoltzmannModeKernel, hij]

end QuantumTheory
