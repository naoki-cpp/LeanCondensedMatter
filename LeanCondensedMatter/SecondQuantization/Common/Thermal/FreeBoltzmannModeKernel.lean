import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Matrix.Diagonal

set_option linter.style.header false

/-!
# Statistics-independent free Boltzmann mode kernel

For a finite or infinite mode type with one-particle energies `ε`, the free one-particle Boltzmann
weights define a diagonal complex matrix kernel

`Kᵢⱼ = δᵢⱼ exp(-β εᵢ)`.

The kernel itself is independent of Bose/Fermi statistics. Statistics enter only in downstream
exchange-cycle and physical partition-function consumers.
-/

namespace SecondQuantization
namespace Common

variable {Mode : Type*}

/-- The diagonal one-particle Boltzmann kernel, shared by free fermion and free boson consumers. -/
noncomputable def freeBoltzmannModeKernel (ε : Mode → ℝ) (β : ℝ) : Matrix Mode Mode ℂ := by
  classical
  exact Matrix.diagonal fun i => Complex.exp (-(β : ℂ) * (ε i : ℂ))

/-- The shared free Boltzmann mode kernel is the diagonal matrix of mode Boltzmann weights. -/
theorem freeBoltzmannModeKernel_eq_diagonal [DecidableEq Mode]
    (ε : Mode → ℝ) (β : ℝ) :
    freeBoltzmannModeKernel ε β =
      Matrix.diagonal (fun i => Complex.exp (-(β : ℂ) * (ε i : ℂ))) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [freeBoltzmannModeKernel]
  · simp [freeBoltzmannModeKernel, hij]

end Common
end SecondQuantization
